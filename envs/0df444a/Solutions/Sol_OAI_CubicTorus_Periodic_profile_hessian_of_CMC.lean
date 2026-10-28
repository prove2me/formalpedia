-- Prove2me | solution 1 for OAI.CubicTorus.Periodic.profile_hessian_of_CMC
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:06:05.006016+00:00
-- url     : https://prove2.me/submissions/121c85b7-716e-40ad-9a5a-f6760baace2d

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_global_normal

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma admissible_neg {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (fun x => -F x) := by
  refine ⟨hF.1.neg, ?_, ?_⟩
  · intro n x
    change -F (x + latticeVector n) = -F x
    rw [hF.2.1 n x]
  · intro x
    simpa using hF.2.2 x

lemma divergence_neg (F : Cover → Cover) (x : Cover) :
    divergence (fun x => -F x) x = -divergence F x := by
  unfold divergence
  change ∑ i : Fin 3, (fderiv ℝ (-F) x (EuclideanSpace.single i 1)) i = _
  rw [fderiv_neg]
  simp

lemma perimeter_empty : perimeter ∅ = 0 := by
  simp [perimeter]

lemma finitePerimeter_empty : FinitePerimeter ∅ := by
  simp [FinitePerimeter, perimeter_empty]

lemma liftSet_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    (fundamentalCube ∩ quotientMap ⁻¹' E : Set Cover) =ᵐ[volume]
      (fundamentalCube ∩ quotientMap ⁻¹' F : Set Cover) := by
  have hh := ae_of_ae_map measurable_quotientMap.aemeasurable hEF
  have h := (ae_restrict_iff' measurableSet_fundamentalCube).1 hh
  filter_upwards [h] with x hx
  change (x ∈ fundamentalCube ∧ quotientMap x ∈ E) =
    (x ∈ fundamentalCube ∧ quotientMap x ∈ F)
  by_cases hc : x ∈ fundamentalCube
  · have hh : (quotientMap x ∈ E) = (quotientMap x ∈ F) := hx hc
    simpa only [hc, true_and] using hh
  · simp only [hc, false_and]

theorem perimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    perimeter E = perimeter F := by
  unfold perimeter
  apply iSup_congr
  intro X
  apply iSup_congr
  intro _
  rw [setIntegral_congr_set (liftSet_congr_ae hEF)]

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

lemma integrableOn_divergence {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    IntegrableOn (divergence F) fundamentalCube := by
  have hEmb := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toHomeomorph.measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrableOn_comp_preimage hEmb]
  rw [cube_preimage]
  have hc : Continuous (fun x : Fin 3 → ℝ => divergence F (WithLp.toLp 2 x)) :=
    (continuous_divergence hF).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  apply hc.integrableOn_Icc.mono_set
  intro x hx
  exact ⟨fun i => (hx i (mem_univ i)).1, fun i => le_of_lt (hx i (mem_univ i)).2⟩

lemma adjacent_faces {i : Fin 3} (x : Fin 2 → ℝ) :
    WithLp.toLp 2 (i.insertNth 1 x) =
      (WithLp.toLp 2 (i.insertNth 0 x) : Cover) + latticeVector (Pi.single i 1) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [latticeVector]
  · simp [latticeVector, Fin.succAbove_ne i k]

theorem integral_divergence_fundamentalCube {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube, divergence F x) = 0 := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let g : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x => F (e.symm x) i
  let dg : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i x => (EuclideanSpace.proj i).comp
      ((fderiv ℝ F (e.symm x)).comp e.symm.toContinuousLinearMap)
  have hdg : ∀ i x, HasFDerivAt (g i) (dg i x) x := by
    intro i x
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      (((hF.1.differentiable (by simp)) (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt)
  have hd : (fun x => ∑ i : Fin 3, dg i x (Pi.single i 1)) =
      fun x => divergence F (e.symm x) := by
    funext x
    simp [dg, divergence, e, PiLp.toLp_single]
  have hct : Continuous (fun x => divergence F (e.symm x)) :=
    (continuous_divergence hF.1).comp e.symm.continuous
  have hth := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) (1 : Fin 3 → ℝ) (by intro i; norm_num)
    g dg ∅ countable_empty
    (fun i => ((EuclideanSpace.proj i).continuous.comp
      (hF.1.continuous.comp e.symm.continuous)).continuousOn)
    (fun x _ i => hdg i x) (by rw [hd]; exact hct.integrableOn_Icc)
  rw [hd] at hth
  have hzero : (∑ i : Fin 3,
      ((∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
         g i (i.insertNth 1 x)) -
       ∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
         g i (i.insertNth 0 x))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have heq : (fun x : Fin 2 → ℝ => g i (i.insertNth 1 x)) =
        (fun x : Fin 2 → ℝ => g i (i.insertNth 0 x)) := by
      funext x
      change F (WithLp.toLp 2 (i.insertNth 1 x)) i = F (WithLp.toLp 2 (i.insertNth 0 x)) i
      rw [adjacent_faces, hF.2.1]
    rw [heq, sub_self]
  have hi : (∫ x in Icc (0 : Fin 3 → ℝ) 1, divergence F (e.symm x)) = 0 := hth.trans hzero
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding, cube_preimage]
  rw [volume_pi, setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc]
  exact hi

lemma quotientMap_measurePreserving :
    MeasurePreserving quotientMap (volume.restrict fundamentalCube) torusVolume :=
  ⟨measurable_quotientMap, rfl⟩

lemma integral_divergence_compl {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' Eᶜ, divergence F x) =
      -(∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  have hi := integral_add_compl₀ hm (integrableOn_divergence hF.1)
  rw [Measure.restrict_restrict₀ hm, Measure.restrict_restrict₀ hm.compl,
    integral_divergence_fundamentalCube hF] at hi
  simp only [inter_comm] at hi
  rw [preimage_compl]
  linarith

theorem perimeter_compl {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    perimeter Eᶜ = perimeter E := by
  have hle : ∀ E : Set Torus, NullMeasurableSet E torusVolume →
      perimeter Eᶜ ≤ perimeter E := by
    intro E hE
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply le_iSup_of_le (fun x => -F x)
    apply le_iSup_of_le (admissible_neg hF)
    rw [integral_divergence_compl hE hF]
    simp only [divergence_neg, integral_neg, le_refl]
  exact le_antisymm (hle E hE) (by simpa only [compl_compl] using hle Eᶜ hE.compl)

theorem finitePerimeter_compl {E : Set Torus} :
    FinitePerimeter Eᶜ ↔ FinitePerimeter E := by
  constructor
  · rintro ⟨hm, hp⟩
    have hm' : NullMeasurableSet E torusVolume := by simpa using hm.compl
    exact ⟨hm', by simpa only [perimeter_compl hm'] using hp⟩
  · rintro ⟨hm, hp⟩
    exact ⟨hm.compl, by rwa [perimeter_compl hm]⟩

lemma lift_indicator_integral {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    (g : Cover → ℝ) :
    (∫ x in fundamentalCube, (quotientMap ⁻¹' E).indicator g x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, g x := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  rw [integral_indicator₀ hm, Measure.restrict_restrict₀ hm, inter_comm]

lemma characteristic_mul (E : Set Torus) (g : Cover → ℝ) (x : Cover) :
    characteristic E (quotientMap x) * g x = (quotientMap ⁻¹' E).indicator g x := by
  classical
  by_cases hx : quotientMap x ∈ E <;> simp [characteristic, hx]

theorem tendsto_lift_integral {Es : ℕ → Set Torus} {E : Set Torus}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x)))
    {g : Cover → ℝ} (hg : IntegrableOn g fundamentalCube) :
    Filter.Tendsto
      (fun n => ∫ x in fundamentalCube ∩ quotientMap ⁻¹' Es n, g x)
      Filter.atTop (nhds (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, g x)) := by
  have hms (n : ℕ) := (hEs n).preimage quotientMap_measurePreserving.quasiMeasurePreserving
  have hlift := ae_of_ae_map measurable_quotientMap.aemeasurable hlim
  have hconv : ∀ᵐ x ∂volume.restrict fundamentalCube,
      Filter.Tendsto (fun n => (quotientMap ⁻¹' Es n).indicator g x)
        Filter.atTop (nhds ((quotientMap ⁻¹' E).indicator g x)) := by
    filter_upwards [hlift] with x hx
    simpa only [characteristic_mul] using hx.mul_const (g x)
  have hdom := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    (fun n => (hg.indicator₀ (hms n)).aestronglyMeasurable) hg.norm
    (fun n => Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self _ _)) hconv
  simpa only [lift_indicator_integral hE, lift_indicator_integral (hEs _)] using hdom

lemma integral_characteristic {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    (∫ x, characteristic E x ∂torusVolume) = (torusVolume E).toReal := by
  unfold characteristic
  rw [integral_indicator₀ hE, setIntegral_const]
  simp [Measure.real_def]

theorem tendsto_volume_of_ae_tendsto {Es : ℕ → Set Torus} {E : Set Torus}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x))) :
    Filter.Tendsto (fun n => torusVolume (Es n)) Filter.atTop (nhds (torusVolume E)) := by
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : Torus => (1 : ℝ))
    (fun n => ((integrable_const (1 : ℝ)).indicator₀ (hEs n)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n => Filter.Eventually.of_forall (fun x => by
      change ‖(Es n).indicator (fun _ => (1 : ℝ)) x‖ ≤ 1
      simpa only [norm_one] using norm_indicator_le_norm_self (s := Es n) (fun _ => (1 : ℝ)) x))
    hlim
  change Filter.Tendsto (fun n => ∫ x, characteristic (Es n) x ∂torusVolume)
    Filter.atTop (nhds (∫ x, characteristic E x ∂torusVolume)) at hconv
  simp only [integral_characteristic (hEs _), integral_characteristic hE] at hconv
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconv
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

lemma volume_compl_of_volume {E : Set Torus} {V : ℝ}
    (hE : NullMeasurableSet E torusVolume) (hV : 0 ≤ V)
    (hvolume : torusVolume E = ENNReal.ofReal V) :
    torusVolume Eᶜ = ENNReal.ofReal (1 - V) := by
  rw [measure_compl₀ hE (measure_ne_top _ _), torusVolume_univ, hvolume,
    ENNReal.ofReal_sub 1 hV, ENNReal.ofReal_one]

theorem isMinimizerAt_compl {V : ℝ} (hV : V ∈ Icc 0 1) {E : Set Torus} :
    IsMinimizerAt (1 - V) Eᶜ ↔ IsMinimizerAt V E := by
  have hforward : ∀ V : ℝ, V ∈ Icc 0 1 → ∀ E : Set Torus,
      IsMinimizerAt V E → IsMinimizerAt (1 - V) Eᶜ := by
    intro V hV E ⟨hE, hvolume, hmin⟩
    refine ⟨finitePerimeter_compl.mpr hE, volume_compl_of_volume hE.1 hV.1 hvolume, ?_⟩
    intro F hF hFvolume
    have hFcvolume : torusVolume Fᶜ = ENNReal.ofReal V := by
      have hh := volume_compl_of_volume hF.1 (sub_nonneg.mpr hV.2) hFvolume
      simpa only [sub_sub_cancel] using hh
    have hm := hmin Fᶜ (finitePerimeter_compl.mpr hF) hFcvolume
    rwa [perimeter_compl hE.1, perimeter_compl hF.1] at *
  constructor
  · intro h
    have hv : 1 - V ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hV.2, by linarith [hV.1]⟩
    simpa only [sub_sub_cancel, compl_compl] using hforward (1 - V) hv Eᶜ h
  · exact hforward V hV E

theorem perimeter_le_of_ae_tendsto_bound {Es : ℕ → Set Torus} {E : Set Torus}
    {Ls : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x)))
    (hbound : ∀ n, perimeter (Es n) ≤ Ls n)
    (hL : Filter.Tendsto Ls Filter.atTop (nhds L)) : perimeter E ≤ L := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_lift_integral hEs hE hlim (integrableOn_divergence hF.1))
  apply le_of_tendsto_of_tendsto ht hL
  apply Filter.Eventually.of_forall
  intro n
  exact (le_iSup₂ (f := fun F (_ : AdmissibleField F) =>
    ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' Es n, divergence F x)) F hF).trans (hbound n)

end CubicTorus

namespace CubicTorus

lemma circle_measurePreserving_mk_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico 0 1)) volume := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma torusVolume_eq_product :
    torusVolume = Measure.map (WithLp.toLp 2 : ProductTorus → Torus) volume := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have he := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage measurableSet_fundamentalCube
  rw [cube_preimage] at he
  have hp := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ => circle_measurePreserving_mk_Ico)
  have hs : (volume : Measure (Fin 3 → ℝ)).restrict
      (univ.pi (fun _ : Fin 3 => Ico 0 1)) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hto : Measurable (WithLp.toLp 2 : ProductTorus → Torus) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable
  unfold torusVolume
  rw [← he.map_eq, hs, Measure.map_map measurable_quotientMap (PiLp.volume_preserving_toLp (Fin 3)).measurable]
  rw [volume_pi, ← hp.map_eq, Measure.map_map hto hp.measurable]
  rfl

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

lemma quotientMap_neg (x : Cover) : quotientMap (-x) = -quotientMap x := by
  ext i
  simp [quotientMap]

end CubicTorus

namespace CubicTorus

lemma divergence_smul_const {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (a : Cover) :
    divergence (fun y => f y • a) point = fderiv ℝ f point a := by
  have ha : (∑ i : Fin 3, a i • EuclideanSpace.single i 1) = a := by
    ext j
    simp [Pi.single_apply]
  simp only [divergence, fderiv_smul_const hf, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, smul_eq_mul]
  conv_rhs => rw [← ha, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

lemma divergence_const_smul {F : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (c : ℝ) :
    divergence (fun y => c • F y) point = c * divergence F point := by
  change (∑ i : Fin 3, (fderiv ℝ (c • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_const_smul hF c]
  simp [divergence, Finset.mul_sum]

lemma abs_flux_le_perimeter {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤ (perimeter E).toReal := by
  apply abs_le.mpr
  constructor
  · have hh : ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        divergence (fun y => -F y) x) ≤ perimeter E :=
      le_iSup_of_le (fun y => -F y) (le_iSup_of_le (admissible_neg hF) le_rfl)
    simp_rw [divergence_neg, integral_neg] at hh
    have := (ENNReal.ofReal_le_iff_le_toReal hE).mp hh
    linarith
  · exact (ENNReal.ofReal_le_iff_le_toReal hE).mp
      (le_iSup_of_le F (le_iSup_of_le hF le_rfl))

lemma abs_flux_le_mul_perimeter {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤ k * (perimeter E).toReal := by
  have hG : AdmissibleField (fun x => k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      calc
        k⁻¹ * ‖F x‖ ≤ k⁻¹ * k := mul_le_mul_of_nonneg_left (hb x) (by positivity)
        _ = 1 := inv_mul_cancel₀ hk.ne'
  have hg := abs_flux_le_perimeter hE hG
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hk)] at hg
  calc
    _ = k * (k⁻¹ * |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x|) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hg hk.le

end CubicTorus

namespace CubicTorus

lemma abs_directional_flux_le {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hb : ∀ x, |f x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f x a|
      ≤ ‖a‖ * (perimeter E).toReal := by
  by_cases ha : a = 0
  · simp [ha]
  have hd := hf.differentiable (by simp)
  have hfield : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x • a) := hf.smul_const a
  have hfieldp : ∀ n x, f (x + latticeVector n) • a = f x • a := by
    intro n x
    rw [hp]
  have hfieldb : ∀ x, ‖f x • a‖ ≤ ‖a‖ := by
    intro x
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg a) (hb x)
  simpa only [divergence_smul_const hd.differentiableAt] using
    abs_flux_le_mul_perimeter hE hfield hfieldp (norm_pos_iff.mpr ha) hfieldb

end CubicTorus

namespace CubicTorus

theorem smooth_test_translation_bound {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hb : ∀ x, |f x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x)|
      ≤ ‖a‖ * (perimeter E).toReal := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x + s • a))
      (fderiv ℝ f (x + t • a) a) t := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using
      (hd (x + t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a)
      = f (x + a) - f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M, _, hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a)
      ((volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M * ‖a‖)
    exact Filter.Eventually.of_forall fun z =>
      ((fderiv ℝ f (z.1 + z.2 • a)).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) : |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      fderiv ℝ f (x + t • a) a| ≤ ‖a‖ * (perimeter E).toReal := by
    have hp' : ∀ n x, f ((x + latticeVector n) + t • a) = f (x + t • a) := by
      intro n x
      rw [add_right_comm, hp]
    simpa only [Function.comp_def, id_eq, fderiv_comp_add_right] using
      abs_directional_flux_le hE (hf.comp (contDiff_id.add contDiff_const)) hp'
        (fun x => hb (x + t • a)) a
  calc
    _ = ‖∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a‖ := by
      simp_rw [hFTC, Real.norm_eq_abs]
    _ = ‖∫ t in Ioc (0 : ℝ) 1,
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a‖ := by
      rw [integral_integral_swap hi]
    _ ≤ (‖a‖ * (perimeter E).toReal) * (volume.restrict (Ioc (0 : ℝ) 1)).real univ := by
      apply norm_integral_le_of_norm_le_const
      exact Filter.Eventually.of_forall fun t => (Real.norm_eq_abs _).trans_le (ht t)
    _ = _ := by simp [Measure.real]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma mollifier_rOut_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  simpa only [mollifier, mul_one, mul_div, mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma smoothApprox_periodic {g : Cover → ℝ}
    (hp : ∀ n x, g (x + latticeVector n) = g x) (k : ℕ) (n : Fin 3 → ℤ) (x : Cover) :
    smoothApprox g k (x + latticeVector n) = smoothApprox g k x := by
  simp only [smoothApprox, convolution_def, ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [show x + latticeVector n - y = (x - y) + latticeVector n by abel, hp]

lemma smoothApprox_ae_tendsto {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smoothApprox g n x) atTop (𝓝 (g x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    mollifier_rOut_tendsto (K := 2) _ (locallyIntegrable_of_bounded hg hb)
  exact Eventually.of_forall fun n => by dsimp [mollifier]; ring_nf; rfl

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

theorem measurable_test_translation_bound {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x)|
      ≤ ‖a‖ * (perimeter E).toReal := by
  have ht := smoothApprox_ae_tendsto hg hb
  have hta := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae ht
  have hlim : ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      Tendsto (fun n => smoothApprox g n (x + a) - smoothApprox g n x)
        atTop (𝓝 (g (x + a) - g x)) := by
    apply ae_restrict_of_ae
    filter_upwards [hta, ht] with x hx hx'
    exact hx.sub hx'
  have him : ∀ n, AEStronglyMeasurable
      (fun x => smoothApprox g n (x + a) - smoothApprox g n x)
        (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
    intro n
    exact (((smoothApprox_contDiff hg hb n).continuous.comp
      (continuous_id.add continuous_const)).sub
        (smoothApprox_contDiff hg hb n).continuous).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      ‖smoothApprox g n (x + a) - smoothApprox g n x‖ ≤ (2 : ℝ) := by
    intro n
    exact Eventually.of_forall fun x => by
      calc
        _ ≤ ‖smoothApprox g n (x + a)‖ + ‖smoothApprox g n x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (smoothApprox_bound hb n (x + a)) (smoothApprox_bound hb n x)
        _ = 2 := by norm_num
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
    him (integrable_const 2) hbd hlim
  apply le_of_tendsto hi.abs
  exact Eventually.of_forall fun n => smooth_test_translation_bound hE
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n) a

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicTorus

lemma setIntegral_lift_measurable {f : Torus → ℝ} (hf : Measurable f)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f z ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f (quotientMap x) := by
  change (∫ z in E, f z ∂Measure.map quotientMap (volume.restrict fundamentalCube)) = _
  rw [setIntegral_map hE hf.aestronglyMeasurable measurable_quotientMap.aemeasurable,
    Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

lemma torus_test_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) {g : Torus → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (a : Cover) :
    |∫ x in E, (g (x + quotientMap a) - g x) ∂torusVolume|
      ≤ ‖a‖ * (perimeter E).toReal := by
  rw [setIntegral_lift_measurable (f := fun x => g (x + quotientMap a) - g x)
    ((hg.comp (measurable_id.add_const _)).sub hg) hE]
  have hp : ∀ n x, g (quotientMap (x + latticeVector n)) = g (quotientMap x) := by
    intro n x
    rw [quotientMap_add, quotientMap_latticeVector, add_zero]
  simpa only [Function.comp_def, quotientMap_add] using
    measurable_test_translation_bound hP (hg.comp measurable_quotientMap) hp
      (fun x => hb (quotientMap x)) a

lemma integral_difference_test {E : Set Torus} (hE : MeasurableSet E)
    {g : Torus → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) (a : Torus) :
    (∫ x in E, (g (x + a) - g x) ∂torusVolume) =
      ∫ x, (characteristic E (x - a) - characteristic E x) * g x ∂torusVolume := by
  have hi₁ : Integrable (fun x => characteristic E x * g (x + a)) torusVolume := by
    apply Integrable.of_bound ((measurable_characteristic hE).mul
      (hg.comp (measurable_id.add_const a))).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Function.comp_def, id_eq]
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound E x)).trans (hb (x + a))
  have hi₂ : Integrable (fun x => characteristic E x * g x) torusVolume := by
    apply Integrable.of_bound ((measurable_characteristic hE).mul hg).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Function.comp_def, id_eq]
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound E x)).trans (hb x)
  have hi₃ : Integrable (fun x => characteristic E (x - a) * g x) torusVolume := by
    apply Integrable.of_bound (((measurable_characteristic hE).comp
      (measurable_id.sub_const a)).mul hg).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Function.comp_def, id_eq]
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound E (x - a))).trans (hb x)
  have hs := (measurePreserving_add_right torusVolume a).integral_comp
    (Homeomorph.addRight a).measurableEmbedding (fun x => characteristic E (x - a) * g x)
  simp only [add_sub_cancel_right] at hs
  calc
    _ = ∫ x, characteristic E x * (g (x + a) - g x) ∂torusVolume := by
      rw [← integral_indicator hE]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        classical
        by_cases hx : x ∈ E <;> simp [characteristic, hx]
    _ = (∫ x, characteristic E x * g (x + a) ∂torusVolume) -
        ∫ x, characteristic E x * g x ∂torusVolume := by
      simp_rw [mul_sub]
      exact integral_sub hi₁ hi₂
    _ = (∫ x, characteristic E (x - a) * g x ∂torusVolume) -
        ∫ x, characteristic E x * g x ∂torusVolume := by rw [hs]
    _ = _ := by simp_rw [sub_mul]; exact (integral_sub hi₃ hi₂).symm

theorem characteristic_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) (a : Cover) :
    (∫ x, |characteristic E (x - quotientMap a) - characteristic E x| ∂torusVolume)
      ≤ ‖a‖ * (perimeter E).toReal := by
  let g : Torus → ℝ := fun x => characteristic E (x - quotientMap a) - characteristic E x
  have hg : Measurable g := ((measurable_characteristic hE).comp
    (measurable_id.sub_const _)).sub (measurable_characteristic hE)
  have hb (x) : |g x| ≤ 1 := by
    rcases characteristic_dichotomy E (x - quotientMap a) with h | h <;>
      rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
  have heq (x) : g x * g x = |g x| := by
    rcases characteristic_dichotomy E (x - quotientMap a) with h | h <;>
      rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
  have h := torus_test_translation_bound hE hP hg hb a
  rw [integral_difference_test hE hg hb] at h
  change |∫ x, g x * g x ∂torusVolume| ≤ _ at h
  simp_rw [heq] at h
  rw [abs_of_nonneg (integral_nonneg fun x => abs_nonneg (g x))] at h
  exact h

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma smoothApprox_lipschitz {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (n : ℕ) : LipschitzWith (smoothApproxLip n) (smoothApprox g n) := by
  have hφ := (mollifier n).contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))
  have hφc := (mollifier n).hasCompactSupport_normed (μ := volume)
  have hd (x) := hφc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))
    (locallyIntegrable_of_bounded hg hb) x
  have hdi : Integrable (fun y : Cover => ‖fderiv ℝ ((mollifier n).normed volume) y‖)
      volume :=
    (hφ.continuous_fderiv (by simp)).norm.integrable_of_hasCompactSupport (hφc.fderiv ℝ).norm
  apply lipschitzWith_of_nnnorm_fderiv_le ((smoothApprox_contDiff hg hb n).differentiable (by simp))
  intro x
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (smoothApprox g n) x‖ ≤ _
  change ‖fderiv ℝ (((mollifier n).normed volume) ⋆ g) x‖ ≤ _
  rw [(hd x).fderiv, convolution_def]
  apply norm_integral_le_of_norm_le hdi
  exact Eventually.of_forall fun y => by
    have heq : ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Cover
        (fderiv ℝ ((mollifier n).normed volume) y)) (g (x - y)) =
        g (x - y) • fderiv ℝ ((mollifier n).normed volume) y := by
      ext v
      simp [ContinuousLinearMap.precompL_apply, mul_comm]
    rw [heq, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb (x - y))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

lemma torusApprox_sub_eq_integral {E : Set Torus} (hE : MeasurableSet E) (n : ℕ) (x : Torus) :
    torusApprox E n x - characteristic E x =
      ∫ y : Cover, (mollifier n).normed volume y *
        (characteristic E (x - quotientMap y) - characteristic E x) := by
  have hm : Measurable (fun y => characteristic E (x - quotientMap y)) :=
    (measurable_characteristic hE).comp (measurable_const.sub measurable_quotientMap)
  have hi := ((mollifier n).integrable_normed (μ := volume)).mul_bdd hm.aestronglyMeasurable
    (Eventually.of_forall fun y => characteristic_bound E (x - quotientMap y))
  simp_rw [mul_sub]
  rw [integral_sub hi ((mollifier n).integrable_normed.mul_const _),
    integral_mul_const, (mollifier n).integral_normed, one_mul]
  congr 1
  simp only [torusApprox, smoothApprox, convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, Function.comp_def, quotientMap_sub, quotientMap_representative]

theorem torusApprox_error {E : Set Torus} (hE : MeasurableSet E) (hP : perimeter E ≠ ⊤)
    (n : ℕ) :
    (∫ x, |torusApprox E n x - characteristic E x| ∂torusVolume) ≤
      (mollifier n).rOut * (perimeter E).toReal := by
  let φ : Cover → ℝ := (mollifier n).normed volume
  let d : Torus × Cover → ℝ := fun z =>
    |characteristic E (z.1 - quotientMap z.2) - characteristic E z.1|
  have hφ : Integrable φ volume := (mollifier n).integrable_normed
  have hφm : Measurable φ := ((mollifier n).contDiff_normed (n := (⊤ : ℕ∞))).continuous.measurable
  have hd : Measurable d := by
    exact (((measurable_characteristic hE).comp
      (measurable_fst.sub (measurable_quotientMap.comp measurable_snd))).sub
        ((measurable_characteristic hE).comp measurable_fst)).abs
  have hd_bound (z) : |d z| ≤ 1 := by
    rcases characteristic_dichotomy E (z.1 - quotientMap z.2) with h | h <;>
      rcases characteristic_dichotomy E z.1 with h' | h' <;> simp [d, h, h']
  have hbase : Integrable (fun z : Torus × Cover => φ z.2) (torusVolume.prod volume) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := torusVolume)).mul_prod hφ
  have hprod : Integrable (fun z : Torus × Cover => φ z.2 * d z) (torusVolume.prod volume) :=
    hbase.mul_bdd hd.aestronglyMeasurable (Eventually.of_forall hd_bound)
  have hip (x : Torus) : Integrable
      (fun y : Cover => φ y * (characteristic E (x - quotientMap y) - characteristic E x)) volume := by
    apply hφ.mul_bdd (c := 1)
      (((measurable_characteristic hE).comp (measurable_const.sub measurable_quotientMap)).sub
        measurable_const).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rcases characteristic_dichotomy E (x - quotientMap y) with h | h <;>
        rcases characteristic_dichotomy E x with h' | h' <;> simp [h, h']
  have hinside (x : Torus) : |torusApprox E n x - characteristic E x| ≤
      ∫ y : Cover, φ y * d (x, y) := by
    rw [torusApprox_sub_eq_integral hE]
    calc
      _ ≤ ∫ y : Cover, ‖φ y * (characteristic E (x - quotientMap y) - characteristic E x)‖ :=
        norm_integral_le_integral_norm _
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          simp [d, Real.norm_eq_abs, abs_of_nonneg ((mollifier n).nonneg_normed y), φ]
  have hipx (y : Cover) : Integrable (fun x : Torus => d (x, y)) torusVolume := by
    apply Integrable.of_bound (hd.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => hd_bound (x, y)
  have htrans (y : Cover) : (∫ x, d (x, y) ∂torusVolume) ≤ ‖y‖ * (perimeter E).toReal :=
    characteristic_translation_bound hE hP y
  have hkernel (y : Cover) : φ y * (∫ x, d (x, y) ∂torusVolume) ≤
      φ y * ((mollifier n).rOut * (perimeter E).toReal) := by
    by_cases hy : φ y = 0
    · simp [hy]
    have hy' : y ∈ Metric.ball (0 : Cover) (mollifier n).rOut := by
      rw [← (mollifier n).support_normed_eq (μ := (volume : Measure Cover))]
      exact hy
    have hnorm : ‖y‖ ≤ (mollifier n).rOut := le_of_lt (by simpa using hy')
    exact mul_le_mul_of_nonneg_left
      ((htrans y).trans (mul_le_mul_of_nonneg_right hnorm ENNReal.toReal_nonneg))
        ((mollifier n).nonneg_normed y)
  calc
    _ ≤ ∫ x, ∫ y : Cover, φ y * d (x, y) ∂volume ∂torusVolume := by
      exact integral_mono ((torusApprox_integrable hE n).sub (integrable_characteristic hE)).abs
        hprod.integral_prod_left hinside
    _ = ∫ y : Cover, ∫ x, φ y * d (x, y) ∂torusVolume := integral_integral_swap hprod
    _ = ∫ y : Cover, φ y * (∫ x, d (x, y) ∂torusVolume) := by
      simp_rw [integral_const_mul]
    _ ≤ ∫ y : Cover, φ y * ((mollifier n).rOut * (perimeter E).toReal) := by
      apply integral_mono _ (hφ.mul_const _) hkernel
      simpa only [integral_const_mul] using hprod.integral_prod_right
    _ = _ := by rw [integral_mul_const, (mollifier n).integral_normed, one_mul]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma cubeToL1_lipschitz : LipschitzWith 1 cubeToL1 := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [NNReal.coe_one, one_mul]
  have hi : Integrable (fun x => dist (f (cubeRepresentative x)) (g (cubeRepresentative x)))
      torusVolume := by
    simpa only [dist_eq_norm, Pi.sub_apply] using ((integrable_cubeEval f).sub (integrable_cubeEval g)).norm
  calc
    _ = ∫ x, dist (f (cubeRepresentative x)) (g (cubeRepresentative x)) ∂torusVolume := by
      rw [L1.dist_eq_integral_dist]
      apply integral_congr_ae
      filter_upwards [(integrable_cubeEval f).coeFn_toL1, (integrable_cubeEval g).coeFn_toL1] with x hx hx'
      change dist ((integrable_cubeEval f).toL1 _ x) ((integrable_cubeEval g).toL1 _ x) = _
      rw [hx, hx']
    _ ≤ ∫ _x : Torus, dist f g ∂torusVolume :=
      integral_mono hi (integrable_const _) (fun x => BoundedContinuousFunction.dist_coe_le_dist _)
    _ = _ := by simp

lemma dist_torusApproxL1 {E : Set Torus} (hE : MeasurableSet E) (hP : perimeter E ≠ ⊤) (n : ℕ) :
    dist (characteristicL1 E hE) (torusApproxL1 E hE n) ≤
      (mollifier n).rOut * (perimeter E).toReal := by
  calc
    _ = ∫ x, |torusApprox E n x - characteristic E x| ∂torusVolume := by
      rw [L1.dist_eq_integral_dist]
      apply integral_congr_ae
      filter_upwards [(integrable_characteristic hE).coeFn_toL1,
        (torusApprox_integrable hE n).coeFn_toL1] with x hx hx'
      change dist ((integrable_characteristic hE).toL1 _ x) ((torusApprox_integrable hE n).toL1 _ x) = _
      rw [hx, hx', Real.dist_eq, abs_sub_comm]
    _ ≤ _ := torusApprox_error hE hP n

lemma totallyBounded_torusApproxL1 {ι : Type*} (Es : ι → Set Torus)
    (hEs : ∀ i, MeasurableSet (Es i)) (n : ℕ) :
    TotallyBounded (range (fun i => torusApproxL1 (Es i) (hEs i) n)) := by
  let F : ι → BoundedContinuousFunction CompactCell ℝ := fun i => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => smoothApprox (characteristic (Es i) ∘ quotientMap) n x,
      (smoothApprox_contDiff ((measurable_characteristic (hEs i)).comp measurable_quotientMap)
        (fun x => characteristic_bound (Es i) (quotientMap x)) n).continuous.comp continuous_subtype_val⟩
  have hLip (i) : LipschitzWith (smoothApproxLip n) (F i) := by
    change LipschitzWith (smoothApproxLip n)
      (smoothApprox (characteristic (Es i) ∘ quotientMap) n ∘ (Subtype.val : CompactCell → Cover))
    simpa only [mul_one] using
      (smoothApprox_lipschitz ((measurable_characteristic (hEs i)).comp measurable_quotientMap)
        (fun x => characteristic_bound (Es i) (quotientMap x)) n).comp
          (LipschitzWith.subtype_val closedFundamentalCube)
  have hEq : Equicontinuous ((↑) : range F → CompactCell → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (smoothApproxLip n)
    rintro ⟨_, i, rfl⟩
    exact hLip i
  have hbounded (f : BoundedContinuousFunction CompactCell ℝ) (x : CompactCell) (hf : f ∈ range F) : f x ∈ Icc (-1) 1 := by
    obtain ⟨i, rfl⟩ := hf
    exact abs_le.mp (smoothApprox_bound (fun y => characteristic_bound (Es i) (quotientMap y)) n x)
  have hcompact := BoundedContinuousFunction.arzela_ascoli (Icc (-1 : ℝ) 1) isCompact_Icc
    (range F) hbounded hEq
  apply ((hcompact.image cubeToL1_lipschitz.continuous).totallyBounded).subset
  rintro _ ⟨i, rfl⟩
  exact ⟨F i, subset_closure (mem_range_self i), rfl⟩

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma totallyBounded_characteristicL1 {ι : Type*} (Es : ι → Set Torus)
    (hEs : ∀ i, MeasurableSet (Es i)) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i, perimeter (Es i) ≤ ENNReal.ofReal C) :
    TotallyBounded (range (fun i => characteristicL1 (Es i) (hEs i))) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hconv : Tendsto (fun n => (mollifier n).rOut * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using mollifier_rOut_tendsto.mul_const C
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
    (totallyBounded_torusApproxL1 Es hEs n) (ε / 2) (half_pos hε)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy, hiy⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  apply mem_iUnion₂.mpr
  refine ⟨y, hy, ?_⟩
  change dist (characteristicL1 (Es i) (hEs i)) y < ε
  have hfin : perimeter (Es i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hP i)
  have hreal : (perimeter (Es i)).toReal ≤ C := by
    simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top (hP i)
  have hdist : dist (characteristicL1 (Es i) (hEs i)) (torusApproxL1 (Es i) (hEs i) n) < ε / 2 :=
    ((dist_torusApproxL1 (hEs i) hfin n).trans
      (mul_le_mul_of_nonneg_left hreal (mollifier n).rOut_pos.le)).trans_lt hn
  have hiy' : dist (torusApproxL1 (Es i) (hEs i) n) y < ε / 2 := hiy
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

theorem exists_ae_tendsto_characteristic {Es : ℕ → Set Torus}
    (hEs : ∀ n, MeasurableSet (Es n)) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ n, perimeter (Es n) ≤ ENNReal.ofReal C) :
    ∃ E : Set Torus, MeasurableSet E ∧ ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂torusVolume, Tendsto (fun n => characteristic (Es (ns n)) x) atTop
        (𝓝 (characteristic E x)) := by
  let fs : ℕ → Lp ℝ 1 torusVolume := fun n => characteristicL1 (Es n) (hEs n)
  have hcompact : IsCompact (closure (range fs)) :=
    (totallyBounded_characteristicL1 Es hEs hC hP).closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨f, _, ns, hns, hconv⟩ := hcompact.isSeqCompact.subseq_of_frequently_in
    (Frequently.of_forall (fun n => subset_closure (mem_range_self n)))
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ x ∂torusVolume, ∀ n, (fs (ns (ms n))) x = characteristic (Es (ns (ms n))) x :=
    ae_all_iff.mpr (fun n => (integrable_characteristic (hEs (ns (ms n)))).coeFn_toL1)
  let E : Set Torus := {x | f x = 1}
  have hE : MeasurableSet E := (Lp.stronglyMeasurable f).measurable (measurableSet_singleton 1)
  refine ⟨E, hE, ns ∘ ms, hns.comp hms, ?_⟩
  filter_upwards [hae, hcoe] with x hx hcx
  have ht : Tendsto (fun n => characteristic (Es (ns (ms n))) x) atTop (𝓝 (f x)) := by
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact (hcx n).symm
  have hfx : f x ∈ ({0, 1} : Set ℝ) := by
    apply ((finite_singleton (1 : ℝ)).insert 0).isClosed.mem_of_tendsto ht
    exact Eventually.of_forall fun n => by
      rcases characteristic_dichotomy (Es (ns (ms n))) x with h | h <;> simp [h]
  have hchar : characteristic E x = f x := by
    rcases mem_insert_iff.mp hfx with hzero | hone
    · have hxE : x ∉ E := by simp only [E, mem_ofPred_eq, hzero]; norm_num
      simp [characteristic, hxE, hzero]
    · have hxE : x ∈ E := hone
      simpa [characteristic, hxE] using hone.symm
  simpa only [Function.comp_apply, hchar] using ht

end CubicTorus

namespace CubicTorus

lemma measurableSet_stripe (V : ℝ) : MeasurableSet (stripe V) := by
  apply measurableSet_lt _ measurable_const
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))

lemma stripe_lift_preimage {V : ℝ} (hV : V ∈ Icc 0 1) :
    (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹'
      (fundamentalCube ∩ quotientMap ⁻¹' stripe V) =
      univ.pi (fun i : Fin 3 => Ico 0 (stripeUpper V i)) := by
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i < 1) ∧
    ((AddCircle.equivIco (1 : ℝ) 0) (x 0 : AddCircle (1 : ℝ)) : ℝ) < V) ↔ _
  constructor
  · rintro ⟨hc, hs⟩ i _
    have he : ((AddCircle.equivIco (1 : ℝ) 0) (x 0 : AddCircle (1 : ℝ)) : ℝ) = x 0 :=
      AddCircle.equivIco_coe_of_mem (by simpa using hc 0)
    rw [he] at hs
    by_cases hi : i = 0
    · subst i
      simpa [stripeUpper] using And.intro (hc 0).1 hs
    · simpa [stripeUpper, hi] using hc i
  · intro hx
    have hc : ∀ i, 0 ≤ x i ∧ x i < 1 := by
      intro i
      have hh := hx i (mem_univ i)
      by_cases hi : i = 0
      · subst i
        simp only [stripeUpper, Function.update_self, mem_Ico] at hh
        exact ⟨hh.1, lt_of_lt_of_le hh.2 hV.2⟩
      · simpa [stripeUpper, hi] using hh
    refine ⟨hc, ?_⟩
    rw [AddCircle.equivIco_coe_of_mem (by simpa using hc 0)]
    simpa [stripeUpper] using (hx 0 (mem_univ 0)).2

lemma volume_stripe {V : ℝ} (hV : V ∈ Icc 0 1) :
    torusVolume (stripe V) = ENNReal.ofReal V := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_stripe V),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_stripe V)), inter_comm]
  have hm := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    ((measurableSet_fundamentalCube.inter (measurable_quotientMap (measurableSet_stripe V))).nullMeasurableSet)
  rw [stripe_lift_preimage hV] at hm
  rw [← hm, Real.volume_pi_Ico]
  norm_num [stripeUpper, Fin.prod_univ_succ]

lemma integral_divergence_stripe {V : ℝ} (hV : V ∈ Icc 0 1)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' stripe V, divergence F x) =
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
        F (WithLp.toLp 2 ((0 : Fin 3).insertNth V x)) 0) -
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
        F (WithLp.toLp 2 ((0 : Fin 3).insertNth 0 x)) 0) := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let b := stripeUpper V
  let g : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x => F (e.symm x) i
  let dg : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i x => (EuclideanSpace.proj i).comp
      ((fderiv ℝ F (e.symm x)).comp e.symm.toContinuousLinearMap)
  have hdg : ∀ i x, HasFDerivAt (g i) (dg i x) x := by
    intro i x
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      (((hF.1.differentiable (by simp)) (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt)
  have hd : (fun x => ∑ i : Fin 3, dg i x (Pi.single i 1)) =
      fun x => divergence F (e.symm x) := by
    funext x
    simp [dg, divergence, e, PiLp.toLp_single]
  have hct : Continuous (fun x => divergence F (e.symm x)) :=
    (continuous_divergence hF.1).comp e.symm.continuous
  have hb : ∀ i, (0 : Fin 3 → ℝ) i ≤ b i := by
    intro i
    by_cases hi : i = 0
    · subst i; simpa [b, stripeUpper] using hV.1
    · simp [b, stripeUpper, hi]
  have hth := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) b hb g dg ∅ countable_empty
    (fun i => ((EuclideanSpace.proj i).continuous.comp
      (hF.1.continuous.comp e.symm.continuous)).continuousOn)
    (fun x _ i => hdg i x) (by rw [hd]; exact hct.integrableOn_Icc)
  rw [hd] at hth
  have hzero : ∀ i : Fin 3, i ≠ 0 →
      (∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) (b ∘ i.succAbove),
        g i (i.insertNth (b i) x)) -
      (∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) (b ∘ i.succAbove),
        g i (i.insertNth 0 x)) = 0 := by
    intro i hi
    have heq : (fun x : Fin 2 → ℝ => g i (i.insertNth (b i) x)) =
        (fun x : Fin 2 → ℝ => g i (i.insertNth 0 x)) := by
      funext x
      have hbi : b i = 1 := by simp [b, stripeUpper, hi]
      rw [hbi]
      change F (WithLp.toLp 2 (i.insertNth 1 x)) i = F (WithLp.toLp 2 (i.insertNth 0 x)) i
      rw [adjacent_faces, hF.2.1]
    rw [heq, sub_self]
  simp only [Pi.zero_apply] at hth
  rw [Finset.sum_eq_single 0 (fun i _ hi => hzero i hi) (by simp)] at hth
  have hab : b ∘ (0 : Fin 3).succAbove = (1 : Fin 2 → ℝ) := by
    ext i
    simp [b, stripeUpper]
  have ha0 : (0 : Fin 3 → ℝ) ∘ (0 : Fin 3).succAbove = (0 : Fin 2 → ℝ) := rfl
  rw [hab, ha0] at hth
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding, stripe_lift_preimage hV]
  rw [volume_pi, setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc]
  rw [← volume_pi]
  convert hth using 1 <;> simp [g, b, stripeUpper, e]
  rfl

end CubicTorus

namespace CubicTorus

lemma volume_square_face : volume (Icc (0 : Fin 2 → ℝ) 1) = 1 := by
  rw [Real.volume_Icc_pi]
  norm_num

lemma stripe_flux_bound {F : Cover → Cover} (hF : AdmissibleField F) (a : ℝ) :
    |∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth a x)) 0| ≤ 1 := by
  have hh := norm_setIntegral_le_of_norm_le_const
    (show volume (Icc (0 : Fin 2 → ℝ) 1) < ⊤ by rw [volume_square_face]; norm_num)
    (fun x (_ : x ∈ Icc (0 : Fin 2 → ℝ) 1) =>
      (PiLp.norm_apply_le (F (WithLp.toLp 2 ((0 : Fin 3).insertNth a x))) 0).trans (hF.2.2 _))
  simpa only [Real.norm_eq_abs, Measure.real, volume_square_face, ENNReal.toReal_one, mul_one] using hh

theorem perimeter_stripe_le {V : ℝ} (hV : V ∈ Icc 0 1) : perimeter (stripe V) ≤ 2 := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [integral_divergence_stripe hV hF]
  have hupper := (abs_le.1 (stripe_flux_bound hF V)).2
  have hlower := (abs_le.1 (stripe_flux_bound hF 0)).1
  have hh : (∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth V x)) 0) -
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth 0 x)) 0) ≤ 2 := by linarith
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (by norm_num)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

theorem exists_isMinimizerAt {V : ℝ} (hV : V ∈ Ioo 0 1) :
    ∃ E : Set Torus, IsMinimizerAt V E := by
  let S : Set ℝ≥0∞ := {p | ∃ E : Set Torus, MeasurableSet E ∧
    torusVolume E = ENNReal.ofReal V ∧ perimeter E = p ∧ p ≤ 2}
  have hV' : V ∈ Icc (0 : ℝ) 1 := ⟨hV.1.le, hV.2.le⟩
  have hne : S.Nonempty := ⟨perimeter (stripe V), stripe V, measurableSet_stripe V,
    volume_stripe hV', rfl, perimeter_stripe_le hV'⟩
  have hinf : sInf S ≤ 2 := (sInf_le hne.choose_spec).trans hne.choose_spec.choose_spec.2.2.2
  obtain ⟨ps, _, hconv, hps⟩ := exists_seq_tendsto_sInf hne (OrderBot.bddBelow S)
  choose Es hEs hvol hpEq hpBound using hps
  have hbound : ∀ n, perimeter (Es n) ≤ ENNReal.ofReal 2 := by
    intro n
    rw [hpEq n]
    simpa using hpBound n
  obtain ⟨E, hE, ns, hns, hae⟩ := exists_ae_tendsto_characteristic hEs (by norm_num) hbound
  have hvo : torusVolume E = ENNReal.ofReal V := by
    have ht := tendsto_volume_of_ae_tendsto (fun n => (hEs (ns n)).nullMeasurableSet)
      hE.nullMeasurableSet hae
    have hc : Tendsto (fun n => torusVolume (Es (ns n))) atTop (𝓝 (ENNReal.ofReal V)) := by
      simpa only [hvol] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ENNReal.ofReal V) atTop _)
    exact tendsto_nhds_unique ht hc
  have hpe : perimeter E ≤ sInf S :=
    perimeter_le_of_ae_tendsto_bound (fun n => (hEs (ns n)).nullMeasurableSet)
      hE.nullMeasurableSet hae (fun n => (hpEq (ns n)).le) (hconv.comp hns.tendsto_atTop)
  refine ⟨E, ⟨hE.nullMeasurableSet, (hpe.trans hinf).trans_lt (by norm_num)⟩, hvo, ?_⟩
  intro F hF hFv
  by_cases hFp : perimeter F ≤ 2
  · have hrep := hF.1.toMeasurable_ae_eq
    have hex : perimeter F ∈ S := by
      refine ⟨toMeasurable torusVolume F, measurableSet_toMeasurable _ _, ?_, ?_, hFp⟩
      · exact (measure_congr hrep).trans hFv
      · exact perimeter_congr_ae hrep
    exact hpe.trans (sInf_le hex)
  · exact (hpe.trans hinf).trans (le_of_lt (lt_of_not_ge hFp))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma characteristic_translation_ae_of_perimeter_zero {E : Set Torus}
    (hE : MeasurableSet E) (hP : perimeter E = 0) (a : Torus) :
    (fun x ↦ characteristic E (x - a)) =ᵐ[torusVolume] characteristic E := by
  have h := characteristic_translation_bound hE (hP ▸ ENNReal.zero_ne_top) (representative a)
  rw [quotientMap_representative, hP, ENNReal.toReal_zero, mul_zero] at h
  have hg : Measurable (fun x ↦ |characteristic E (x - a) - characteristic E x|) :=
    (((measurable_characteristic hE).comp (measurable_id.sub_const a)).sub
      (measurable_characteristic hE)).abs
  have hi : Integrable (fun x ↦ |characteristic E (x - a) - characteristic E x|) torusVolume := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact Eventually.of_forall fun x ↦ by
      rcases characteristic_dichotomy E (x - a) with h | h <;>
        rcases characteristic_dichotomy E x with h' | h' <;> simp [h, h']
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ abs_nonneg _) hi).1
    (le_antisymm h (integral_nonneg fun x ↦ abs_nonneg _))
  filter_upwards [hae] with x hx
  exact sub_eq_zero.1 (abs_eq_zero.1 hx)

theorem volume_eq_zero_or_one_of_perimeter_zero {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hP : perimeter E = 0) :
    torusVolume E = 0 ∨ torusVolume E = 1 := by
  wlog hEm : MeasurableSet E generalizing E
  · have hae := hE.toMeasurable_ae_eq
    have hP' : perimeter (toMeasurable torusVolume E) = 0 := (perimeter_congr_ae hae).trans hP
    have hh := this (measurableSet_toMeasurable torusVolume E).nullMeasurableSet hP'
      (measurableSet_toMeasurable torusVolume E)
    rwa [measure_congr hae] at hh
  have hall : ∀ᵐ a ∂torusVolume, ∀ᵐ x ∂torusVolume,
      characteristic E (x + a) = characteristic E x := by
    exact Eventually.of_forall fun a ↦ by
      have hh := characteristic_translation_ae_of_perimeter_zero hEm hP (-a)
      filter_upwards [hh] with x hx
      simpa only [sub_neg_eq_add] using hx
  have hswap := (Measure.ae_ae_comm (μ := torusVolume) (ν := torusVolume)
    (p := fun a x ↦ characteristic E (x + a) = characteristic E x)
    (measurableSet_eq_fun ((measurable_characteristic hEm).comp (measurable_snd.add measurable_fst))
      ((measurable_characteristic hEm).comp measurable_snd))).1 hall
  obtain ⟨x, hx⟩ := hswap.exists
  have hav := integral_congr_ae hx
  rw [integral_add_left_eq_self, integral_characteristic hE, integral_const] at hav
  simp only [Measure.real_def, torusVolume_univ, ENNReal.toReal_one, one_smul] at hav
  rcases characteristic_dichotomy E x with h0 | h1
  · left
    exact ((ENNReal.toReal_eq_zero_iff _).1 (hav.trans h0)).resolve_right (measure_ne_top _ _)
  · right
    have hh := congrArg ENNReal.ofReal (hav.trans h1)
    simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_one] using hh

theorem perimeter_pos_of_volume {V : ℝ} (hV : V ∈ Ioo 0 1) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hvolume : torusVolume E = ENNReal.ofReal V) :
    0 < perimeter E := by
  apply bot_lt_iff_ne_bot.2
  intro hzero
  rcases volume_eq_zero_or_one_of_perimeter_zero hE hzero with h0 | h1
  · rw [hvolume] at h0
    exact (ENNReal.ofReal_pos.2 hV.1).ne' h0
  · rw [hvolume] at h1
    have hh := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_ofReal hV.1.le, ENNReal.toReal_one] at hh
    exact hV.2.ne hh

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma isoperimetricProfile_eq_of_isMinimizerAt {V : ℝ} {E : Set Torus}
    (hE : IsMinimizerAt V E) : isoperimetricProfile V = (perimeter E).toReal / 2 := by
  have heq : sInf {p : ℝ≥0∞ | ∃ F : Set Torus,
      FinitePerimeter F ∧ torusVolume F = ENNReal.ofReal V ∧ perimeter F = p} = perimeter E := by
    apply le_antisymm
    · exact sInf_le ⟨E, hE.1, hE.2.1, rfl⟩
    · apply le_sInf
      rintro p ⟨F, hF, hFv, rfl⟩
      exact hE.2.2 F hF hFv
  simp only [isoperimetricProfile, heq]

lemma isMinimizerAt_empty : IsMinimizerAt 0 ∅ := by
  refine ⟨finitePerimeter_empty, by simp, ?_⟩
  intro F _ _
  rw [perimeter_empty]
  exact bot_le

lemma isMinimizerAt_univ : IsMinimizerAt 1 univ := by
  have hh := (isMinimizerAt_compl (by norm_num : (0 : ℝ) ∈ Icc 0 1)).2 isMinimizerAt_empty
  simpa using hh

theorem exists_isMinimizerAt_Icc {V : ℝ} (hV : V ∈ Icc 0 1) :
    ∃ E : Set Torus, IsMinimizerAt V E := by
  rcases hV.1.eq_or_lt with h | h
  · subst V
    exact ⟨∅, isMinimizerAt_empty⟩
  rcases hV.2.eq_or_lt with h' | h'
  · subst V
    exact ⟨univ, isMinimizerAt_univ⟩
  exact exists_isMinimizerAt ⟨h, h'⟩

lemma isoperimetricProfile_le_competitor {V : ℝ} (hV : V ∈ Icc 0 1)
    {E : Set Torus} (hE : FinitePerimeter E) (hvol : torusVolume E = ENNReal.ofReal V) :
    isoperimetricProfile V ≤ (perimeter E).toReal / 2 := by
  obtain ⟨F, hF⟩ := exists_isMinimizerAt_Icc hV
  rw [isoperimetricProfile_eq_of_isMinimizerAt hF]
  exact div_le_div_of_nonneg_right (ENNReal.toReal_mono hE.2.ne (hF.2.2 E hE hvol)) (by norm_num)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma divergence_smul_function {f : Cover → ℝ} {F : Cover → Cover} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (hF : DifferentiableAt ℝ F point) :
    divergence (fun y ↦ f y • F y) point = f point * divergence F point +
      ⟪gradient f point, F point⟫ := by
  have ha : (∑ i : Fin 3, F point i • EuclideanSpace.single i 1) = F point := by
    ext j
    simp [Pi.single_apply]
  rw [inner_gradient_left]
  conv_rhs => rw [← ha, map_sum]
  change (∑ i : Fin 3, (fderiv ℝ (f • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_smul hf hF]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    divergence, Finset.mul_sum, map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GradientCalibration
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalMeasure_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    (∫ z, normalTest F hF.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  have hG : AdmissibleField (fun x ↦ k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      exact (mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hk.le)).trans_eq
        (inv_mul_cancel₀ hk.ne')
  have hh := hμ.2 _ hG
  simp only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right,
    integral_const_mul] at hh ⊢
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul] at hh
  exact mul_left_cancel₀ (inv_ne_zero hk.ne') hh

end CubicTorus

open scoped RealInnerProductSpace

namespace CubicTorus
open Filter
open scoped Topology

lemma coordinateMove_contDiff (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateMove i f t) := by
  unfold coordinateMove
  fun_prop

lemma coordinateMove_hasFDerivAt (i : Fin 3) {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (t : ℝ) :
    HasFDerivAt (coordinateMove i f t) (coordinateMoveDeriv i f t point) point := by
  have h₁ : HasFDerivAt (fun y : Cover ↦ y) (ContinuousLinearMap.id ℝ Cover) point :=
    hasFDerivAt_id point
  have h₂ := (hf.hasFDerivAt.const_mul t).smul_const
    (EuclideanSpace.single i (1 : ℝ) : Cover)
  have he : coordinateMoveDeriv i f t point = ContinuousLinearMap.id ℝ Cover +
      (t • fderiv ℝ f point).smulRight (EuclideanSpace.single i (1 : ℝ) : Cover) := by
    ext y j
    simp [coordinateMoveDeriv, mul_comm]
  rw [he]
  exact h₁.add h₂

lemma coordinateMove_periodic (i : Fin 3) {f : Cover → ℝ}
    (hp : ∀ n x, f (x + latticeVector n) = f x) (t : ℝ) (n : Fin 3 → ℤ) (x : Cover) :
    coordinateMove i f t (x + latticeVector n) = coordinateMove i f t x + latticeVector n := by
  simp only [coordinateMove, hp]
  abel

lemma coordinateMoveDeriv_det (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x : Cover) :
    (coordinateMoveDeriv i f t x).det = coordinateJacobian i f t x := by
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : LinearMap.toMatrix B B (coordinateMoveDeriv i f t x).toLinearMap =
      Matrix.of (fun j k ↦ (if j = k then 1 else 0) +
        (if j = i then t * fderiv ℝ f x (EuclideanSpace.single k 1) else 0)) := by
    ext j k
    rw [LinearMap.toMatrix_apply]
    change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
      (coordinateMoveDeriv i f t x ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) j = _
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply]
    by_cases h : j = i <;> simp [coordinateMoveDeriv, h, mul_comm]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, he]
  rw [Matrix.det_fin_three]
  fin_cases i <;> simp [coordinateJacobian]

lemma coordinateMove_injective (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) : Function.Injective (coordinateMove i f t) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro x y hxy
  have he : x - y = -(t * (f x - f y)) • EuclideanSpace.single i 1 := by
    calc
      x - y = coordinateMove i f t x - coordinateMove i f t y -
          (t * (f x - f y)) • EuclideanSpace.single i 1 := by
        unfold coordinateMove
        module
      _ = _ := by rw [hxy, sub_self, zero_sub, neg_smul]
  have hn : ‖x - y‖ = |t| * ‖f x - f y‖ := by
    rw [he, norm_smul, norm_neg, Real.norm_eq_abs, abs_mul]
    simp [Real.norm_eq_abs]
  have hh : ‖x - y‖ ≤ |t| * M * ‖x - y‖ := by
    have hz := hLip.norm_sub_le x y
    calc
      ‖x - y‖ = |t| * ‖f x - f y‖ := hn
      _ ≤ |t| * (M * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = _ := by ring
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma divergence_sub_fields {F G : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (hG : DifferentiableAt ℝ G point) :
    divergence (fun y ↦ F y - G y) point = divergence F point - divergence G point := by
  change (∑ i : Fin 3, (fderiv ℝ (F - G) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_sub hF hG]
  simp [divergence, Finset.sum_sub_distrib]

lemma linearForm_apply_basis (L : Cover →L[ℝ] ℝ) (v : Cover) :
    L v = ∑ j : Fin 3, v j * L (EuclideanSpace.single j 1) := by
  have hv : (∑ j : Fin 3, v j • EuclideanSpace.single j 1) = v := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [← hv, map_sum]
  simp

lemma divergence_comp_coordinateMove (i : Fin 3) {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) {G : Cover → Cover} {time : ℝ}
    (hG : DifferentiableAt ℝ G (coordinateMove i f time point)) :
    divergence (fun y ↦ G (coordinateMove i f time y)) point =
      divergence G (coordinateMove i f time point) +
        time * fderiv ℝ f point
          (fderiv ℝ G (coordinateMove i f time point) (EuclideanSpace.single i 1)) := by
  have hm := coordinateMove_hasFDerivAt i hf time
  have hd := (hG.hasFDerivAt.comp point hm).fderiv
  change fderiv ℝ (fun y ↦ G (coordinateMove i f time y)) point = _ at hd
  simp only [divergence, hd,
    coordinateMoveDeriv, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [linearForm_apply_basis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coordinateJacobian_contDiff (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateJacobian i f t) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  unfold coordinateJacobian
  fun_prop

lemma coordinatePullback_contDiff (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) {G : Cover → Cover}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinatePullback i f t G) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hm := coordinateMove_contDiff i hf t
  have hj := coordinateJacobian_contDiff i hf t
  unfold coordinatePullback
  exact (hj.smul (hG.comp hm)).sub
    ((contDiff_const.mul (hd.clm_apply (hG.comp hm))).smul contDiff_const)

lemma coordinatePullback_periodic (i : Fin 3) {f : Cover → ℝ}
    (hp : ∀ n x, f (x + latticeVector n) = f x) (t : ℝ) {G : Cover → Cover}
    (hG : ∀ n x, G (x + latticeVector n) = G x) (n : Fin 3 → ℤ) (x : Cover) :
    coordinatePullback i f t G (x + latticeVector n) = coordinatePullback i f t G x := by
  simp only [coordinatePullback, coordinateJacobian, fderiv_periodic hp,
    coordinateMove_periodic i hp, hG]

lemma coordinatePullback_divergence (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) {G : Cover → Cover}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Cover) :
    divergence (coordinatePullback i f t G) x =
      coordinateJacobian i f t x * divergence G (coordinateMove i f t x) := by
  have hfd := (hf.differentiable (by simp)).differentiableAt (x := x)
  have hdf := ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp)).differentiableAt (x := x)
  have hm := coordinateMove_hasFDerivAt i hfd t
  have hg := (hG.differentiable (by simp)).differentiableAt (x := coordinateMove i f t x)
  have hu := hg.hasFDerivAt.comp x hm
  have hj := ((hdf.hasFDerivAt.clm_apply (hasFDerivAt_const
    (EuclideanSpace.single i (1 : ℝ) : Cover) x)).const_mul t).const_add 1
  have hb := (hdf.hasFDerivAt.clm_apply hu).const_mul t
  have he := ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top))
    (EuclideanSpace.single i 1) (G (coordinateMove i f t x))
  change divergence (fun y ↦ coordinateJacobian i f t y • G (coordinateMove i f t y) -
    (t * fderiv ℝ f y (G (coordinateMove i f t y))) • EuclideanSpace.single i 1) x = _
  have hjf := hj.fderiv
  change fderiv ℝ (coordinateJacobian i f t) x = _ at hjf
  dsimp only [Function.comp_def] at hb
  have hJ : DifferentiableAt ℝ (coordinateJacobian i f t) x := hj.differentiableAt
  have hU : DifferentiableAt ℝ (fun y ↦ G (coordinateMove i f t y)) x := hu.differentiableAt
  have hB : DifferentiableAt ℝ
      (fun y ↦ t * fderiv ℝ f y (G (coordinateMove i f t y))) x := hb.differentiableAt
  have hA : DifferentiableAt ℝ
      (fun y ↦ coordinateJacobian i f t y • G (coordinateMove i f t y)) x := hJ.smul hU
  have hC : DifferentiableAt ℝ
      (fun y ↦ (t * fderiv ℝ f y (G (coordinateMove i f t y))) •
        (EuclideanSpace.single i 1 : Cover)) x := hB.smul_const _
  rw [divergence_sub_fields hA hC,
    divergence_smul_function hJ hU,
    divergence_smul_const hB, inner_gradient_left,
    hjf, hb.fderiv, divergence_comp_coordinateMove i hfd hg]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, zero_add,
    coordinateMoveDeriv, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, map_zero]
  dsimp only [coordinateJacobian, Function.comp_def]
  rw [← he]
  ring

end CubicTorus

namespace CubicTorus

lemma coordinateJacobian_norm_le (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) (x : Cover) :
    ‖coordinateJacobian i f t x‖ ≤ 1 + |t| * M := by
  have hd : ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ M := by
    simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (EuclideanSpace.single i 1)).trans
      (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  calc
    _ ≤ ‖(1 : ℝ)‖ + ‖t * fderiv ℝ f x (EuclideanSpace.single i 1)‖ := norm_add_le _ _
    _ ≤ 1 + |t| * M := by
      rw [norm_one, norm_mul, Real.norm_eq_abs t]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) 1

lemma coordinateJacobian_pos (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) {t : ℝ} (ht : |t| * M < 1) (x : Cover) :
    0 < coordinateJacobian i f t x := by
  have hd : |fderiv ℝ f x (EuclideanSpace.single i 1)| ≤ M := by
    simpa [Real.norm_eq_abs] using
      (ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (EuclideanSpace.single i 1)).trans
        (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  have hb := mul_le_mul_of_nonneg_left hd (abs_nonneg t)
  rw [← abs_mul] at hb
  have := (abs_le.1 hb).1
  unfold coordinateJacobian
  linarith

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
namespace CubicTorus

lemma coordinatePullback_norm_le (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) {G : Cover → Cover}
    (hG : ∀ x, ‖G x‖ ≤ 1) (x : Cover) :
    ‖coordinatePullback i f t G x‖ ≤ 1 + 2 * |t| * M := by
  have hu := hG (coordinateMove i f t x)
  have hd : ‖fderiv ℝ f x (G (coordinateMove i f t x))‖ ≤ M :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [hM x, norm_nonneg (fderiv ℝ f x)])
  calc
    _ ≤ ‖coordinateJacobian i f t x • G (coordinateMove i f t x)‖ +
        ‖(t * fderiv ℝ f x (G (coordinateMove i f t x))) • EuclideanSpace.single i 1‖ :=
      norm_sub_le _ _
    _ ≤ (1 + |t| * M) + |t| * M := by
      simp only [norm_smul, norm_mul]
      have he : ‖(EuclideanSpace.single i (1 : ℝ) : Cover)‖ = 1 := by simp
      rw [he, mul_one, Real.norm_eq_abs t]
      exact add_le_add
        (by simpa only [mul_one] using
          (mul_le_mul (coordinateJacobian_norm_le i hM t x) hu
            (norm_nonneg _) (by positivity)))
        (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    _ = _ := by ring

end CubicTorus

namespace CubicTorus

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

end CubicTorus

namespace CubicTorus

lemma realVolume_lift {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real E = volume.real (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  simp only [Measure.real_def, torusVolume,
    Measure.map_apply measurable_quotientMap hE,
    Measure.restrict_apply (measurable_quotientMap hE), inter_comm]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma inner_coordinatePullback (i : Fin 3) (f : Cover → ℝ) (t : ℝ)
    (G : Cover → Cover) (x n : Cover) :
    ⟪n, coordinatePullback i f t G x⟫ =
      ⟪coordinateCofactor i f t x n, G (coordinateMove i f t x)⟫ := by
  simp only [coordinatePullback, coordinateCofactor, inner_sub_right, real_inner_smul_right,
    inner_sub_left, real_inner_smul_left, inner_gradient_left]
  ring

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma coordinateCofactor_eq (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x n : Cover) :
    coordinateCofactor i f t x n = n + t • coordinateNormalVelocity i f x n := by
  unfold coordinateCofactor coordinateJacobian coordinateNormalVelocity
  module

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma integrableOn_directionalDeriv (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IntegrableOn (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) fundamentalCube := by
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) :=
    hf.smul contDiff_const
  have hi := integrableOn_divergence hFc
  have he : divergence (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) =
      fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1) := by
    funext x
    exact divergence_smul_const (hf.differentiable (by simp)).differentiableAt _
  rwa [he] at hi

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma coordinatePullback_smul (i : Fin 3) (f : Cover → ℝ) (t c : ℝ)
    (F : Cover → Cover) (x : Cover) :
    coordinatePullback i f t (fun y ↦ c • F y) x = c • coordinatePullback i f t F x := by
  simp only [coordinatePullback, map_smul, smul_sub, smul_smul]
  module

lemma coordinatePullback_norm_le_mul (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) {G : Cover → Cover}
    {k : ℝ} (hk : 0 < k) (hG : ∀ x, ‖G x‖ ≤ k) (x : Cover) :
    ‖coordinatePullback i f t G x‖ ≤ (1 + 2 * |t| * M) * k := by
  have hnorm : ∀ y, ‖k⁻¹ • G y‖ ≤ 1 := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hk.le)]
    exact (mul_le_mul_of_nonneg_left (hG y) (inv_nonneg.mpr hk.le)).trans_eq
      (inv_mul_cancel₀ hk.ne')
  have hh := coordinatePullback_norm_le i hM0 hM t hnorm x
  rw [coordinatePullback_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hk.le)] at hh
  calc
    _ = k * (k⁻¹ * ‖coordinatePullback i f t G x‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
    _ ≤ k * (1 + 2 * |t| * M) := mul_le_mul_of_nonneg_left hh hk.le
    _ = _ := mul_comm _ _

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus

lemma fderiv_component {F : Cover → Cover} {x : Cover} (hF : DifferentiableAt ℝ F x)
    (i : Fin 3) (v : Cover) :
    fderiv ℝ (fun y ↦ F y i) x v = fderiv ℝ F x v i := by
  have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ F y i) x = _ at hh
  rw [hh]
  rfl

lemma flux_sum_components (E : Set Torus) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) =
      ∑ i : Fin 3, directionalFlux E i (fun x ↦ F x i) := by
  unfold divergence directionalFlux
  simp_rw [← fderiv_component (hF.differentiable (by simp)).differentiableAt]
  exact integral_finsetSum _ (fun i _ ↦
    (integrableOn_directionalDeriv i ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF)).mono_set
      inter_subset_left)

lemma exists_positive_directionalFlux {E : Set Torus} (hP : 0 < perimeter E) :
    ∃ (i : Fin 3) (f : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ n x, f (x + latticeVector n) = f x) ∧ 0 < directionalFlux E i f := by
  have hh : ∃ F, AdmissibleField F ∧
      0 < ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
    by_contra! hn
    have : perimeter E ≤ 0 := iSup_le fun F ↦ iSup_le fun hF ↦ by
      exact (ENNReal.ofReal_eq_zero.2 (hn F hF)).le
    exact not_le_of_gt hP this
  obtain ⟨F, hF, hp⟩ := hh
  rw [flux_sum_components E hF.1] at hp
  have hi : ∃ i : Fin 3, 0 < directionalFlux E i (fun x ↦ F x i) := by
    by_contra! hn
    exact not_le_of_gt hp (Finset.sum_nonpos fun i _ ↦ hn i)
  obtain ⟨i, hi⟩ := hi
  refine ⟨i, fun x ↦ F x i, (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF.1, ?_, hi⟩
  intro n x
  dsimp only
  rw [hF.2.1]

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma continuous_tangentialDivergence {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (fun z : NormalBundle ↦ tangentialDivergence F z.1 z.2) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_divergence hF).comp hx).sub
    (continuous_normalUnit.inner
      (((hF.continuous_fderiv (by simp)).comp hx).clm_apply continuous_normalUnit))

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVBallCalibration
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Pointwise
namespace CubicTorus

lemma latticeVector_injective : Function.Injective latticeVector := by
  intro n m h
  funext i
  have hi := congrArg (fun x : Cover ↦ x i) h
  change (n i : ℝ)=(m i : ℝ) at hi
  exact_mod_cast hi

lemma lattice_fundamentalCube : IsAddFundamentalDomain (Fin 3 → ℤ) fundamentalCube volume := by
  apply IsAddFundamentalDomain.mk' measurableSet_fundamentalCube.nullMeasurableSet
  intro x
  obtain ⟨n,hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
  refine ⟨n,?_,?_⟩
  · change x+latticeVector n∈fundamentalCube
    rw [← hn]
    exact representative_mem_fundamentalCube _
  · intro m hm
    change x+latticeVector m∈fundamentalCube at hm
    have hq : quotientMap (x+latticeVector m)=quotientMap x := by
      rw [quotientMap_add,quotientMap_latticeVector,add_zero]
    have he : x+latticeVector m=x+latticeVector n := by
      rw [← hn,← hq,representative_quotientMap_of_mem hm]
    exact latticeVector_injective (add_left_cancel he)

lemma periodic_image_fundamental {T : Cover → Cover} (hc : Continuous T)
    (hb : Function.Bijective T)
    (hp : ∀ n x,T (x+latticeVector n)=T x+latticeVector n) :
    IsAddFundamentalDomain (Fin 3 → ℤ) (T '' fundamentalCube) volume := by
  apply IsAddFundamentalDomain.mk'
    ((hc.measurableEmbedding hb.1).measurableSet_image' measurableSet_fundamentalCube).nullMeasurableSet
  intro y
  obtain ⟨x,rfl⟩ := hb.2 y
  obtain ⟨n,hn,huniq⟩ : ∃! n : Fin 3 → ℤ,x+latticeVector n∈fundamentalCube := by
    obtain ⟨n,hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
    refine ⟨n,?_,?_⟩
    · dsimp only; rw [← hn]; exact representative_mem_fundamentalCube _
    · intro m hm
      apply latticeVector_injective
      apply add_left_cancel (a:=x)
      rw [← hn,← (show quotientMap (x+latticeVector m)=quotientMap x by
        rw [quotientMap_add,quotientMap_latticeVector,add_zero]),representative_quotientMap_of_mem hm]
  refine ⟨n,?_,?_⟩
  · change T x+latticeVector n∈T '' fundamentalCube
    exact ⟨x+latticeVector n,hn,hp n x⟩
  · intro m hm
    obtain ⟨z,hz,hzm⟩ := hm
    exact huniq m (by dsimp only; have he : z=x+latticeVector m := hb.1 (hzm.trans (hp m x).symm); rwa [← he])

lemma integral_periodic_image_cube {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] {T : Cover → Cover} (hc : Continuous T) (hb : Function.Bijective T)
    (hp : ∀ n x,T (x+latticeVector n)=T x+latticeVector n)
    {g : Cover → Y} (hg : ∀ n x,g (x+latticeVector n)=g x) :
    (∫ x in fundamentalCube,g x) = ∫ x in T '' fundamentalCube,g x :=
  lattice_fundamentalCube.setIntegral_eq (periodic_image_fundamental hc hb hp) hg

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateMove_surjective (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x,‖fderiv ℝ f x‖₊≤M)
    {t : ℝ} (ht : |t| *M<1) : Function.Surjective (coordinateMove i f t) := by
  intro y
  let g : Cover → Cover := fun x ↦ y-(t*f x) • EuclideanSpace.single i 1
  have hg : ContractingWith (‖t‖₊*M) g := by
    refine ⟨by exact_mod_cast ht, LipschitzWith.of_dist_le_mul ?_⟩
    intro x z
    have he : g x-g z=(-(t*(f x-f z))) • EuclideanSpace.single i 1 := by dsimp [g]; module
    rw [dist_eq_norm,he,norm_smul]
    simp only [norm_neg,Real.norm_eq_abs,abs_mul,PiLp.norm_single,norm_one,mul_one,
      NNReal.coe_mul,coe_nnnorm]
    calc
      |t| * |f x-f z| ≤ |t| *(M*dist x z) := by
        exact mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using
          (lipschitzWith_of_nnnorm_fderiv_le hf hM).dist_le_mul x z) (abs_nonneg t)
      _ = _ := by ring
  refine ⟨hg.fixedPoint,?_⟩
  have he := hg.fixedPoint_isFixedPt
  change y-(t*f hg.fixedPoint) • EuclideanSpace.single i 1=hg.fixedPoint at he
  exact eq_sub_iff_add_eq.mp he.symm

lemma periodicCoordinateRegion_measurable (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x,‖fderiv ℝ f x‖₊≤M)
    {t : ℝ} (ht : |t| *M<1) {E : Set Torus} (hE : MeasurableSet E) :
    MeasurableSet (periodicCoordinateRegion i f t E) := by
  have hc : Continuous (coordinateMove i f t) := continuous_id.add
    ((continuous_const.mul hf.continuous).smul continuous_const)
  exact ((hc.measurableEmbedding (coordinateMove_injective i hf hM ht)).measurableSet_image'
    (measurable_quotientMap hE)).preimage measurable_representative

lemma periodicCoordinateRegion_lift (i : Fin 3) {f : Cover → ℝ}
    (hp : ∀ n x,f (x+latticeVector n)=f x) (t : ℝ) (E : Set Torus) :
    quotientMap ⁻¹' periodicCoordinateRegion i f t E=coordinateMove i f t '' (quotientMap ⁻¹' E) := by
  ext x
  have hind : ∀ n y, (y+latticeVector n∈coordinateMove i f t '' (quotientMap ⁻¹' E)) ↔
      y∈coordinateMove i f t '' (quotientMap ⁻¹' E) := by
    intro n y
    constructor
    · rintro ⟨z,hz,he⟩
      refine ⟨z+latticeVector (-n),?_,?_⟩
      · change quotientMap (z+latticeVector (-n))∈E
        simpa only [mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hz
      · rw [coordinateMove_periodic i hp,he]
        ext j; simp [latticeVector]
    · rintro ⟨z,hz,rfl⟩
      refine ⟨z+latticeVector n,?_,coordinateMove_periodic i hp t n z⟩
      simpa only [mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hz
  change representative (quotientMap x)∈coordinateMove i f t '' (quotientMap ⁻¹' E) ↔
    x∈coordinateMove i f t '' (quotientMap ⁻¹' E)
  obtain ⟨n,hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
  rw [hn,hind]

lemma integral_periodicCoordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) (hp : ∀ n x,f (x+latticeVector n)=f x)
    {M : NNReal} (hM : ∀ x,‖fderiv ℝ f x‖₊≤M) {t : ℝ} (ht : |t| *M<1)
    {E : Set Torus} (hE : MeasurableSet E) {g : Cover → ℝ}
    (hg : ∀ n x,g (x+latticeVector n)=g x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' periodicCoordinateRegion i f t E,g x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,
        coordinateJacobian i f t x*g (coordinateMove i f t x) := by
  let S := quotientMap ⁻¹' periodicCoordinateRegion i f t E
  have hS : MeasurableSet S := measurable_quotientMap (periodicCoordinateRegion_measurable i hf hM ht hE)
  have hsp : ∀ n x,S.indicator g (x+latticeVector n)=S.indicator g x := by
    intro n x
    by_cases hx : x∈S
    · have hx' : x+latticeVector n∈S := by
        simpa only [S,mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hx
      simp only [indicator_of_mem hx,indicator_of_mem hx',hg]
    · have hx' : x+latticeVector n∉S := by
        simpa only [S,mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hx
      simp only [indicator_of_notMem hx,indicator_of_notMem hx']
  have hc : Continuous (coordinateMove i f t) := continuous_id.add
    ((continuous_const.mul hf.continuous).smul continuous_const)
  have he := integral_periodic_image_cube hc
    ⟨coordinateMove_injective i hf hM ht,coordinateMove_surjective i hf hM ht⟩
    (coordinateMove_periodic i hp t) hsp
  rw [integral_indicator hS,integral_indicator hS] at he
  simp only [Measure.restrict_restrict hS,inter_comm S] at he
  change (∫ x in fundamentalCube∩S,g x)=_
  rw [he]
  have him : coordinateMove i f t '' fundamentalCube∩S=
      coordinateMove i f t '' (fundamentalCube∩quotientMap ⁻¹' E) := by
    dsimp only [S]
    rw [periodicCoordinateRegion_lift i hp]
    exact (Set.image_inter (coordinateMove_injective i hf hM ht)).symm
  rw [him,integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_fundamentalCube.inter (measurable_quotientMap hE))
    (fun x _ ↦ (coordinateMove_hasFDerivAt i (hf x) t).hasFDerivWithinAt)
    (coordinateMove_injective i hf hM ht).injOn]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [coordinateMoveDeriv_det,abs_of_pos (coordinateJacobian_pos i
    (fun y ↦ by exact_mod_cast hM y) ht x),smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma perimeter_periodicCoordinateRegion_le (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    perimeter (periodicCoordinateRegion i f t E) ≤
      ENNReal.ofReal (1 + 2 * |t| * M) * perimeter E := by
  have hfd := hf.differentiable (by simp)
  have hC : 0 < 1 + 2 * |t| * M := by positivity
  have hMr : ∀ x, ‖fderiv ℝ f x‖ ≤ (M : ℝ) := fun x ↦ by exact_mod_cast hM x
  unfold perimeter at ⊢
  refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
  rw [integral_periodicCoordinateRegion i hfd hp hM ht hE (divergence_periodic hG.2.1)]
  have hh := abs_flux_le_mul_perimeter hP
    (coordinatePullback_contDiff i hf t hG.1) (coordinatePullback_periodic i hp t hG.2.1)
    hC (coordinatePullback_norm_le i M.coe_nonneg hMr t hG.2.2)
  simp_rw [coordinatePullback_divergence i hf t hG.1] at hh
  calc
    _ ≤ ENNReal.ofReal ((1 + 2 * |t| * M) * (perimeter E).toReal) :=
      ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hh)
    _ = _ := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hP]
      rfl

lemma finitePerimeter_periodicCoordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) : FinitePerimeter (periodicCoordinateRegion i f t E) := by
  refine ⟨(periodicCoordinateRegion_measurable i (hf.differentiable (by simp)) hM ht hE).nullMeasurableSet,
    (perimeter_periodicCoordinateRegion_le i hf hp hM ht hE hP).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP.lt_top

namespace Periodic

lemma exists_variation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x,f (x+latticeVector n)=f x) :
    ∃ a : Variation,a.coordinate=i ∧ a.function=f := by
  obtain ⟨M,hM,hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp)) (fderiv_periodic hp)
  exact ⟨⟨i,f,⟨M,hM⟩,hf,hp,fun x ↦ by exact_mod_cast hbound x⟩,rfl,rfl⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma chainBound_pos (l : VariationChain) : 0 < chainBound l := by
  induction l with
  | nil => norm_num [chainBound]
  | cons p l ih => rcases p with ⟨a,t⟩; exact mul_pos (by positivity) ih

lemma chainMove_contDiff (l : VariationChain) : ContDiff ℝ (⊤ : ℕ∞) (chainMove l) := by
  induction l with
  | nil => exact contDiff_id
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih.comp (coordinateMove_contDiff a.coordinate a.smooth t)

lemma chainJacobian_contDiff (l : VariationChain) : ContDiff ℝ (⊤ : ℕ∞) (chainJacobian l) := by
  induction l with
  | nil => exact contDiff_const
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact (coordinateJacobian_contDiff a.coordinate a.smooth t).mul
      (ih.comp (coordinateMove_contDiff a.coordinate a.smooth t))

lemma chainPullback_contDiff (l : VariationChain) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (chainPullback l F) := by
  induction l with
  | nil => exact hF
  | cons p l ih => rcases p with ⟨a,t⟩; exact coordinatePullback_contDiff a.coordinate a.smooth t ih

lemma chainPullback_periodic (l : VariationChain) {F : Cover → Cover}
    (hF : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,chainPullback l F (x+latticeVector n)=chainPullback l F x := by
  induction l with
  | nil => exact hF
  | cons p l ih => rcases p with ⟨a,t⟩; exact coordinatePullback_periodic a.coordinate a.periodic t ih

lemma chainPullback_norm (l : VariationChain) {F : Cover → Cover} (hF : ∀ x,‖F x‖≤1) :
    ∀ x,‖chainPullback l F x‖ ≤ chainBound l := by
  induction l with
  | nil => exact hF
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact coordinatePullback_norm_le_mul a.coordinate a.bound.coe_nonneg
      (fun x ↦ by exact_mod_cast a.derivative_bound x) t (chainBound_pos l) ih

lemma chainPullback_divergence (l : VariationChain) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (chainPullback l F) x = chainJacobian l x * divergence F (chainMove l x) := by
  induction l generalizing x with
  | nil => simp [chainPullback,chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainPullback,coordinatePullback_divergence a.coordinate a.smooth t (chainPullback_contDiff l hF),ih]
    simp only [chainJacobian,chainMove,mul_assoc]

lemma chain_inner_pullback (l : VariationChain) (F : Cover → Cover) (x n : Cover) :
    ⟪n,chainPullback l F x⟫=⟪chainCofactor l x n,F (chainMove l x)⟫ := by
  induction l generalizing x n with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainPullback,inner_coordinatePullback,ih]
    rfl

lemma chainRegion_measurable {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) : MeasurableSet (chainRegion l E) := by
  induction l generalizing E with
  | nil => exact hE
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact ih (fun p hp ↦ hl p (by simp [hp]))
      (periodicCoordinateRegion_measurable a.coordinate (a.smooth.differentiable (by simp))
        a.derivative_bound (hl (a,t) (by simp)) hE)

lemma chainRegion_finite {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) (hfin : perimeter E<⊤) : FinitePerimeter (chainRegion l E) := by
  induction l generalizing E with
  | nil => exact ⟨hE.nullMeasurableSet,hfin⟩
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have ht := hl (a,t) (by simp)
    exact ih (fun p hp ↦ hl p (by simp [hp]))
      (periodicCoordinateRegion_measurable a.coordinate (a.smooth.differentiable (by simp)) a.derivative_bound ht hE)
      (finitePerimeter_periodicCoordinateRegion a.coordinate a.smooth a.periodic a.derivative_bound ht hE hfin.ne).2

lemma chainMove_periodic (l : VariationChain) (n : Fin 3 → ℤ) (x : Cover) :
    chainMove l (x+latticeVector n)=chainMove l x+latticeVector n := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainMove,coordinateMove_periodic a.coordinate a.periodic,ih]
    rfl

lemma chainJacobian_periodic (l : VariationChain) (n : Fin 3 → ℤ) (x : Cover) :
    chainJacobian l (x+latticeVector n)=chainJacobian l x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    simp only [chainJacobian,coordinateMove_periodic a.coordinate a.periodic,ih,
      coordinateJacobian,fderiv_periodic a.periodic]

lemma integral_chainRegion {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) {g : Cover → ℝ}
    (hg : ∀ n x,g (x+latticeVector n)=g x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' chainRegion l E,g x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,chainJacobian l x*g (chainMove l x) := by
  induction l generalizing E with
  | nil => simp [chainRegion,chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have ht := hl (a,t) (by simp)
    rw [chainRegion,ih (fun p hp ↦ hl p (by simp [hp]))
      (periodicCoordinateRegion_measurable a.coordinate (a.smooth.differentiable (by simp)) a.derivative_bound ht hE),
      integral_periodicCoordinateRegion a.coordinate (a.smooth.differentiable (by simp))
        a.periodic a.derivative_bound ht hE (fun n x ↦ by
          rw [chainJacobian_periodic,chainMove_periodic,hg])]
    simp only [chainJacobian,chainMove,mul_assoc]

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainMass
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrableOn_fundamentalCube_of_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Cover → F} (hf : Continuous f) : IntegrableOn f fundamentalCube :=
  (hf.continuousOn.integrableOn_compact isCompact_closedFundamentalCube).mono_set
    (fun x hx ↦ ⟨WithLp.ofLp x,⟨fun i ↦ (hx i).1,fun i ↦ (hx i).2.le⟩,rfl⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma wallVelocity_contDiff (a : Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2) := by
  unfold coordinateNormalVelocity
  exact (((a.smooth.fderiv_right (by simp)).comp contDiff_fst).clm_apply contDiff_const).smul contDiff_snd |>.sub
    ((contDiff_snd.inner ℝ contDiff_const).smul ((gradient_contDiff a.smooth).comp contDiff_fst))

lemma chainCofactor_contDiff (l : VariationChain) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Cover×Cover ↦ chainCofactor l p.1 p.2) := by
  induction l with
  | nil => exact contDiff_snd
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : Cover×Cover ↦
        coordinateCofactor a.coordinate a.function t p.1 p.2) := by
      simp only [coordinateCofactor_eq]
      exact contDiff_snd.add (contDiff_const.fun_smul (wallVelocity_contDiff a))
    exact ih.comp (((coordinateMove_contDiff a.coordinate a.smooth t).comp contDiff_fst).prodMk hc)

lemma chainCofactor_continuous_normal (l : VariationChain) :
    Continuous (fun z : NormalBundle ↦ chainCofactor l z.1 z.2) :=
  (chainCofactor_contDiff l).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))

theorem perimeter_chainRegion_le_normalArea {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) : perimeter (chainRegion l E)≤ENNReal.ofReal
      (∫ z,‖chainCofactor l z.1 z.2‖ ∂(μ : Measure NormalBundle)) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  have hΓ := chainPullback_contDiff l hF.1
  have hflux := normalMeasure_flux hμ hΓ (chainPullback_periodic l hF.2.1)
    (chainBound_pos l) (chainPullback_norm l hF.2.2)
  rw [integral_chainRegion hl hE (divergence_periodic hF.2.1)]
  simp_rw [← chainPullback_divergence l hF.1]
  rw [← hflux]
  apply ENNReal.ofReal_le_ofReal
  apply integral_mono
  · exact (normalTest _ hΓ.continuous).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (chainCofactor_continuous_normal l).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover),chainPullback l F z.1⟫≤_
    rw [chain_inner_pullback]
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hF.2.2 _))

lemma chainMove_append (l k : VariationChain) (x : Cover) :
    chainMove (l++k) x=chainMove k (chainMove l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih _

lemma chainJacobian_append (l k : VariationChain) (x : Cover) :
    chainJacobian (l++k) x=chainJacobian l x*chainJacobian k (chainMove l x) := by
  induction l generalizing x with
  | nil => simp [chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    simp only [List.cons_append,chainJacobian,chainMove,ih,mul_assoc]

lemma chainCofactor_append (l k : VariationChain) (x n : Cover) :
    chainCofactor (l++k) x n=chainCofactor k (chainMove l x) (chainCofactor l x n) := by
  induction l generalizing x n with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih _ _

lemma ChainValid.append {l k : VariationChain} (hl : ChainValid l) (hk : ChainValid k) :
    ChainValid (l++k) := by
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · exact hl p hp
  · exact hk p hp

lemma volume_chainRegion {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) : torusVolume.real (chainRegion l E)=chainMass l E := by
  rw [realVolume_lift (chainRegion_measurable hl hE)]
  rw [← setIntegral_one_eq_measureReal]
  change (∫ x in fundamentalCube∩quotientMap ⁻¹' chainRegion l E,(1 : ℝ))=_
  rw [integral_chainRegion hl hE (fun _ _ ↦ rfl)]
  simp only [mul_one,chainMass]

lemma chainMass_append (l : VariationChain) (b : Variation) (s : ℝ) (E : Set Torus) :
    chainMass (l++[(b,s)]) E=chainMass l E+s*chainTransportedFlux l b E := by
  have hJ := integrableOn_fundamentalCube_of_continuous (chainJacobian_contDiff l).continuous
  have hB : IntegrableOn (fun x ↦ chainJacobian l x*
      fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)) fundamentalCube :=
    integrableOn_fundamentalCube_of_continuous
    ((chainJacobian_contDiff l).continuous.mul
      ((((b.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).comp (chainMove_contDiff l).continuous)))
  unfold chainMass chainTransportedFlux
  simp only [chainJacobian_append,chainJacobian,coordinateJacobian,mul_one]
  simp_rw [mul_add,mul_one,show ∀ x : Cover,chainJacobian l x*(s*
      fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1))=
      s*(chainJacobian l x*fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)) from fun x ↦ by ring]
  rw [integral_add (hJ.mono_set inter_subset_left) ((hB.mono_set inter_subset_left).const_mul s),integral_const_mul]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma simultaneousMove_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×Cover ↦ chainMove (simultaneousChain l p.1) p.2) := by
  induction l with
  | nil => exact contDiff_snd
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateMove a.coordinate a.function p.1 p.2) := by
      unfold coordinateMove
      exact contDiff_snd.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd)).smul contDiff_const)
    exact ih.comp (contDiff_fst.prodMk hm)

lemma simultaneousJacobian_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×Cover ↦ chainJacobian (simultaneousChain l p.1) p.2) := by
  induction l with
  | nil => exact contDiff_const
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateMove a.coordinate a.function p.1 p.2) := by
      unfold coordinateMove
      exact contDiff_snd.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd)).smul contDiff_const)
    have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateJacobian a.coordinate a.function p.1 p.2) := by
      unfold coordinateJacobian
      exact contDiff_const.add (contDiff_fst.mul (((a.smooth.fderiv_right (by simp)).comp contDiff_snd).clm_apply contDiff_const))
    exact hJ.mul (ih.comp (contDiff_fst.prodMk hm))

lemma simultaneousCofactor_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×(Cover×Cover) ↦ chainCofactor (simultaneousChain l p.1) p.2.1 p.2.2) := by
  induction l with
  | nil => exact contDiff_snd.snd
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ coordinateMove a.coordinate a.function p.1 p.2.1) := by
      unfold coordinateMove
      exact contDiff_snd.fst.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd.fst)).smul contDiff_const)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ coordinateCofactor a.coordinate a.function p.1 p.2.1 p.2.2) := by
      simp only [coordinateCofactor_eq]
      exact contDiff_snd.snd.add (contDiff_fst.fun_smul ((wallVelocity_contDiff a).comp contDiff_snd))
    exact ih.comp (contDiff_fst.prodMk (hm.prodMk hc))

@[simp] lemma simultaneousCofactor_zero (l : List Variation) (x n : Cover) :
    chainCofactor (simultaneousChain l 0) x n=n := by
  induction l generalizing x n with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainCofactor,coordinateCofactor_eq,coordinateMove] using ih x n

lemma simultaneousChain_eventually_valid (l : List Variation) :
    ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (simultaneousChain l t) := by
  induction l with
  | nil => exact Eventually.of_forall fun _ p hp ↦ by simp [simultaneousChain] at hp
  | cons a l ih =>
    have ha : ∀ᶠ t in 𝓝 (0 : ℝ),|t| *(a.bound : ℝ)<1 :=
      (continuous_abs.mul continuous_const).continuousAt.eventually (eventually_lt_nhds (by simp))
    filter_upwards [ih,ha] with t ht hat
    intro p hp
    simp only [simultaneousChain,List.map_cons,List.mem_cons] at hp
    rcases hp with rfl|hp
    · exact hat
    · exact ht p hp

@[simp] lemma simultaneousMass_zero (l : List Variation) {E : Set Torus} (hE : MeasurableSet E) :
    chainMass (simultaneousChain l 0) E=torusVolume.real E := by
  simp only [chainMass,simultaneousJacobian_zero,setIntegral_one_eq_measureReal]
  exact (realVolume_lift hE).symm

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure X} [IsFiniteMeasure μ]

omit [NormedSpace ℝ X] [SecondCountableTopology X] [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_of_continuous_compact_carrier
    [NormedSpace ℝ X] [SecondCountableTopology X] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {f : X → E} (hf : Continuous f) : Integrable f μ := by
  have h := hf.continuousOn.integrableOn_compact hK (μ := μ)
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hμ] at h

lemma hasDerivAt_compact_parameter_integral {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) :
    HasDerivAt (fun t ↦ ∫ x,F (t,x) ∂μ)
      (∫ x,fderiv ℝ F (t,x) (1,0) ∂μ) t := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (f := fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) hd.continuous.continuousOn
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Icc (t-1) (t+1)) (bound := fun _ : X ↦ M)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s ↦ (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (integrable_of_continuous_compact_carrier hK hμ (hF.continuous.comp (continuous_const.prodMk continuous_id)))
    ((hd.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (hμ.mono fun x hx s hs ↦ hM (s,x) ⟨hs,hx⟩)
    (integrable_const M) ?_).2
  exact Eventually.of_forall fun x s _ ↦
    (hF.differentiable (by simp) (s,x)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))

theorem contDiff_compact_parameter_integral {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ x,F (t,x) ∂μ) := by
  have hfinite : ∀ n : ℕ,∀ F : ℝ×X → E,ContDiff ℝ (⊤ : ℕ∞) F →
      ContDiff ℝ n (fun t ↦ ∫ x,F (t,x) ∂μ) := by
    intro n
    induction n with
    | zero =>
      intro F hF
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t ↦
        (hasDerivAt_compact_parameter_integral hK hμ hF t).continuousAt)
    | succ n ih =>
      intro F hF
      have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) :=
        (hF.fderiv_right (by simp)).clm_apply contDiff_const
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
      refine ⟨fun t ↦ (hasDerivAt_compact_parameter_integral hK hμ hF t).differentiableAt,by simp,?_⟩
      have heq : deriv (fun t ↦ ∫ x,F (t,x) ∂μ)=(fun t ↦ ∫ x,fderiv ℝ F (t,x) (1,0) ∂μ) :=
        funext fun t ↦ (hasDerivAt_compact_parameter_integral hK hμ hF t).deriv
      rw [heq]
      exact ih _ hd
  exact contDiff_infty.mpr fun n ↦ hfinite n F hF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cubeIntersection_compact_carrier (E : Set Torus) :
    ∀ᵐ x ∂(volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)),x∈closedFundamentalCube := by
  have hh := ae_restrict_mem measurableSet_fundamentalCube (μ := (volume : Measure Cover))
  have hh' := ae_restrict_of_ae_restrict_of_subset (t := fundamentalCube)
    (s := fundamentalCube∩quotientMap ⁻¹' E) inter_subset_left hh
  exact hh'.mono fun x hx ↦ ⟨WithLp.ofLp x,⟨fun i ↦ (hx i).1,fun i ↦ (hx i).2.le⟩,rfl⟩

lemma smooth_quotient_extension {f g : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (h0 : g 0≠0) :
    ∃ q : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) q ∧ q =ᶠ[𝓝 0] (fun t ↦ f t/g t) := by
  let S : Set ℝ := {t | g t≠0}
  have hS : IsOpen S := isOpen_ne.preimage hg.continuous
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds h0)
  let η : ContDiffBump (0 : ℝ) := ⟨r/4,r/2,by positivity,by linarith⟩
  have hsupp : tsupport η⊆S := by
    rw [η.tsupport_eq]
    intro t ht
    exact hsub (show dist t 0 < r from lt_of_le_of_lt ht (by change r/2 < r; linarith))
  refine ⟨fun t ↦ η t*(f t/g t),?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t∈tsupport η
    · exact η.contDiff.contDiffAt.mul (hf.contDiffAt.div hg.contDiffAt (hsupp ht))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with s hs
      simp [hs]
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) η.rIn_pos] with t ht
    rw [η.one_of_mem_closedBall (Metric.ball_subset_closedBall ht),one_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma simultaneousMass_smooth (l : List Variation) (E : Set Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ chainMass (simultaneousChain l t) E) :=
  contDiff_compact_parameter_integral isCompact_closedFundamentalCube
    (cubeIntersection_compact_carrier E) (simultaneousJacobian_smooth l)

lemma simultaneousFlux_smooth (l : List Variation) (b : Variation) (E : Set Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ chainTransportedFlux (simultaneousChain l t) b E) := by
  exact contDiff_compact_parameter_integral isCompact_closedFundamentalCube (cubeIntersection_compact_carrier E)
    (F := fun p : ℝ×Cover ↦ chainJacobian (simultaneousChain l p.1) p.2 *
      fderiv ℝ b.function (chainMove (simultaneousChain l p.1) p.2) (EuclideanSpace.single b.coordinate 1))
    ((simultaneousJacobian_smooth l).mul
    (((b.smooth.fderiv_right (by simp)).clm_apply contDiff_const).comp (simultaneousMove_smooth l)))

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothNormalLength_smooth : ContDiff ℝ (⊤ : ℕ∞) smoothNormalLength := by
  apply ((contDiff_norm_sq ℝ).add (normSmoothingBump.contDiff.comp (contDiff_norm_sq ℝ))).sqrt
  intro v
  apply ne_of_gt
  by_cases hv : v=0
  · subst v
    simp only [Function.comp_apply,norm_zero,zero_pow (by decide : 2≠0),zero_add]
    rw [normSmoothingBump.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [normSmoothingBump]))]
    norm_num
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hv)) normSmoothingBump.nonneg

lemma smoothNormalLength_eq {v : Cover} (hv : 1/2≤‖v‖) : smoothNormalLength v=‖v‖ := by
  unfold smoothNormalLength
  rw [normSmoothingBump.zero_of_le_dist,add_zero,Real.sqrt_sq (norm_nonneg _)]
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg (sq_nonneg ‖v‖)]
  change (1/4 : ℝ)≤‖v‖^2
  nlinarith

lemma normalCarrier_compact : IsCompact normalCarrier :=
  isCompact_closedFundamentalCube.prod (isCompact_sphere 0 1)

lemma normalEmbedding_mem (z : NormalBundle) : normalEmbedding z∈normalCarrier := by
  exact ⟨z.1.property,by simpa [Metric.mem_sphere,dist_zero_right,normalEmbedding] using z.2.property⟩

lemma normalMap_ae_carrier (μ : FiniteMeasure NormalBundle) :
    ∀ᵐ p ∂Measure.map normalEmbedding (μ : Measure NormalBundle),p∈normalCarrier := by
  exact (ae_map_iff normalEmbedding_continuous.measurable.aemeasurable
    (show MeasurableSet normalCarrier from normalCarrier_compact.measurableSet)).2
    (Eventually.of_forall normalEmbedding_mem)

theorem normalArea_smoothAt {C : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (h0 : ∀ p∈normalCarrier,C (0,p)=p.2)
    (μ : FiniteMeasure NormalBundle) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) 0 := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),∀ p∈normalCarrier,1/2≤‖C (t,p)‖ := by
    apply normalCarrier_compact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((hC.continuous.norm).continuousAt.eventually (eventually_gt_nhds ?_)).mono
    · intro q hq; exact hq.le
    · change 1/2<‖C (0,p)‖
      rw [h0 p hp]
      have hn : ‖p.2‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hp.2
      rw [hn]
      norm_num
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ p,smoothNormalLength (C (t,p))
      ∂Measure.map normalEmbedding (μ : Measure NormalBundle)) :=
    contDiff_compact_parameter_integral normalCarrier_compact (normalMap_ae_carrier μ)
      (smoothNormalLength_smooth.comp hC)
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hsmall] with t ht
  rw [integral_map normalEmbedding_continuous.measurable.aemeasurable]
  · apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ (smoothNormalLength_eq (ht _ (normalEmbedding_mem z))).symm
  · exact ((smoothNormalLength_smooth.comp hC).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CorrectedChain
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma correctedChainCofactor_smooth (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ×(Cover×Cover) ↦ chainCofactor (correctedChain l b γ p.1) p.2.1 p.2.2) := by
  simp only [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
  exact (simultaneousCofactor_smooth l).add ((hγ.comp contDiff_fst).fun_smul
    ((wallVelocity_contDiff b).comp
      (((simultaneousMove_smooth l).comp (contDiff_fst.prodMk contDiff_snd.fst)).prodMk
        (simultaneousCofactor_smooth l))))

lemma correctedChainArea_smoothAt (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0)
    (μ : FiniteMeasure NormalBundle) : ContDiffAt ℝ (⊤ : ℕ∞) (correctedChainArea l b γ μ) 0 := by
  apply normalArea_smoothAt (correctedChainCofactor_smooth l b hγ) ?_ μ
  intro p _
  simp [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0]

lemma correctedChainArea_zero (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ0 : γ 0=0) (μ : FiniteMeasure NormalBundle) :
    correctedChainArea l b γ μ 0=(μ.mass : ℝ) := by
  unfold correctedChainArea
  simp_rw [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0,
    zero_smul,add_zero,simultaneousCofactor_zero,fun z : NormalBundle ↦ z.2.property]
  simp only [integral_const,smul_eq_mul,mul_one]
  rfl

end Periodic
end CubicTorus

end
end

section

noncomputable section
open Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma hasDerivAt_norm_curve {f : ℝ → X} {v : X} {t : ℝ}
    (hf : HasDerivAt f v t) (h0 : f t≠0) :
    HasDerivAt (fun s ↦ ‖f s‖) (⟪f t,v⟫/‖f t‖) t := by
  have hh := hf.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hh
  convert hh using 1 <;> first | rfl | ring

lemma second_derivative_norm_curve {C : ℝ → X} (hC : ContDiff ℝ (⊤ : ℕ∞) C)
    (h0 : ‖C 0‖=1) :
    deriv (deriv (fun t ↦ ‖C t‖)) 0 = ‖deriv C 0‖^2 - ⟪C 0,deriv C 0⟫^2 +
      ⟪C 0,deriv (deriv C) 0⟫ := by
  have hn : C 0≠0 := by intro hz; rw [hz,norm_zero] at h0; norm_num at h0
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ),C t≠0 := hC.continuous.continuousAt.eventually_ne hn
  have hd := (hC.differentiable (by simp) 0).hasDerivAt
  have hd' := ((contDiff_infty_iff_deriv.mp hC).2.differentiable (by simp) 0).hasDerivAt
  have hg := hasDerivAt_norm_curve hd hn
  have heq : deriv (fun t ↦ ‖C t‖) =ᶠ[𝓝 0] (fun t ↦ ⟪C t,deriv C t⟫/‖C t‖) := by
    filter_upwards [hne] with t ht
    exact (hasDerivAt_norm_curve ((hC.differentiable (by simp) t).hasDerivAt) ht).deriv
  rw [heq.deriv_eq]
  have hh := ((hd.inner ℝ hd').fun_div hg (by rw [h0]; norm_num)).deriv
  simp only [h0,div_one,one_pow,mul_one,real_inner_self_eq_norm_sq] at hh
  rw [hh]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [IsFiniteMeasure μ]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E] in
lemma deriv_parameter_slice
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E]
    {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : X) :
    deriv (fun s ↦ F (s,x)) t=fderiv ℝ F (t,x) (1,0) :=
  ((hF.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

lemma second_deriv_parameter_slice {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : X) :
    deriv (deriv (fun s ↦ F (s,x))) t=
      fderiv ℝ (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) (t,x) (1,0) := by
  rw [show deriv (fun s ↦ F (s,x))=(fun s ↦ fderiv ℝ F (s,x) (1,0)) from
    funext fun s ↦ deriv_parameter_slice hF s x]
  exact deriv_parameter_slice ((hF.fderiv_right (by simp)).clm_apply contDiff_const) t x

lemma second_deriv_compact_parameter_integral {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) :
    deriv (deriv (fun s ↦ ∫ x,F (s,x) ∂μ)) t=
      ∫ x,deriv (deriv (fun s ↦ F (s,x))) t ∂μ := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  rw [show deriv (fun s ↦ ∫ x,F (s,x) ∂μ)=(fun s ↦ ∫ x,fderiv ℝ F (s,x) (1,0) ∂μ) from
    funext fun s ↦ (hasDerivAt_compact_parameter_integral hK hμ hF s).deriv,
    (hasDerivAt_compact_parameter_integral hK hμ hd t).deriv]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ (second_deriv_parameter_slice hF t x).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalArea_second_derivative {C : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (h0 : ∀ p∈normalCarrier,C (0,p)=p.2)
    (μ : FiniteMeasure NormalBundle) :
    deriv (deriv (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle))) 0 =
      ∫ z,‖deriv (fun t ↦ C (t,normalEmbedding z)) 0‖^2 -
        ⟪(z.2 : Cover),deriv (fun t ↦ C (t,normalEmbedding z)) 0⟫^2 +
        ⟪(z.2 : Cover),deriv (deriv (fun t ↦ C (t,normalEmbedding z))) 0⟫
        ∂(μ : Measure NormalBundle) := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),∀ p∈normalCarrier,1/2≤‖C (t,p)‖ := by
    apply normalCarrier_compact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((hC.continuous.norm).continuousAt.eventually (eventually_gt_nhds ?_)).mono
    · intro q hq; exact hq.le
    · change 1/2<‖C (0,p)‖
      rw [h0 p hp]
      have hn : ‖p.2‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hp.2
      rw [hn]
      norm_num
  let F : ℝ×(Cover×Cover) → ℝ := fun p ↦ smoothNormalLength (C p)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := smoothNormalLength_smooth.comp hC
  have heq : (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) =ᶠ[𝓝 0]
      (fun t ↦ ∫ p,F (t,p) ∂Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    filter_upwards [hsmall] with t ht
    rw [integral_map normalEmbedding_continuous.measurable.aemeasurable]
    · apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ (smoothNormalLength_eq (ht _ (normalEmbedding_mem z))).symm
    · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [heq.deriv.deriv_eq,second_deriv_compact_parameter_integral normalCarrier_compact (normalMap_ae_carrier μ) hF]
  have hm : AEStronglyMeasurable (fun p : Cover×Cover ↦ deriv (deriv (fun t ↦ F (t,p))) 0)
      (Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    simp_rw [second_deriv_parameter_slice hF]
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ fderiv ℝ F p (1,0)) :=
      (hF.fderiv_right (by simp)).clm_apply contDiff_const
    have hdd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦
        fderiv ℝ (fun q ↦ fderiv ℝ F q (1,0)) p (1,0)) :=
      (hd.fderiv_right (by simp)).clm_apply contDiff_const
    exact (hdd.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [integral_map normalEmbedding_continuous.measurable.aemeasurable hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  have hz : (fun t ↦ F (t,normalEmbedding z)) =ᶠ[𝓝 0] (fun t ↦ ‖C (t,normalEmbedding z)‖) := by
    filter_upwards [hsmall] with t ht
    exact smoothNormalLength_eq (ht _ (normalEmbedding_mem z))
  dsimp only
  rw [hz.deriv.deriv_eq]
  have hcz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ C (t,normalEmbedding z)) :=
    hC.comp (contDiff_id.prodMk contDiff_const)
  have hc0 := h0 _ (normalEmbedding_mem z)
  rw [second_derivative_norm_curve hcz (by rw [hc0]; exact z.2.property),hc0]
  rfl

end CubicTorus

end
end

section

noncomputable section
open Filter
open scoped Topology
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma deriv_smooth (f : ℝ → X) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv f) := (contDiff_infty_iff_deriv.mp hf).2

lemma deriv_smooth_add {f g : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : deriv (fun t ↦ f t+g t)=fun t ↦ deriv f t+deriv g t := by
  funext t
  exact ((hf.differentiable (by simp) t).hasDerivAt.add
    (hg.differentiable (by simp) t).hasDerivAt).deriv

lemma deriv_smooth_smul {f : ℝ → ℝ} {g : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    deriv (fun t ↦ f t • g t)=fun t ↦ deriv f t • g t+f t • deriv g t := by
  funext t
  simpa only [add_comm] using ((hf.differentiable (by simp) t).hasDerivAt.fun_smul
    (hg.differentiable (by simp) t).hasDerivAt).deriv

lemma second_deriv_zero_smul {f : ℝ → ℝ} {g : ℝ → X}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (h0 : f 0=0) (hd0 : deriv f 0=0) :
    deriv (deriv (fun t ↦ f t • g t)) 0=deriv (deriv f) 0 • g 0 := by
  rw [deriv_smooth_smul hf hg,deriv_smooth_add ((deriv_smooth f hf).fun_smul hg)
    (hf.fun_smul (deriv_smooth g hg)),deriv_smooth_smul (deriv_smooth f hf) hg,
    deriv_smooth_smul hf (deriv_smooth g hg)]
  simp [h0,hd0]

lemma correction_second_derivative {m f γ : ℝ → ℝ}
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (h0 : γ 0=0) (hf0 : f 0≠0)
    (hdm : deriv m 0=0) (hex : (fun t ↦ m t+γ t*f t) =ᶠ[𝓝 0] fun _ ↦ m 0) :
    deriv γ 0=0 ∧ deriv (deriv γ) 0*f 0= -deriv (deriv m) 0 := by
  have hd := hex.deriv_eq
  have hdprod : deriv (fun t ↦ γ t*f t) 0=deriv γ 0*f 0 := by
    simpa [h0] using ((hγ.differentiable (by simp) 0).hasDerivAt.fun_mul
      (hf.differentiable (by simp) 0).hasDerivAt).deriv
  rw [deriv_smooth_add hm (hγ.mul hf)] at hd
  dsimp only at hd
  rw [hdprod,hdm,zero_add,deriv_const] at hd
  have hdγ := (mul_eq_zero.mp hd).resolve_right hf0
  refine ⟨hdγ,?_⟩
  have hdd := hex.deriv.deriv_eq
  rw [deriv_smooth_add hm (hγ.mul hf),deriv_smooth_add (deriv_smooth m hm)
    (deriv_smooth _ (hγ.mul hf)),deriv_const',deriv_const] at hdd
  dsimp only at hdd
  have he := second_deriv_zero_smul hγ hf h0 hdγ
  simp only [smul_eq_mul] at he
  rw [he] at hdd
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalArea_second_zero_correction {C P : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (h0 : ∀ p∈normalCarrier,C (0,p)=p.2) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0) (hdγ : deriv γ 0=0)
    (μ : FiniteMeasure NormalBundle) :
    deriv (deriv (fun t ↦ ∫ z,‖C (t,normalEmbedding z)+γ t • P (t,normalEmbedding z)‖
      ∂(μ : Measure NormalBundle))) 0 =
      deriv (deriv (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle))) 0+
        deriv (deriv γ) 0*(∫ z,⟪(z.2 : Cover),P (0,normalEmbedding z)⟫ ∂(μ : Measure NormalBundle)) := by
  let D : ℝ×(Cover×Cover) → Cover := fun p ↦ C p+γ p.1 • P p
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := hC.add ((hγ.comp contDiff_fst).fun_smul hP)
  have hD0 : ∀ p∈normalCarrier,D (0,p)=p.2 := by intro p hp; simp [D,hγ0,h0 p hp]
  change deriv (deriv (fun t ↦ ∫ z,‖D (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle))) 0 = _
  rw [normalArea_second_derivative hD hD0,normalArea_second_derivative hC h0]
  have hid (z : NormalBundle) :
      deriv (fun t ↦ D (t,normalEmbedding z)) 0=deriv (fun t ↦ C (t,normalEmbedding z)) 0 := by
    have hcz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ C (t,normalEmbedding z)) :=
      hC.comp (contDiff_id.prodMk contDiff_const)
    have hpz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ P (t,normalEmbedding z)) :=
      hP.comp (contDiff_id.prodMk contDiff_const)
    change deriv (fun t ↦ C (t,normalEmbedding z)+γ t • P (t,normalEmbedding z)) 0 = _
    rw [deriv_smooth_add hcz (hγ.fun_smul hpz),deriv_smooth_smul hγ hpz]
    simp [hγ0,hdγ]
  have hidd (z : NormalBundle) :
      deriv (deriv (fun t ↦ D (t,normalEmbedding z))) 0=
        deriv (deriv (fun t ↦ C (t,normalEmbedding z))) 0+deriv (deriv γ) 0 • P (0,normalEmbedding z) := by
    have hcz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ C (t,normalEmbedding z)) :=
      hC.comp (contDiff_id.prodMk contDiff_const)
    have hpz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ P (t,normalEmbedding z)) :=
      hP.comp (contDiff_id.prodMk contDiff_const)
    change deriv (deriv (fun t ↦ C (t,normalEmbedding z)+γ t • P (t,normalEmbedding z))) 0 = _
    rw [deriv_smooth_add hcz (hγ.fun_smul hpz),
      deriv_smooth_add (deriv_smooth _ hcz) (deriv_smooth _ (hγ.fun_smul hpz))]
    dsimp only
    rw [second_deriv_zero_smul hγ hpz hγ0 hdγ]
  simp_rw [hid,hidd,inner_add_right,real_inner_smul_right,← add_assoc]
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ fderiv ℝ C p (1,0)) :=
    (hC.fderiv_right (by simp)).clm_apply contDiff_const
  have hdd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦
      fderiv ℝ (fun q ↦ fderiv ℝ C q (1,0)) p (1,0)) :=
    (hd.fderiv_right (by simp)).clm_apply contDiff_const
  have hv : Continuous (fun z : NormalBundle ↦ deriv (fun t ↦ C (t,normalEmbedding z)) 0) := by
    simp_rw [deriv_parameter_slice hC]
    exact hd.continuous.comp (continuous_const.prodMk normalEmbedding_continuous)
  have hw : Continuous (fun z : NormalBundle ↦ deriv (deriv (fun t ↦ C (t,normalEmbedding z))) 0) := by
    simp_rw [second_deriv_parameter_slice hC]
    exact hdd.continuous.comp (continuous_const.prodMk normalEmbedding_continuous)
  have hi : Integrable (fun z : NormalBundle ↦ ‖deriv (fun t ↦ C (t,normalEmbedding z)) 0‖^2-
      ⟪(z.2 : Cover),deriv (fun t ↦ C (t,normalEmbedding z)) 0⟫^2+
      ⟪(z.2 : Cover),deriv (deriv (fun t ↦ C (t,normalEmbedding z))) 0⟫) (μ : Measure NormalBundle) :=
    (((hv.norm.pow 2).sub ((continuous_normalUnit.inner hv).pow 2)).add
      (continuous_normalUnit.inner hw)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hip : Integrable (fun z : NormalBundle ↦ ⟪(z.2 : Cover),P (0,normalEmbedding z)⟫)
      (μ : Measure NormalBundle) :=
    (continuous_normalUnit.inner (hP.continuous.comp (continuous_const.prodMk normalEmbedding_continuous))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add hi (hip.const_mul _),integral_const_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalArea_first_derivative {C : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (h0 : ∀ p∈normalCarrier,C (0,p)=p.2)
    (μ : FiniteMeasure NormalBundle) :
    deriv (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) 0 =
      ∫ z,⟪(z.2 : Cover),deriv (fun t ↦ C (t,normalEmbedding z)) 0⟫
        ∂(μ : Measure NormalBundle) := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),∀ p∈normalCarrier,1/2≤‖C (t,p)‖ := by
    apply normalCarrier_compact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((hC.continuous.norm).continuousAt.eventually (eventually_gt_nhds ?_)).mono
    · intro q hq; exact hq.le
    · change 1/2<‖C (0,p)‖
      rw [h0 p hp]
      have hn : ‖p.2‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hp.2
      rw [hn]
      norm_num
  let F : ℝ×(Cover×Cover) → ℝ := fun p ↦ smoothNormalLength (C p)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := smoothNormalLength_smooth.comp hC
  have heq : (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) =ᶠ[𝓝 0]
      (fun t ↦ ∫ p,F (t,p) ∂Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    filter_upwards [hsmall] with t ht
    rw [integral_map normalEmbedding_continuous.measurable.aemeasurable]
    · apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ (smoothNormalLength_eq (ht _ (normalEmbedding_mem z))).symm
    · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [heq.deriv_eq,(hasDerivAt_compact_parameter_integral normalCarrier_compact
    (normalMap_ae_carrier μ) hF 0).deriv]
  have hm : AEStronglyMeasurable (fun p : Cover×Cover ↦ fderiv ℝ F (0,p) (1,0))
      (Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ fderiv ℝ F p (1,0)) :=
      (hF.fderiv_right (by simp)).clm_apply contDiff_const
    exact (hd.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [integral_map normalEmbedding_continuous.measurable.aemeasurable hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  have hz : (fun t ↦ F (t,normalEmbedding z)) =ᶠ[𝓝 0] (fun t ↦ ‖C (t,normalEmbedding z)‖) := by
    filter_upwards [hsmall] with t ht
    exact smoothNormalLength_eq (ht _ (normalEmbedding_mem z))
  dsimp only
  rw [← deriv_parameter_slice hF,hz.deriv_eq]
  have hcz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ C (t,normalEmbedding z)) :=
    hC.comp (contDiff_id.prodMk contDiff_const)
  have hc0 := h0 _ (normalEmbedding_mem z)
  have hn : C (0,normalEmbedding z)≠0 := by
    rw [hc0]
    exact norm_ne_zero_iff.mp (by rw [show ‖(normalEmbedding z).2‖=1 from z.2.property]; norm_num)
  rw [(hasDerivAt_norm_curve (hcz.differentiable (by simp) 0).hasDerivAt hn).deriv,hc0]
  simp only [normalEmbedding,z.2.property,div_one]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma deriv_id_smul_zero {f : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    deriv (fun t : ℝ ↦ t • f t) 0=f 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).fun_smul
    (hf.differentiable (by simp) 0).hasDerivAt).deriv

lemma second_deriv_id_smul_zero {f : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    deriv (deriv (fun t : ℝ ↦ t • f t)) 0=2 • deriv f 0 := by
  have hid : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ t) := contDiff_id
  rw [deriv_smooth_smul hid hf]
  simp only [deriv_id'',one_smul]
  rw [deriv_smooth_add hf (hid.fun_smul (deriv_smooth f hf))]
  dsimp only
  rw [deriv_id_smul_zero (deriv_smooth f hf)]
  simp only [two_smul]

lemma deriv_add_time_smul {g f : ℝ → X} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    deriv (fun t : ℝ ↦ g t+t • f t) 0=deriv g 0+f 0 := by
  simpa only [id_eq,one_smul,zero_smul,zero_add,add_zero] using
    ((hg.differentiable (by simp) 0).hasDerivAt.fun_add
      ((hasDerivAt_id (0 : ℝ)).fun_smul (hf.differentiable (by simp) 0).hasDerivAt)).deriv

namespace Periodic

lemma simultaneousMass_append (l : List Variation) (a : Variation) (E : Set Torus) (t : ℝ) :
    chainMass (simultaneousChain (l++[a]) t) E = chainMass (simultaneousChain l t) E+
      t*chainTransportedFlux (simultaneousChain l t) a E := by
  simpa only [simultaneousChain,List.map_append,List.map_cons,List.map_nil] using
    chainMass_append (simultaneousChain l t) a t E

lemma simultaneousMass_deriv (l : List Variation) (E : Set Torus) :
    deriv (fun t ↦ chainMass (simultaneousChain l t) E) 0=chainFlux l E := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainMass,chainJacobian,chainFlux]
  | append_singleton l a ih =>
    simp_rw [simultaneousMass_append l a E]
    rw [show deriv (fun t ↦ chainMass (simultaneousChain l t) E+
        t*chainTransportedFlux (simultaneousChain l t) a E) 0=
        deriv (fun t ↦ chainMass (simultaneousChain l t) E) 0+directionalFlux E a.coordinate a.function from by
      simpa only [smul_eq_mul,simultaneousFlux_zero] using
        deriv_add_time_smul (simultaneousMass_smooth l E) (simultaneousFlux_smooth l a E),ih]
    simp [chainFlux,List.map_append]

lemma simultaneousMove_deriv (l : List Variation) (x : Cover) :
    deriv (fun t ↦ chainMove (simultaneousChain l t) x) 0=chainVelocity l x := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainMove,chainVelocity]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) := (simultaneousMove_smooth l).comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ x)))
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ a.function (chainMove (simultaneousChain l t) x) • EuclideanSpace.single a.coordinate (1 : ℝ)) := (a.smooth.comp hm).fun_smul (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ (EuclideanSpace.single a.coordinate (1 : ℝ) : Cover)))
    have he : (fun t ↦ chainMove (simultaneousChain (l++[a]) t) x)=
        (fun t ↦ chainMove (simultaneousChain l t) x+
          t • (a.function (chainMove (simultaneousChain l t) x) • EuclideanSpace.single a.coordinate (1 : ℝ))) := by
      funext t
      simp [simultaneousChain,List.map_append,chainMove_append,chainMove,coordinateMove,mul_smul]
    rw [he,deriv_add_time_smul hm hf,ih,simultaneousMove_zero]
    simp [chainVelocity,List.map_append]

lemma simultaneousCofactor_deriv (l : List Variation) (x n : Cover) :
    deriv (fun t ↦ chainCofactor (simultaneousChain l t) x n) 0=chainNormalVelocity l x n := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainCofactor,chainNormalVelocity]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) := (simultaneousMove_smooth l).comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ x)))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainCofactor (simultaneousChain l t) x n) := (simultaneousCofactor_smooth l).comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ (x,n))))
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateNormalVelocity a.coordinate a.function
      (chainMove (simultaneousChain l t) x) (chainCofactor (simultaneousChain l t) x n)) :=
      (wallVelocity_contDiff a).comp (hm.prodMk hc)
    have he : (fun t ↦ chainCofactor (simultaneousChain (l++[a]) t) x n)=
        (fun t ↦ chainCofactor (simultaneousChain l t) x n+
          t • coordinateNormalVelocity a.coordinate a.function (chainMove (simultaneousChain l t) x)
            (chainCofactor (simultaneousChain l t) x n)) := by
      funext t
      simp [simultaneousChain,List.map_append,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
    rw [he,deriv_add_time_smul hc hf,ih]
    simp [chainNormalVelocity,List.map_append]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma second_deriv_add_time_smul {g f : ℝ → X} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    deriv (deriv (fun t : ℝ ↦ g t+t • f t)) 0=
      deriv (deriv g) 0+2 • deriv f 0 := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ t • f t) := contDiff_id.fun_smul hf
  rw [deriv_smooth_add hg ht,
    deriv_smooth_add (deriv_smooth g hg) (deriv_smooth _ ht)]
  dsimp only
  rw [second_deriv_id_smul_zero hf]

namespace Periodic

lemma normalJet_append (l : List Variation) (a : Variation) (x n : Cover) :
    normalJet (l++[a]) x n =
      ((normalJet l x n).1+a.function x • EuclideanSpace.single a.coordinate 1,
        (normalJet l x n).2.1+coordinateNormalVelocity a.coordinate a.function x n,
        (normalJet l x n).2.2+2 • (fderiv ℝ (fun p : Cover×Cover ↦
          coordinateNormalVelocity a.coordinate a.function p.1 p.2) (x,n)
            ((normalJet l x n).1,(normalJet l x n).2.1))) := by
  simp only [normalJet,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma normalJet_first (l : List Variation) (x n : Cover) :
    (normalJet l x n).1=chainVelocity l x ∧ (normalJet l x n).2.1=chainNormalVelocity l x n := by
  induction l using List.reverseRecOn with
  | nil => simp [normalJet,chainVelocity,chainNormalVelocity]
  | append_singleton l a ih =>
    simp only [normalJet_append]
    constructor
    · simpa [chainVelocity,List.map_append] using congrArg (fun u ↦ u+a.function x • EuclideanSpace.single a.coordinate (1 : ℝ)) ih.1
    · simpa [chainNormalVelocity,List.map_append] using congrArg (fun u ↦ u+coordinateNormalVelocity a.coordinate a.function x n) ih.2

end Periodic
end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_ComponentDivergence
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
namespace Periodic

lemma simultaneousCofactor_second_deriv (l : List Variation) (x n : Cover) :
    deriv (deriv (fun t ↦ chainCofactor (simultaneousChain l t) x n)) 0=(normalJet l x n).2.2 := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainCofactor,normalJet]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) :=
      (simultaneousMove_smooth l).comp (contDiff_id.prodMk contDiff_const)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainCofactor (simultaneousChain l t) x n) :=
      (simultaneousCofactor_smooth l).comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ (x,n))))
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateNormalVelocity a.coordinate a.function
      (chainMove (simultaneousChain l t) x) (chainCofactor (simultaneousChain l t) x n)) :=
      (wallVelocity_contDiff a).comp (hm.prodMk hc)
    have he : (fun t ↦ chainCofactor (simultaneousChain (l++[a]) t) x n)=
        (fun t ↦ chainCofactor (simultaneousChain l t) x n+
          t • coordinateNormalVelocity a.coordinate a.function (chainMove (simultaneousChain l t) x)
            (chainCofactor (simultaneousChain l t) x n)) := by
      funext t
      simp [simultaneousChain,List.map_append,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
    rw [he,second_deriv_add_time_smul hc hf,ih,normalJet_append]
    dsimp only
    congr 2
    have hdf : HasFDerivAt (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2)
        (fderiv ℝ (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2) (x,n))
        (chainMove (simultaneousChain l 0) x,chainCofactor (simultaneousChain l 0) x n) := by
      simpa only [simultaneousMove_zero,simultaneousCofactor_zero] using
        ((wallVelocity_contDiff a).differentiable (by simp) (x,n)).hasFDerivAt
    have hd := hdf.comp_hasDerivAt 0
      ((hm.differentiable (by simp) 0).hasDerivAt.prodMk (hc.differentiable (by simp) 0).hasDerivAt)
    simpa only [Function.comp_def,simultaneousMove_deriv,simultaneousCofactor_deriv,
      (normalJet_first l x n).1,(normalJet_first l x n).2] using hd.deriv

theorem simultaneousArea_second_deriv (l : List Variation) (μ : FiniteMeasure NormalBundle) :
    deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖
      ∂(μ : Measure NormalBundle))) 0 =
      ∫ z,‖chainNormalVelocity l z.1 z.2‖^2-⟪(z.2 : Cover),chainNormalVelocity l z.1 z.2⟫^2+
        ⟪(z.2 : Cover),(normalJet l z.1 z.2).2.2⟫ ∂(μ : Measure NormalBundle) := by
  have h := normalArea_second_derivative (simultaneousCofactor_smooth l)
    (by intro p _; exact simultaneousCofactor_zero l p.1 p.2) μ
  simpa only [normalEmbedding,simultaneousCofactor_deriv,simultaneousCofactor_second_deriv] using h

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma componentDivergence_smooth (a : Variation) : ContDiff ℝ (⊤ : ℕ∞) (componentDivergence a) :=
  (a.smooth.fderiv_right (by simp)).clm_apply contDiff_const

lemma massJet_append (l : List Variation) (a : Variation) (x : Cover) :
    massJet (l++[a]) x = ((massJet l x).1+a.function x • EuclideanSpace.single a.coordinate 1,
      (massJet l x).2.1+componentDivergence a x,
      (massJet l x).2.2+2*(fderiv ℝ (componentDivergence a) x (massJet l x).1+
        (massJet l x).2.1*componentDivergence a x)) := by
  simp only [massJet,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma massJet_first (l : List Variation) (x : Cover) :
    (massJet l x).1=chainVelocity l x := by
  induction l using List.reverseRecOn with
  | nil => simp [massJet,chainVelocity]
  | append_singleton l a ih =>
    simpa [massJet_append,chainVelocity,List.map_append] using
      congrArg (fun u ↦ u+a.function x • EuclideanSpace.single a.coordinate (1 : ℝ)) ih

lemma simultaneousJacobian_append (l : List Variation) (a : Variation) (x : Cover) (t : ℝ) :
    chainJacobian (simultaneousChain (l++[a]) t) x=chainJacobian (simultaneousChain l t) x+
      t*(chainJacobian (simultaneousChain l t) x*componentDivergence a (chainMove (simultaneousChain l t) x)) := by
  simp only [simultaneousChain,List.map_append,chainJacobian_append,List.map_cons,List.map_nil,
    chainJacobian,coordinateJacobian,mul_one,componentDivergence]
  ring

lemma simultaneousJacobian_deriv (l : List Variation) (x : Cover) :
    deriv (fun t ↦ chainJacobian (simultaneousChain l t) x) 0=(massJet l x).2.1 := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainJacobian,massJet]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) :=
      (simultaneousMove_smooth l).comp (contDiff_id.prodMk contDiff_const)
    have hj : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainJacobian (simultaneousChain l t) x) :=
      (simultaneousJacobian_smooth l).comp (contDiff_id.prodMk contDiff_const)
    simp_rw [simultaneousJacobian_append l a x]
    simpa [massJet_append,ih] using deriv_add_time_smul hj (hj.mul ((componentDivergence_smooth a).comp hm))

lemma simultaneousJacobian_second_deriv (l : List Variation) (x : Cover) :
    deriv (deriv (fun t ↦ chainJacobian (simultaneousChain l t) x)) 0=(massJet l x).2.2 := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainJacobian,massJet]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) :=
      (simultaneousMove_smooth l).comp (contDiff_id.prodMk contDiff_const)
    have hj : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainJacobian (simultaneousChain l t) x) :=
      (simultaneousJacobian_smooth l).comp (contDiff_id.prodMk contDiff_const)
    have hd : HasFDerivAt (componentDivergence a) (fderiv ℝ (componentDivergence a) x)
        (chainMove (simultaneousChain l 0) x) := by
      simpa only [simultaneousMove_zero] using
        ((componentDivergence_smooth a).differentiable (by simp) x).hasFDerivAt
    have hf := hd.comp_hasDerivAt 0 ((hm.differentiable (by simp) 0).hasDerivAt)
    have he := ((hj.differentiable (by simp) 0).hasDerivAt.mul hf).deriv
    simp only [Function.comp_def,simultaneousJacobian_zero,simultaneousMove_zero,
      simultaneousMove_deriv,simultaneousJacobian_deriv,one_mul] at he
    change deriv (fun t ↦ chainJacobian (simultaneousChain l t) x *
      componentDivergence a (chainMove (simultaneousChain l t) x)) 0 =
      (massJet l x).2.1*componentDivergence a x+fderiv ℝ (componentDivergence a) x (chainVelocity l x) at he
    simp_rw [simultaneousJacobian_append l a x]
    have hh := second_deriv_add_time_smul hj (hj.mul ((componentDivergence_smooth a).comp hm))
    simp only [smul_eq_mul,Function.comp_def] at hh
    rw [hh,ih,he,massJet_append]
    simp only [massJet_first]
    ring

lemma simultaneousMass_second_deriv (l : List Variation) (E : Set Torus) :
    deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,(massJet l x).2.2 := by
  simpa only [chainMass,simultaneousJacobian_second_deriv] using
    second_deriv_compact_parameter_integral isCompact_closedFundamentalCube
      (cubeIntersection_compact_carrier E) (simultaneousJacobian_smooth l) 0

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem exists_chain_of_field {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    ∃ l : List Variation,(∀ x,chainVelocity l x=F x) ∧
      (∀ E,chainFlux l E=∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x) ∧
      ∀ x n,⟪n,chainNormalVelocity l x n⟫=‖n‖^2*divergence F x-⟪n,fderiv ℝ F x n⟫ := by
  have hx (i : Fin 3) : ∃ a : Variation,a.coordinate=i ∧ a.function=(fun x ↦ F x i) :=
    exists_variation_of_function i ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF)
      (fun m x ↦ by change F (x+latticeVector m) i=F x i; rw [hp])
  choose a ha hb using hx
  refine ⟨List.ofFn a,?_,?_,?_⟩
  · intro x
    simp only [chainVelocity,List.map_ofFn,List.sum_ofFn,Function.comp_apply,ha,hb]
    ext j
    simp [Finset.sum_apply,Pi.single_apply,smul_eq_mul]
  · intro E
    simp only [chainFlux,List.map_ofFn,List.sum_ofFn,Function.comp_apply,ha,hb]
    exact (flux_sum_components E hF).symm
  · intro x n
    simp only [chainNormalVelocity,List.map_ofFn,List.sum_ofFn,Function.comp_apply,ha,hb,
      inner_sum,coordinateNormalVelocity,inner_sub_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq,inner_gradient_right,conj_trivial,
      Finset.sum_sub_distrib,← Finset.sum_mul]
    simp_rw [fderiv_component (hF.differentiable (by simp) x)]
    dsimp [divergence]
    congr 1
    · ring
    · simp [PiLp.inner_apply,EuclideanSpace.single,mul_comm]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_decompose (v : Cover) : v=∑ i : Fin 3,v i • EuclideanSpace.single i 1 := by
  ext j
  simp [Pi.single_apply]

lemma cover_clm_component (L : Cover →L[ℝ] Cover) (v : Cover) (i : Fin 3) :
    L v i=∑ j : Fin 3,v j*L (EuclideanSpace.single j 1) i := by
  change (EuclideanSpace.proj i : Cover →L[ℝ] ℝ) (L v)=_
  conv_lhs => rw [cover_decompose v,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

lemma coverTrace_comp_comm (L M : Cover →L[ℝ] Cover) :
    coverTrace (L.comp M)=coverTrace (M.comp L) := by
  simp only [coverTrace,ContinuousLinearMap.comp_apply]
  conv_lhs => enter [2,i]; rw [cover_clm_component]
  conv_rhs => enter [2,i]; rw [cover_clm_component]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coverTrace_smulRight (l : Cover →L[ℝ] ℝ) (v : Cover) :
    coverTrace (l.smulRight v)=l v := by
  conv_rhs => rw [cover_decompose v]
  simp only [coverTrace,ContinuousLinearMap.smulRight_apply,PiLp.smul_apply,
    smul_eq_mul,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma divergence_eq_coverTrace (F : Cover → Cover) (x : Cover) :
    divergence F x=coverTrace (fderiv ℝ F x) := rfl

lemma cofactorLinear_add (L M : Cover →L[ℝ] Cover) (n : Cover) :
    cofactorLinear (L+M) n=cofactorLinear L n+cofactorLinear M n := by
  simp only [cofactorLinear,coverTrace_add,map_add,add_apply]
  module

lemma cofactorQuadratic_add (L M : Cover →L[ℝ] Cover) (n : Cover) :
    cofactorQuadratic (L+M) n=cofactorQuadratic L n+cofactorQuadratic M n+
      2 • (cofactorLinear M (cofactorLinear L n)-cofactorLinear (M.comp L) n) := by
  simp only [cofactorQuadratic,cofactorLinear,coverTrace_add,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add,coverTrace_comp_comm L M,map_add,add_apply,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,map_sub,map_smul]
  module

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TranslateNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cofactorLinear_inner (L : Cover →L[ℝ] Cover) {n : Cover} (hn : ‖n‖=1) :
    ⟪n,cofactorLinear L n⟫=coverTrace L-⟪n,L n⟫ := by
  simp only [cofactorLinear,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hn,one_pow,mul_one,ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm]

lemma cofactorQuadratic_smulRight (l : Cover →L[ℝ] ℝ) (v n : Cover) :
    cofactorQuadratic (l.smulRight v) n=0 := by
  have hc : (l.smulRight v).comp (l.smulRight v)=l v • l.smulRight v := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      map_smul,smul_apply]
    module
  have ha : (l.smulRight v).adjoint ((l.smulRight v).adjoint n)=
      l v • (l.smulRight v).adjoint n := by
    have hh := congrArg (fun L : Cover →L[ℝ] Cover ↦ L.adjoint n) hc
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
      map_smul,starRingEnd_apply,star_trivial,smul_apply] using hh
  simp only [cofactorQuadratic,hc,coverTrace_smulRight,coverTrace_smul,ha]
  module

lemma cofactorLinear_coordinate {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point)
    (i : Fin 3) (n : Cover) :
    cofactorLinear (fderiv ℝ (fun y ↦ f y • EuclideanSpace.single i 1) point) n=
      coordinateNormalVelocity i f point n := by
  rw [fderiv_smul_const hf]
  have ha : ((fderiv ℝ f point).smulRight (EuclideanSpace.single i (1 : ℝ))).adjoint n=
      ⟪n,EuclideanSpace.single i 1⟫ • gradient f point := by
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.smulRight_apply,
      real_inner_smul_right,real_inner_smul_left,inner_gradient_left]
    ring
  simp only [cofactorLinear,coverTrace_smulRight,ha,coordinateNormalVelocity]

lemma cofactor_field_derivative {G : Cover → Cover} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (x n u v : Cover) :
    fderiv ℝ (fun p : Cover×Cover ↦ cofactorLinear (fderiv ℝ G p.1) p.2) (x,n) (u,v)=
      cofactorLinear (fderiv ℝ (fderiv ℝ G) x u) n+
        cofactorLinear (fderiv ℝ G x) v := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by simp)
  have hfst : HasFDerivAt (fun p : Cover×Cover ↦ p.1) (ContinuousLinearMap.fst ℝ Cover Cover) (x,n) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun p : Cover×Cover ↦ p.2) (ContinuousLinearMap.snd ℝ Cover Cover) (x,n) := hasFDerivAt_snd
  have hd := ((cofactorOperator.hasFDerivAt.comp (x,n)
    ((hg.differentiable (by simp) x).hasFDerivAt.comp (x,n) hfst)).clm_apply
      hsnd).fderiv
  change fderiv ℝ (fun p : Cover×Cover ↦ cofactorOperator (fderiv ℝ G p.1) p.2) (x,n) (u,v)=_
  simp only [Function.comp_def] at hd
  rw [hd]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,cofactorOperator_apply]
  rw [add_comm]
  rfl

lemma derivative_transport {F G : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Cover) :
    fderiv ℝ (fun y ↦ fderiv ℝ G y (F y)) x=
      fderiv ℝ (fderiv ℝ G) x (F x)+(fderiv ℝ G x).comp (fderiv ℝ F x) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by simp)
  rw [fderiv_clm_apply (hg.differentiable (by simp) x)
    (hF.differentiable (by simp) x)]
  have hs : (fderiv ℝ (fderiv ℝ G) x).flip (F x)=fderiv ℝ (fderiv ℝ G) x (F x) := by
    apply ContinuousLinearMap.ext
    intro v
    exact (hG.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) v (F x)
  rw [hs,add_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma variationField_smooth (a : Variation) : ContDiff ℝ (⊤ : ℕ∞) (variationField a) :=
  a.smooth.smul contDiff_const

lemma variationField_periodic (a : Variation) (m : Fin 3 → ℤ) (x : Cover) :
    variationField a (x+latticeVector m)=variationField a x := by
  simp only [variationField,a.periodic]

lemma chainVelocity_append (l : List Variation) (a : Variation) :
    chainVelocity (l++[a])=fun x ↦ chainVelocity l x+variationField a x := by
  funext x
  simp [chainVelocity,variationField,List.map_append]

lemma chainVelocity_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞) (chainVelocity l) := by
  induction l using List.reverseRecOn with
  | nil => exact contDiff_const
  | append_singleton l a ih => rw [chainVelocity_append]; exact ih.add (variationField_smooth a)

lemma motionJet_append (l : List Variation) (a : Variation) (x : Cover) :
    motionJet (l++[a]) x=((motionJet l x).1+variationField a x,
      (motionJet l x).2+2 • fderiv ℝ (variationField a) x (motionJet l x).1) := by
  simp only [motionJet,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma motionJet_first (l : List Variation) (x : Cover) : (motionJet l x).1=chainVelocity l x := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih => simp only [motionJet_append,chainVelocity_append,ih]

lemma motionJet_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞) (motionJet l) := by
  induction l using List.reverseRecOn with
  | nil => exact contDiff_const
  | append_singleton l a ih =>
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (variationField a)) :=
      (variationField_smooth a).fderiv_right (by simp)
    simp_rw [show motionJet (l++[a])=(fun x ↦ ((motionJet l x).1+variationField a x,
      (motionJet l x).2+2 • fderiv ℝ (variationField a) x (motionJet l x).1)) from funext (motionJet_append l a)]
    exact (ih.fst.add (variationField_smooth a)).prodMk (ih.snd.add ((hd.clm_apply ih.fst).const_smul 2))

lemma motionJet_periodic (l : List Variation) (m : Fin 3 → ℤ) (x : Cover) :
    motionJet l (x+latticeVector m)=motionJet l x := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    simp only [motionJet_append,ih,variationField_periodic,
      fderiv_periodic (variationField_periodic a)]

lemma chainNormalVelocity_eq_cofactor (l : List Variation) (x n : Cover) :
    chainNormalVelocity l x n=cofactorLinear (fderiv ℝ (chainVelocity l) x) n := by
  induction l using List.reverseRecOn with
  | nil =>
    change 0=cofactorLinear (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x) n
    simp [cofactorLinear]
  | append_singleton l a ih =>
    rw [chainVelocity_append,fderiv_fun_add ((chainVelocity_smooth l).differentiable (by simp) x)
      ((variationField_smooth a).differentiable (by simp) x),cofactorLinear_add,← ih]
    rw [show cofactorLinear (fderiv ℝ (variationField a) x) n=
      coordinateNormalVelocity a.coordinate a.function x n from
        cofactorLinear_coordinate (a.smooth.differentiable (by simp) x) a.coordinate n]
    simp [chainNormalVelocity,List.map_append]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volumeQuadratic_add (L M : Cover →L[ℝ] Cover) :
    volumeQuadratic (L+M)=volumeQuadratic L+volumeQuadratic M+
      2*(coverTrace L*coverTrace M-coverTrace (M.comp L)) := by
  simp only [volumeQuadratic,ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add,
    coverTrace_add,coverTrace_comp_comm L M]
  ring

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainAcceleration
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volumeQuadratic_smulRight (l : Cover →L[ℝ] ℝ) (v : Cover) :
    volumeQuadratic (l.smulRight v)=0 := by
  have hc : (l.smulRight v).comp (l.smulRight v)=l v • l.smulRight v := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      map_smul,smul_apply]
    module
  simp only [volumeQuadratic,hc,coverTrace_smulRight,coverTrace_smul]
  ring

lemma normal_jet_acceleration_step (D L M K : Cover →L[ℝ] Cover) (n : Cover)
    (hM : cofactorQuadratic M n=0) :
    cofactorLinear D n+cofactorQuadratic L n+
        2 • (cofactorLinear K n+cofactorLinear M (cofactorLinear L n))=
      cofactorLinear (D+2 • (K+M.comp L)) n+cofactorQuadratic (L+M) n := by
  rw [cofactorQuadratic_add,hM]
  simp only [two_smul,cofactorLinear_add]
  module

lemma mass_jet_acceleration_step (D L M K : Cover →L[ℝ] Cover)
    (hM : volumeQuadratic M=0) :
    coverTrace D+volumeQuadratic L+2*(coverTrace K+coverTrace L*coverTrace M)=
      coverTrace (D+2 • (K+M.comp L))+volumeQuadratic (L+M) := by
  rw [volumeQuadratic_add,hM]
  simp only [two_smul,coverTrace_add]
  ring

lemma divergence_smooth {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (divergence F) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  exact coverTraceCLM.contDiff.comp hd

lemma divergence_derivative {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (x v : Cover) : fderiv ℝ (divergence F) x v=coverTrace (fderiv ℝ (fderiv ℝ F) x v) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  have he := (coverTraceCLM.hasFDerivAt.comp x (hd.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ coverTraceCLM (fderiv ℝ F y)) x v=_
  simp only [Function.comp_def] at he
  rw [he]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma chainAcceleration_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞) (chainAcceleration l) :=
  (motionJet_smooth l).snd

lemma chainAcceleration_periodic (l : List Variation) (m : Fin 3 → ℤ) (x : Cover) :
    chainAcceleration l (x+latticeVector m)=chainAcceleration l x := by
  simp only [chainAcceleration,motionJet_periodic]

lemma chainAcceleration_append (l : List Variation) (a : Variation) :
    chainAcceleration (l++[a])=fun x ↦ chainAcceleration l x+
      2 • fderiv ℝ (variationField a) x (chainVelocity l x) := by
  funext x
  simp only [chainAcceleration,motionJet_append,motionJet_first]

lemma chainAcceleration_derivative_append (l : List Variation) (a : Variation) (x : Cover) :
    fderiv ℝ (chainAcceleration (l++[a])) x=fderiv ℝ (chainAcceleration l) x+
      2 • (fderiv ℝ (fderiv ℝ (variationField a)) x (chainVelocity l x)+
        (fderiv ℝ (variationField a) x).comp (fderiv ℝ (chainVelocity l) x)) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (variationField a)) :=
    (variationField_smooth a).fderiv_right (by simp)
  have ht := hd.clm_apply (chainVelocity_smooth l)
  have h2 : fderiv ℝ (fun y ↦ 2 • fderiv ℝ (variationField a) y (chainVelocity l y)) x=
      2 • fderiv ℝ (fun y ↦ fderiv ℝ (variationField a) y (chainVelocity l y)) x := by
    simp only [two_smul]
    exact fderiv_fun_add (ht.differentiable (by simp) x) (ht.differentiable (by simp) x)
  rw [chainAcceleration_append,fderiv_fun_add
    ((chainAcceleration_smooth l).differentiable (by simp) x)
    ((ht.const_smul 2).differentiable (by simp) x),
    h2,
    derivative_transport (chainVelocity_smooth l) (variationField_smooth a)]

lemma variation_normal_derivative (a : Variation) (x n u v : Cover) :
    fderiv ℝ (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2)
      (x,n) (u,v)=cofactorLinear (fderiv ℝ (fderiv ℝ (variationField a)) x u) n+
        cofactorLinear (fderiv ℝ (variationField a) x) v := by
  have he : (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2)=
      (fun p : Cover×Cover ↦ cofactorLinear (fderiv ℝ (variationField a) p.1) p.2) := by
    funext p
    exact (cofactorLinear_coordinate (a.smooth.differentiable (by simp) p.1) a.coordinate p.2).symm
  rw [he,cofactor_field_derivative (variationField_smooth a)]

lemma variation_cofactor_quadratic (a : Variation) (x n : Cover) :
    cofactorQuadratic (fderiv ℝ (variationField a) x) n=0 := by
  unfold variationField
  rw [fderiv_smul_const (a.smooth.differentiable (by simp) x)]
  exact cofactorQuadratic_smulRight _ _ _

theorem normalJet_second (l : List Variation) (x n : Cover) :
    (normalJet l x n).2.2=cofactorLinear (fderiv ℝ (chainAcceleration l) x) n+
      cofactorQuadratic (fderiv ℝ (chainVelocity l) x) n := by
  induction l using List.reverseRecOn with
  | nil =>
    change 0=cofactorLinear (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x) n+
      cofactorQuadratic (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x) n
    simp [cofactorLinear,cofactorQuadratic]
  | append_singleton l a ih =>
    rw [normalJet_append]
    dsimp only
    rw [ih,(normalJet_first l x n).1,(normalJet_first l x n).2,
      variation_normal_derivative,chainNormalVelocity_eq_cofactor,
      chainAcceleration_derivative_append,chainVelocity_append,
      fderiv_fun_add ((chainVelocity_smooth l).differentiable (by simp) x)
        ((variationField_smooth a).differentiable (by simp) x)]
    exact normal_jet_acceleration_step _ _ _ _ _ (variation_cofactor_quadratic a x n)

lemma componentDivergence_eq (a : Variation) : componentDivergence a=divergence (variationField a) := by
  funext x
  exact (divergence_smul_const (a.smooth.differentiable (by simp) x) _).symm

lemma variation_volume_quadratic (a : Variation) (x : Cover) :
    volumeQuadratic (fderiv ℝ (variationField a) x)=0 := by
  unfold variationField
  rw [fderiv_smul_const (a.smooth.differentiable (by simp) x)]
  exact volumeQuadratic_smulRight _ _

lemma massJet_divergence (l : List Variation) (x : Cover) :
    (massJet l x).2.1=coverTrace (fderiv ℝ (chainVelocity l) x) := by
  induction l using List.reverseRecOn with
  | nil =>
    change 0=coverTrace (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x)
    simp
  | append_singleton l a ih =>
    rw [massJet_append]
    dsimp only
    rw [ih,componentDivergence_eq,chainVelocity_append,
      fderiv_fun_add ((chainVelocity_smooth l).differentiable (by simp) x)
        ((variationField_smooth a).differentiable (by simp) x),coverTrace_add]
    rfl

theorem massJet_second (l : List Variation) (x : Cover) :
    (massJet l x).2.2=coverTrace (fderiv ℝ (chainAcceleration l) x)+
      volumeQuadratic (fderiv ℝ (chainVelocity l) x) := by
  induction l using List.reverseRecOn with
  | nil =>
    change 0=coverTrace (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x)+
      volumeQuadratic (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x)
    simp [volumeQuadratic]
  | append_singleton l a ih =>
    rw [massJet_append]
    dsimp only
    rw [ih,massJet_first,massJet_divergence,componentDivergence_eq,
      divergence_derivative (variationField_smooth a),divergence_eq_coverTrace,
      chainAcceleration_derivative_append,chainVelocity_append,
      fderiv_fun_add ((chainVelocity_smooth l).differentiable (by simp) x)
        ((variationField_smooth a).differentiable (by simp) x)]
    exact mass_jet_acceleration_step _ _ _ _ (variation_volume_quadratic a x)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volumeQuadratic_continuous : Continuous volumeQuadratic := by
  exact (coverTraceCLM.continuous.pow 2).sub
    (coverTraceCLM.continuous.comp (continuous_id.clm_comp continuous_id))

lemma cofactorQuadratic_continuous :
    Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ cofactorQuadratic p.1 p.2) := by
  have ht : Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ coverTrace p.1) :=
    coverTraceCLM.continuous.comp continuous_fst
  have ha : Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ p.1.adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp continuous_fst
  exact (((volumeQuadratic_continuous.comp continuous_fst).smul continuous_snd).sub
    ((continuous_const.mul ht).smul (ha.clm_apply continuous_snd))).add
      ((ha.clm_apply (ha.clm_apply continuous_snd)).const_smul 2)

lemma ambientAreaQuadratic_continuous :
    Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ ambientAreaQuadratic p.1 p.2) := by
  have hc : Continuous (fun p : (Cover →L[ℝ] Cover)×Cover ↦ cofactorLinear p.1 p.2) :=
    (cofactorOperator.continuous.comp continuous_fst).clm_apply continuous_snd
  exact ((hc.norm.pow 2).sub ((continuous_snd.inner hc).pow 2)).add
    (continuous_snd.inner cofactorQuadratic_continuous)

lemma ambientAreaQuadratic_integrable (μ : FiniteMeasure NormalBundle)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Integrable (fun z : NormalBundle ↦ ambientAreaQuadratic (fderiv ℝ F z.1) z.2)
      (μ : Measure NormalBundle) := by
  exact (ambientAreaQuadratic_continuous.comp
    (((hF.continuous_fderiv (by simp)).comp normalEmbedding_continuous.fst).prodMk
      continuous_normalUnit)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma cube_integrable_continuous (E : Set Torus) {f : Cover → ℝ} (hf : Continuous f) :
    IntegrableOn f (fundamentalCube∩quotientMap ⁻¹' E) :=
  integrable_of_continuous_compact_carrier isCompact_closedFundamentalCube
    (cubeIntersection_compact_carrier E) hf

lemma periodic_normal_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x := by
  obtain ⟨C,_,hb⟩ := periodic_bounded hF.continuous hp
  have hc : 0<C+‖F 0‖+1 := by linarith [hb 0,norm_nonneg (F 0)]
  exact normalMeasure_flux hμ hF hp hc
    (fun x ↦ (hb x).trans (by linarith [norm_nonneg (F 0)] : C≤C+‖F 0‖+1))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma chainQuadratic_eq_ambient {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (l : List Variation) :
    chainQuadratic E μ H l=ambientQuadratic E μ H (chainVelocity l) := by
  have ha := ambientAreaQuadratic_integrable μ (chainVelocity_smooth l)
  have hb : Integrable (fun z : NormalBundle ↦
      tangentialDivergence (chainAcceleration l) z.1 z.2) (μ : Measure NormalBundle) :=
    (continuous_tangentialDivergence (chainAcceleration_smooth l)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc := cube_integrable_continuous E
    (continuous_divergence (chainAcceleration_smooth l))
  have hd := cube_integrable_continuous E
    (volumeQuadratic_continuous.comp ((chainVelocity_smooth l).continuous_fderiv (by simp)))
  change IntegrableOn (fun x ↦ volumeQuadratic (fderiv ℝ (chainVelocity l) x))
    (fundamentalCube∩quotientMap ⁻¹' E) at hd
  have hn : (fun z : NormalBundle ↦
      ‖chainNormalVelocity l z.1 z.2‖^2-⟪(z.2 : Cover),chainNormalVelocity l z.1 z.2⟫^2+
      ⟪(z.2 : Cover),(normalJet l z.1 z.2).2.2⟫)=
      (fun z : NormalBundle ↦ ambientAreaQuadratic (fderiv ℝ (chainVelocity l) z.1) z.2+
        tangentialDivergence (chainAcceleration l) z.1 z.2) := by
    funext z
    rw [normalJet_second,chainNormalVelocity_eq_cofactor,inner_add_right,
      cofactorLinear_inner (fderiv ℝ (chainAcceleration l) z.1) z.2.property]
    unfold ambientAreaQuadratic tangentialDivergence
    rw [divergence_eq_coverTrace]
    ring
  have hv : (fun x ↦ (massJet l x).2.2)=
      (fun x ↦ divergence (chainAcceleration l) x+
        volumeQuadratic (fderiv ℝ (chainVelocity l) x)) := by
    funext x
    exact massJet_second l x
  have hh := hH (chainAcceleration l) (chainAcceleration_smooth l) (chainAcceleration_periodic l)
  rw [periodic_normal_flux hμ (chainAcceleration_smooth l) (chainAcceleration_periodic l)] at hh
  unfold chainQuadratic ambientQuadratic
  rw [hn,hv,integral_add ha hb,integral_add hc hd,hh]
  ring

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volumeCorrection_smooth {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (volumeCorrection F) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  exact ((divergence_smooth hF).smul hF).sub (hd.clm_apply hF)

lemma volumeCorrection_periodic {F : Cover → Cover}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (m : Fin 3 → ℤ) (x : Cover) :
    volumeCorrection F (x+latticeVector m)=volumeCorrection F x := by
  simp only [volumeCorrection,divergence_eq_coverTrace,fderiv_periodic hp,hp]

lemma divergence_volumeCorrection {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (volumeCorrection F) x=volumeQuadratic (fderiv ℝ F x) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hdiv := divergence_smooth hF
  have he := ((hdiv.differentiable (by simp) x).hasFDerivAt.smul
    (hF.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ divergence F y • F y) x = _ at he
  unfold volumeCorrection
  rw [divergence_eq_coverTrace,fderiv_fun_sub (f := fun y ↦ divergence F y • F y)
    ((hdiv.smul hF).differentiable (by simp) x)
    ((hd.clm_apply hF).differentiable (by simp) x),he,derivative_transport hF hF]
  change coverTraceCLM (_-_) = _
  rw [map_sub]
  simp only [coverTraceCLM_apply,coverTrace_add,coverTrace_smulRight,coverTrace_smul,
    divergence_derivative hF,volumeQuadratic,divergence_eq_coverTrace]
  ring

lemma volumeQuadratic_boundary {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ m x,F (x+latticeVector m)=F x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,volumeQuadratic (fderiv ℝ F x))=
      ∫ z,⟪(z.2 : Cover),volumeCorrection F z.1⟫ ∂(μ : Measure NormalBundle) := by
  rw [periodic_normal_flux hμ (volumeCorrection_smooth hF) (volumeCorrection_periodic hp)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ (divergence_volumeCorrection hF x).symm))

lemma ambientQuadratic_boundary {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (H : ℝ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ m x,F (x+latticeVector m)=F x) :
    ambientQuadratic E μ H F=
      ∫ z,ambientBoundaryQuadratic H F z.1 z.2 ∂(μ : Measure NormalBundle) := by
  have hv : Integrable (fun z : NormalBundle ↦
      H*⟪(z.2 : Cover),volumeCorrection F z.1⟫) (μ : Measure NormalBundle) :=
    (continuous_const.mul (continuous_normalUnit.inner
      ((volumeCorrection_smooth hF).continuous.comp normalEmbedding_continuous.fst))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [ambientQuadratic,volumeQuadratic_boundary hμ hF hp]
  simp only [ambientBoundaryQuadratic]
  rw [integral_sub (ambientAreaQuadratic_integrable μ hF) hv,integral_const_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma adjoint_smulRight_unit (l : Cover →L[ℝ] ℝ) {n : Cover} (hn : ‖n‖=1) :
    (l.smulRight n).adjoint n=l.adjoint 1 := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.smulRight_apply,
    real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,
    ContinuousLinearMap.adjoint_inner_left]
  simp

lemma inner_adjoint_one (l : Cover →L[ℝ] ℝ) (v : Cover) :
    ⟪l.adjoint 1,v⟫=l v := by
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

lemma coverTrace_normal_square (D : Cover →L[ℝ] Cover) (l : Cover →L[ℝ] ℝ)
    (n : Cover) (c : ℝ) :
    coverTrace ((c • D+l.smulRight n).comp (c • D+l.smulRight n))=
      c^2*coverTrace (D.comp D)+2*c*l (D n)+(l n)^2 := by
  have h1 : (l.smulRight n).comp D=(l.comp D).smulRight n := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have h2 : (l.smulRight n).comp (l.smulRight n)=l n • l.smulRight n := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      map_smul,smul_apply]
    module
  simp only [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,coverTrace_add,
    coverTrace_smul,coverTrace_comp_comm D (l.smulRight n),h1,h2,
    coverTrace_smulRight,ContinuousLinearMap.comp_apply]
  ring

lemma ambientAreaQuadratic_formula (L : Cover →L[ℝ] Cover) {n : Cover} (hn : ‖n‖=1) :
    ambientAreaQuadratic L n=‖L.adjoint n‖^2-⟪n,L.adjoint n⟫^2+
      (coverTrace L)^2-coverTrace (L.comp L)-
      2*coverTrace L*⟪n,L.adjoint n⟫+2*⟪L n,L.adjoint n⟫ := by
  unfold ambientAreaQuadratic cofactorLinear cofactorQuadratic
  rw [norm_sub_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,sq_abs,hn,one_pow,mul_one,
    inner_add_right,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,ContinuousLinearMap.adjoint_inner_right]
  simp only [map_smul,real_inner_smul_left,two_smul,inner_add_right,
    ContinuousLinearMap.adjoint_inner_right]
  ring

theorem normal_hessian_algebra (D : Cover →L[ℝ] Cover) (l : Cover →L[ℝ] ℝ)
    {n : Cover} (hn : ‖n‖=1) (hD : D.adjoint n=0) (c : ℝ) :
    ambientAreaQuadratic (c • D+l.smulRight n) n-
      coverTrace D*⟪n,coverTrace (c • D+l.smulRight n) • (c • n)-
        (c • D+l.smulRight n) (c • n)⟫=
      ‖l.adjoint 1‖^2-(l n)^2-c^2*coverTrace (D.comp D) := by
  have hd : ⟪n,D n⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,hD,inner_zero_left]
  have ha : (c • D+l.smulRight n).adjoint n=l.adjoint 1 := by
    simp only [map_add,map_smul,add_apply,smul_apply,hD,smul_zero,zero_add]
    exact adjoint_smulRight_unit l hn
  have hi : ⟪n,l.adjoint 1⟫=l n := by rw [real_inner_comm,inner_adjoint_one]
  rw [ambientAreaQuadratic_formula _ hn,ha,hi,coverTrace_normal_square]
  simp only [coverTrace_add,coverTrace_smul,coverTrace_smulRight,
    add_apply,smul_apply,map_smul,
    ContinuousLinearMap.smulRight_apply,inner_add_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    hn,one_pow,mul_one]
  have hig : ⟪D n,l.adjoint 1⟫=l (D n) :=
    (real_inner_comm _ _).trans (inner_adjoint_one l (D n))
  simp only [hig,hi,inner_add_right,real_inner_smul_right,hd,mul_zero,zero_add,
    real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_unit_normal_derivative {N : Cover → Cover} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hu : ∀ᶠ y in 𝓝 x, ‖N y‖=1) :
    (fderiv ℝ N x).adjoint (N x)=0 := by
  have he : (fun y ↦ ⟪N y,N y⟫)=ᶠ[𝓝 x](fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hu] with y hy
    rw [real_inner_self_eq_norm_sq,hy,one_pow]
  have hh := (hN.hasFDerivAt.inner ℝ hN.hasFDerivAt).fderiv
  have hz := he.fderiv_eq (𝕜 := ℝ)
  rw [hh] at hz
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun L : Cover →L[ℝ] ℝ ↦ L v) hz
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply,fderiv_const_apply,zero_apply] at hv
  rw [ContinuousLinearMap.adjoint_inner_left,inner_zero_left]
  rw [real_inner_comm (fderiv ℝ N x v) (N x)] at hv
  nlinarith [real_inner_comm (N x) (fderiv ℝ N x v)]

lemma adjoint_fderiv_one (f : Cover → ℝ) (x : Cover) :
    (fderiv ℝ f x).adjoint 1=gradient f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_adjoint_one,inner_gradient_left]

theorem normal_variation_hessian {N : Cover → Cover} {f : Cover → ℝ} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hf : DifferentiableAt ℝ f x)
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) {H : ℝ} (hH : divergence N x=H) :
    ambientBoundaryQuadratic H (fun y ↦ f y • N y) x (N x)=
      ‖gradient f x‖^2-⟪N x,gradient f x⟫^2-
        (f x)^2*coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)) := by
  have hd := (hf.hasFDerivAt.smul hN.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ f y • N y) x=_ at hd
  have hn : ‖N x‖=1 := hu.self_of_nhds
  have hg : fderiv ℝ f x (N x)=⟪N x,gradient f x⟫ := by
    rw [real_inner_comm,inner_gradient_left]
  unfold ambientBoundaryQuadratic volumeCorrection
  simp only [divergence_eq_coverTrace,hd]
  rw [← hH,divergence_eq_coverTrace,
    normal_hessian_algebra _ _ hn (smooth_unit_normal_derivative hN hu),
    adjoint_fderiv_one,hg]

lemma surface_gradient_norm {n : Cover} (hn : ‖n‖=1) (v : Cover) :
    ‖v-⟪n,v⟫ • n‖^2=‖v‖^2-⟪n,v⟫^2 := by
  rw [norm_sub_sq_real]
  simp only [real_inner_smul_right,norm_smul,Real.norm_eq_abs,hn,mul_one,sq_abs]
  rw [real_inner_comm v n]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma ambientBoundaryQuadratic_zero_of_notMem_tsupport {F : Cover → Cover}
    {x : Cover} (hx : x∉tsupport F) (H : ℝ) (n : Cover) :
    ambientBoundaryQuadratic H F x n=0 := by
  have hf : F x=0 := image_eq_zero_of_notMem_tsupport hx
  have hd : fderiv ℝ F x=0 := fderiv_of_notMem_tsupport ℝ hx
  simp [ambientBoundaryQuadratic,ambientAreaQuadratic,volumeCorrection,
    divergence_eq_coverTrace,hd,hf,cofactorLinear,cofactorQuadratic]

lemma boundaryQuadratic_eq_normalExtension {μ : FiniteMeasure NormalBundle} {H : ℝ}
    {f : Cover → ℝ} {N : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hgeom : ∀ᵐ z ∂(μ : Measure NormalBundle), z.1∈tsupport f →
      N z.1=(z.2 : Cover) ∧ (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H) :
    (∫ z,ambientBoundaryQuadratic H (fun y ↦ f y • N y) z.1 z.2 ∂(μ : Measure NormalBundle))=
      normalExtensionJacobi μ f N := by
  apply integral_congr_ae
  filter_upwards [hgeom] with z hz
  by_cases hx : (z.1 : Cover)∈tsupport f
  · obtain ⟨hn,hu,hh⟩ := hz hx
    rw [← hn,normal_variation_hessian (hN.differentiable (by simp) _) (hf.differentiable (by simp) _) hu hh,
      surface_gradient_norm (hu.self_of_nhds)]
  · have hF : (z.1 : Cover)∉tsupport (fun y ↦ f y • N y) :=
      fun h ↦ hx (tsupport_smul_subset_left f N h)
    rw [ambientBoundaryQuadratic_zero_of_notMem_tsupport hF,
      image_eq_zero_of_notMem_tsupport hx]
    have hg : gradient f z.1=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
    simp only [hg,inner_zero_right,zero_smul,sub_self,norm_zero,zero_pow (by norm_num : 2≠0),zero_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_contDiff_top {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (divergence F) := by
  exact coverTraceCLM.contDiff.comp (hF.fderiv_right (by simp))

lemma tangentialDivergence_scalar_normal {N : Cover → Cover} {f : Cover → ℝ} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hf : DifferentiableAt ℝ f x)
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) :
    tangentialDivergence (fun y ↦ f y • N y) x (N x)=f x*divergence N x := by
  have hd := (hf.hasFDerivAt.smul hN.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ f y • N y) x = _ at hd
  have hn := hu.self_of_nhds
  have hzero : ⟪N x,fderiv ℝ N x (N x)⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,smooth_unit_normal_derivative hN hu,inner_zero_left]
  unfold tangentialDivergence
  simp only [divergence_eq_coverTrace,hd,coverTrace_add,coverTrace_smul,
    coverTrace_smulRight,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,inner_add_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hn,one_pow,hzero,mul_zero,mul_one]
  ring

theorem weakCMC_normal_extension {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),divergence N z.1=H := by
  let f : Cover → ℝ := fun x ↦ divergence N x-H
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (divergence_contDiff_top hN).sub contDiff_const
  have hfp : ∀ m x,f (x+latticeVector m)=f x := by
    intro m x
    simp only [f,divergence_periodic hp]
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f x • N x) := hf.smul hN
  have hFp : ∀ m x,(fun y ↦ f y • N y) (x+latticeVector m)=f x • N x := by
    intro m x
    change f (x+latticeVector m) • N (x+latticeVector m)=_
    rw [hfp,hp]
  have h := hCMC _ hF hFp
  have hl : (∫ z,tangentialDivergence (fun x ↦ f x • N x) z.1 z.2 ∂(μ : Measure NormalBundle))=
      ∫ z,f z.1*divergence N z.1 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    filter_upwards [hn] with z hz
    rw [← hz.1,tangentialDivergence_scalar_normal
      (hN.differentiable (by simp) _) (hf.differentiable (by simp) _) hz.2]
  have hr : (∫ z,⟪(z.2 : Cover),f z.1 • N z.1⟫ ∂(μ : Measure NormalBundle))=
      ∫ z,f z.1 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    filter_upwards [hn] with z hz
    rw [hz.1,real_inner_smul_right,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
  rw [hl,hr] at h
  have hfc : Continuous (fun z : NormalBundle ↦ f z.1) := hf.continuous.comp
    (continuous_subtype_val.comp continuous_fst)
  have hdc : Continuous (fun z : NormalBundle ↦ divergence N z.1) :=
    (continuous_divergence hN).comp (continuous_subtype_val.comp continuous_fst)
  have hi : Integrable (fun z : NormalBundle ↦ f z.1*divergence N z.1) (μ : Measure NormalBundle) :=
    (hfc.mul hdc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (fun z : NormalBundle ↦ H*f z.1) (μ : Measure NormalBundle) :=
    (hfc.const_mul H).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : (∫ z,(f z.1)^2 ∂(μ : Measure NormalBundle))=0 := by
    have he : (fun z : NormalBundle ↦ (f z.1)^2)=
        (fun z ↦ f z.1*divergence N z.1-H*f z.1) := by
      funext z
      dsimp [f]
      ring
    rw [he,integral_sub hi hi',integral_const_mul,h,sub_self]
  have his : Integrable (fun z : NormalBundle ↦ (f z.1)^2) (μ : Measure NormalBundle) :=
    (hfc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z : NormalBundle ↦ sq_nonneg (f z.1))) his).mp hs
  filter_upwards [hz] with z hz
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_LatticeHeightHom
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma simultaneousArea_deriv (l : List Variation) (μ : FiniteMeasure NormalBundle) :
    deriv (simultaneousArea l μ) 0=
      ∫ z,tangentialDivergence (chainVelocity l) z.1 z.2 ∂(μ : Measure NormalBundle) := by
  have he := normalArea_first_derivative (simultaneousCofactor_smooth l)
    (by intro p _; exact simultaneousCofactor_zero l p.1 p.2) μ
  change deriv (simultaneousArea l μ) 0=_ at he
  rw [he]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ by
    change ⟪(z.2 : Cover),deriv (fun t ↦ chainCofactor (simultaneousChain l t) z.1 z.2) 0⟫=_
    rw [simultaneousCofactor_deriv,chainNormalVelocity_eq_cofactor,
      cofactorLinear_inner _ z.2.property]
    rfl

theorem normal_chain_support_jets {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) :
    ∃ l : List Variation,chainVelocity l=N ∧
      chainFlux l E=(μ.mass : ℝ) ∧
      deriv (simultaneousArea l μ) 0=H*(μ.mass : ℝ) ∧
      deriv (deriv (simultaneousArea l μ)) 0-
        H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0=
        -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle)) := by
  obtain ⟨l,hl,hflux,_⟩ := exists_chain_of_field hN hp
  have hl' : chainVelocity l=N := funext hl
  have hf : (∫ z,⟪(z.2 : Cover),N z.1⟫ ∂(μ : Measure NormalBundle))=(μ.mass : ℝ) := by
    have he : (fun z : NormalBundle ↦ ⟪(z.2 : Cover),N z.1⟫)=ᵐ[μ.toMeasure] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [hn] with z hz
      rw [hz.1,real_inner_self_eq_norm_sq,z.2.property,one_pow]
    rw [integral_congr_ae he,integral_const,smul_eq_mul,mul_one]
    rfl
  have hH := weakCMC_normal_extension hCMC hN hp hn
  have hJ : ambientQuadratic E μ H N=
      -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle)) := by
    rw [ambientQuadratic_boundary hμ H hN hp]
    have he := boundaryQuadratic_eq_normalExtension (μ := μ) (H := H)
      (f := fun _ ↦ (1 : ℝ)) contDiff_const hN (by
        filter_upwards [hn,hH] with z hz hh
        exact fun _ ↦ ⟨hz.1,hz.2,hh⟩)
    simp only [one_smul] at he
    rw [he]
    have hg (x : Cover) : gradient (fun _ : Cover ↦ (1 : ℝ)) x=0 := by simp [gradient]
    simp only [normalExtensionJacobi,hg,inner_zero_right,zero_smul,
      sub_self,norm_zero,zero_pow (by norm_num : 2≠0),one_pow,one_mul,zero_sub,integral_neg]
  refine ⟨l,hl',?_,?_,?_⟩
  · rw [hflux,← periodic_normal_flux hμ hN hp,hf]
  · rw [simultaneousArea_deriv,hl',hCMC N hN hp,hf]
  · change deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖
        ∂(μ : Measure NormalBundle))) 0-_= _
    rw [simultaneousArea_second_deriv,simultaneousMass_second_deriv]
    change chainQuadratic E μ H l=_
    rw [chainQuadratic_eq_ambient hμ hCMC,hl',hJ]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem smooth_linear_volume_correction {m f : ℝ → ℝ}
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0≠0) :
    ∃ γ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) γ ∧ γ 0=0 ∧ deriv γ 0=0 ∧
      deriv (deriv γ) 0*f 0= -deriv (deriv m) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),m t+γ t*f t=m 0+t*deriv m 0) := by
  let p := deriv m 0
  have hn : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ m 0+t*p-m t) := by fun_prop
  obtain ⟨γ,hγ,he⟩ := smooth_quotient_extension hn hf hf0
  have hγ0 : γ 0=0 := by simpa using he.self_of_nhds
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ),f t≠0 := hf.continuous.continuousAt.eventually_ne hf0
  have hx : ∀ᶠ t in 𝓝 (0 : ℝ),m t+γ t*f t=m 0+t*p := by
    filter_upwards [he,hne] with t ht hft
    rw [ht,div_mul_cancel₀ _ hft]
    ring
  let q : ℝ → ℝ := fun t ↦ m t-t*p
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := by dsimp [q]; fun_prop
  have hdq : deriv q=fun t ↦ deriv m t-p := by
    funext t
    simpa [q] using ((hm.differentiable (by simp) t).hasDerivAt.fun_sub
      ((hasDerivAt_id t).mul_const p)).deriv
  have hdq0 : deriv q 0=0 := by rw [hdq]; simp [p]
  have hddq : deriv (deriv q) 0=deriv (deriv m) 0 := by
    rw [hdq]
    exact ((deriv_smooth m hm).differentiable (by simp) 0).hasDerivAt.sub_const p |>.deriv
  have hxq : (fun t ↦ q t+γ t*f t)=ᶠ[𝓝 0] fun _ ↦ q 0 := by
    filter_upwards [hx] with t ht
    dsimp [q]
    linarith
  obtain ⟨hdγ,hddγ⟩ := correction_second_derivative hq hf hγ hγ0 hf0 hdq0 hxq
  rw [hddq] at hddγ
  exact ⟨γ,hγ,hγ0,hdγ,hddγ,hx⟩

namespace Periodic

theorem chain_linear_volume_correction (l : List Variation) (b : Variation)
    {E : Set Torus} (hE : MeasurableSet E)
    (hB : directionalFlux E b.coordinate b.function≠0) :
    ∃ γ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) γ ∧ γ 0=0 ∧ deriv γ 0=0 ∧
      deriv (deriv γ) 0*directionalFlux E b.coordinate b.function=
        -deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
        torusVolume.real (chainRegion (correctedChain l b γ t) E)=
          torusVolume.real E+t*chainFlux l E) := by
  obtain ⟨γ,hγ,hγ0,hdγ,hddγ,hx⟩ := smooth_linear_volume_correction
    (simultaneousMass_smooth l E) (simultaneousFlux_smooth l b E) (by simpa using hB)
  simp only [simultaneousFlux_zero] at hddγ
  refine ⟨γ,hγ,hγ0,hdγ,hddγ,?_⟩
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),|γ t| * (b.bound : ℝ)<1 :=
    (hγ.continuous.continuousAt.abs.mul_const _).eventually (eventually_lt_nhds (by simp [hγ0]))
  filter_upwards [simultaneousChain_eventually_valid l,hsmall,hx] with t ht hbt hxt
  have hv : ChainValid (correctedChain l b γ t) :=
    ht.append (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact hbt)
  refine ⟨hv,?_⟩
  rw [volume_chainRegion hv hE]
  change chainMass (simultaneousChain l t++[(b,γ t)]) E=_
  rw [chainMass_append,hxt,simultaneousMass_zero l hE,simultaneousMass_deriv]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma coordinateCMC_of_global {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (b : Variation) : normalFirstVariation μ b=H*directionalFlux E b.coordinate b.function := by
  have he := hCMC (variationField b) (variationField_smooth b) (variationField_periodic b)
  rw [periodic_normal_flux hμ (variationField_smooth b) (variationField_periodic b)] at he
  have hleft : normalFirstVariation μ b=
      ∫ z,tangentialDivergence (variationField b) z.1 z.2 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      change ⟪(z.2 : Cover),coordinateNormalVelocity b.coordinate b.function z.1 z.2⟫=_
      rw [← cofactorLinear_coordinate (b.smooth.differentiable (by simp) z.1),
        cofactorLinear_inner _ z.2.property]
      rfl
  rw [hleft,he]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦ divergence_smul_const (b.smooth.differentiable (by simp) x) _

lemma correctedChainArea_deriv_zero_speed (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0)
    (hdγ : deriv γ 0=0) (μ : FiniteMeasure NormalBundle) :
    deriv (correctedChainArea l b γ μ) 0=deriv (simultaneousArea l μ) 0 := by
  have hd := normalArea_first_derivative (correctedChainCofactor_smooth l b hγ)
    (by intro p _; simp [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0]) μ
  have hc := normalArea_first_derivative (simultaneousCofactor_smooth l)
    (by intro p _; simp) μ
  change deriv (correctedChainArea l b γ μ) 0=_ at hd
  change deriv (simultaneousArea l μ) 0=_ at hc
  rw [hd,hc]
  apply integral_congr_ae
  refine ae_of_all _ fun z ↦ ?_
  change ⟪(z.2 : Cover),deriv (fun t ↦ chainCofactor (correctedChain l b γ t) z.1 z.2) 0⟫=
    ⟪(z.2 : Cover),deriv (fun t ↦ chainCofactor (simultaneousChain l t) z.1 z.2) 0⟫
  congr 1
  let C : ℝ → Cover := fun t ↦ chainCofactor (simultaneousChain l t) z.1 z.2
  let P : ℝ → Cover := fun t ↦ coordinateNormalVelocity b.coordinate b.function
    (chainMove (simultaneousChain l t) z.1) (C t)
  have hC : ContDiff ℝ (⊤ : ℕ∞) C :=
    (simultaneousCofactor_smooth l).comp (contDiff_id.prodMk
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ ((z.1 : Cover),(z.2 : Cover)))))
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (wallVelocity_contDiff b).comp
    (((simultaneousMove_smooth l).comp (contDiff_id.prodMk contDiff_const)).prodMk hC)
  change deriv (fun t ↦ chainCofactor (correctedChain l b γ t) z.1 z.2) 0=deriv C 0
  have he : (fun t ↦ chainCofactor (correctedChain l b γ t) z.1 z.2)=
      (fun t ↦ C t+γ t • P t) := by
    funext t
    simp only [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
    rfl
  rw [he,deriv_smooth_add hC (hγ.fun_smul hP),deriv_smooth_smul hγ hP]
  simp [hγ0,hdγ]

lemma correctedChainArea_second_zero_speed (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0)
    (hdγ : deriv γ 0=0) (μ : FiniteMeasure NormalBundle) :
    deriv (deriv (correctedChainArea l b γ μ)) 0=
      deriv (deriv (simultaneousArea l μ)) 0+deriv (deriv γ) 0*normalFirstVariation μ b := by
  let C : ℝ×(Cover×Cover) → Cover := fun p ↦ chainCofactor (simultaneousChain l p.1) p.2.1 p.2.2
  let P : ℝ×(Cover×Cover) → Cover := fun p ↦ coordinateNormalVelocity b.coordinate b.function
    (chainMove (simultaneousChain l p.1) p.2.1) (C p)
  have hC : ContDiff ℝ (⊤ : ℕ∞) C := simultaneousCofactor_smooth l
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (wallVelocity_contDiff b).comp
    (((simultaneousMove_smooth l).comp (contDiff_fst.prodMk contDiff_snd.fst)).prodMk hC)
  have he := normalArea_second_zero_correction hC hP (by intro p _; simp [C]) hγ hγ0 hdγ μ
  have hleft : (fun t ↦ ∫ z,‖C (t,normalEmbedding z)+γ t • P (t,normalEmbedding z)‖
      ∂(μ : Measure NormalBundle))=correctedChainArea l b γ μ := by
    funext t
    simp only [correctedChainArea,correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
    rfl
  rw [hleft] at he
  change deriv (deriv (correctedChainArea l b γ μ)) 0=
    deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖ ∂(μ : Measure NormalBundle))) 0+_
  simpa [P,C,normalEmbedding,normalFirstVariation] using he

end Periodic
end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TubeCalibration
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma deriv_volume_reparam (A : ℝ → ℝ) (V P x : ℝ) :
    deriv (fun y ↦ A ((y-V)/P)) x=deriv A ((x-V)/P)/P := by
  have he : (fun y ↦ A ((y-V)/P))=(fun y ↦ A (P⁻¹*(y-V))) := by
    funext y
    congr 1
    ring
  rw [he,deriv_comp_sub_const (fun t ↦ A (P⁻¹*t)) V x,deriv_comp_mul_left]
  simp only [smul_eq_mul]
  rw [show P⁻¹*(x-V)=(x-V)/P by ring]
  ring

lemma second_deriv_volume_reparam (A : ℝ → ℝ) (V P x : ℝ) :
    deriv (deriv (fun y ↦ A ((y-V)/P)/2)) x=
      deriv (deriv A) ((x-V)/P)/P/P/2 := by
  have he : deriv (fun y ↦ A ((y-V)/P)/2)=
      (fun y ↦ deriv A ((y-V)/P)/P/2) := by
    funext y
    rw [deriv_div_const,deriv_volume_reparam]
  rw [he,deriv_div_const,deriv_div_const,deriv_volume_reparam]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem profile_hessian_of_CMC_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) :
    ∃ (N : Cover → Cover) (C : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) N ∧ (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) ∧
      Reduction.UpperSupport isoperimetricProfile C V ∧ deriv C V=H/2 ∧
      (isoperimetricProfile V)^2*deriv (deriv C) V=
        -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle))/8 := by
  obtain ⟨N,hN,hp,hn⟩ := isMinimizerAt_global_normal hV hE hmin hμ
  obtain ⟨l,_hl,hflux,harea,hsecond⟩ := normal_chain_support_jets hμ hCMC hN hp hn
  have hpos : 0<(μ.mass : ℝ) := by
    rw [hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne
  obtain ⟨i,f,hf,hpf,hfpos⟩ := exists_positive_directionalFlux
    (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1)
  obtain ⟨b,hbi,hbf⟩ := exists_variation_of_function i hf hpf
  have hB : directionalFlux E b.coordinate b.function≠0 := by simpa [hbi,hbf] using hfpos.ne'
  obtain ⟨γ,hγ,hγ0,hdγ,hddγ,hvol⟩ := chain_linear_volume_correction l b hE hB
  let A : ℝ → ℝ := correctedChainArea l b γ μ
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) A 0 := correctedChainArea_smoothAt l b hγ hγ0 μ
  have hA0 : A 0=(μ.mass : ℝ) := correctedChainArea_zero l b hγ0 μ
  have hdA : deriv A 0=H*(μ.mass : ℝ) := by
    rw [correctedChainArea_deriv_zero_speed l b hγ hγ0 hdγ μ,harea]
  have hddA : deriv (deriv A) 0=
      -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle)) := by
    rw [correctedChainArea_second_zero_speed l b hγ hγ0 hdγ μ,
      coordinateCMC_of_global hμ hCMC b]
    have he : deriv (deriv γ) 0*(H*directionalFlux E b.coordinate b.function)=
        -H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0 := by
      calc _ = H*(deriv (deriv γ) 0*directionalFlux E b.coordinate b.function) := by ring
           _ = _ := by rw [hddγ]; ring
    rw [he]
    simpa only [sub_eq_add_neg,neg_mul] using hsecond
  have habove : ∀ᶠ t in 𝓝 (0 : ℝ),isoperimetricProfile (V+t*(μ.mass : ℝ))≤A t/2 := by
    have hVI : ∀ᶠ t in 𝓝 (0 : ℝ),V+t*(μ.mass : ℝ)∈Icc 0 1 := by
      have hct : ContinuousAt (fun t : ℝ ↦ V+t*(μ.mass : ℝ)) 0 := by fun_prop
      exact hct.eventually (Icc_mem_nhds (by simpa using hV.1) (by simpa using hV.2))
    filter_upwards [hvol,hVI] with t ht hvt
    have hfin := chainRegion_finite ht.1 hE hmin.1.2
    have hve : torusVolume (chainRegion (correctedChain l b γ t) E)=
        ENNReal.ofReal (V+t*(μ.mass : ℝ)) := by
      have hv' := ht.2
      simp only [hflux,Measure.real,hmin.2.1,ENNReal.toReal_ofReal hV.1.le] at hv'
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _),hv']
    have hprofile := isoperimetricProfile_le_competitor hvt hfin hve
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (perimeter_chainRegion_le_normalArea ht.1 hE hμ)
    rw [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _)] at hreal
    exact hprofile.trans (div_le_div_of_nonneg_right hreal (by norm_num))
  let C : ℝ → ℝ := fun W ↦ A ((W-V)/(μ.mass : ℝ))/2
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun W : ℝ ↦ (W-V)/(μ.mass : ℝ)) := by fun_prop
  have hC : ContDiffAt ℝ (⊤ : ℕ∞) C V := by
    have ha : ContDiffAt ℝ (⊤ : ℕ∞) A ((V-V)/(μ.mass : ℝ)) := by simpa using hA
    exact (ha.comp V hr.contDiffAt).div_const 2
  have hCV : C V=isoperimetricProfile V := by
    simp only [C,sub_self,zero_div,hA0,hμ.1,isoperimetricProfile_eq_of_isMinimizerAt hmin]
  refine ⟨N,C,hN,hp,hn,
    ⟨hC.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)),hCV,?_⟩,?_,?_⟩
  · have ht : Tendsto (fun W : ℝ ↦ (W-V)/(μ.mass : ℝ)) (𝓝 V) (𝓝 0) := by
      simpa only [sub_self,zero_div] using hr.continuous.continuousAt.tendsto (x := V)
    filter_upwards [ht.eventually habove] with W hW
    have hi : V+(W-V)/(μ.mass : ℝ)*(μ.mass : ℝ)=W := by
      rw [div_mul_cancel₀ _ hpos.ne']; ring
    simpa only [hi,C] using hW
  · change deriv (fun W ↦ A ((W-V)/(μ.mass : ℝ))/2) V=H/2
    rw [deriv_div_const,deriv_volume_reparam,sub_self,zero_div,hdA,mul_div_cancel_right₀ _ hpos.ne']
  · rw [← hCV]
    change (A ((V-V)/(μ.mass : ℝ))/2)^2*
      deriv (deriv (fun W ↦ A ((W-V)/(μ.mass : ℝ))/2)) V=_
    rw [second_deriv_volume_reparam,sub_self,zero_div,hA0,hddA]
    field_simp [hpos.ne']
    ring

end Periodic
end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.Periodic.profile_hessian_of_CMC_oai := @OAI.CubicTorus.Periodic.profile_hessian_of_CMC_oai
