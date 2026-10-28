-- Prove2me | solution 1 for OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:54:54.693987+00:00
-- url     : https://prove2.me/submissions/ab1b7a46-07c0-4514-a776-ff40d987cb9d

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_MovingCenter_isMinimizerAt_trapped_sequential_decay
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_centered_multiplier
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_lower_density
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_upper_density

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

lemma admissible_zero : AdmissibleField (fun _ => 0) := by
  exact ⟨contDiff_const, by simp, by simp⟩

lemma divergence_zero (x : Cover) : divergence (fun _ => 0) x = 0 := by
  simp [divergence]

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

theorem finitePerimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    FinitePerimeter E ↔ FinitePerimeter F := by
  rw [FinitePerimeter, FinitePerimeter, perimeter_congr_ae hEF]
  exact and_congr ⟨fun h => h.congr hEF, fun h => h.congr hEF.symm⟩ Iff.rfl

theorem isMinimizerAt_congr_ae {E F : Set Torus} {V : ℝ}
    (hEF : E =ᵐ[torusVolume] F) : IsMinimizerAt V E ↔ IsMinimizerAt V F := by
  unfold IsMinimizerAt
  rw [finitePerimeter_congr_ae hEF, measure_congr hEF, perimeter_congr_ae hEF]

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

lemma integral_characteristic {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    (∫ x, characteristic E x ∂torusVolume) = (torusVolume E).toReal := by
  unfold characteristic
  rw [integral_indicator₀ hE, setIntegral_const]
  simp [Measure.real_def]

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

lemma admissible_translate {F : Cover → Cover} (hF : AdmissibleField F) (a : Cover) :
    AdmissibleField (fun x => F (x + a)) := by
  refine ⟨hF.1.comp (contDiff_id.add contDiff_const), ?_, fun x => hF.2.2 _⟩
  intro n x
  change F ((x + latticeVector n) + a) = F (x + a)
  rw [add_right_comm, hF.2.1]

lemma setIntegral_lift {f : Cover → ℝ} (hf : Continuous f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f (representative z) ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f x := by
  calc
    _ = ∫ x in quotientMap ⁻¹' E, f (representative (quotientMap x))
        ∂volume.restrict fundamentalCube :=
      setIntegral_map hE (hf.measurable.comp measurable_representative).aestronglyMeasurable
        measurable_quotientMap.aemeasurable
    _ = _ := by
      simp_rw [periodic_representative hp]
      rw [Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

lemma flux_translation {F : Cover → Cover} (hF : AdmissibleField F)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((fun z => z + quotientMap a) ⁻¹' E),
      divergence F x) =
    ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun y => F (y - a)) x := by
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap a) ⁻¹' E) := by
    exact (by fun_prop : Measurable (fun z : Torus => z + quotientMap a)) hE
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) hpre]
  have hG := admissible_translate hF (-a)
  have hG' : AdmissibleField (fun y => F (y - a)) := by simpa [sub_eq_add_neg] using hG
  rw [← setIntegral_lift (continuous_divergence hG'.1) (divergence_periodic hG'.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (fun y => F (y - a)) (representative (z + quotientMap a))) := by
    funext z
    simp only [sub_eq_add_neg, divergence_translate]
    have hq : quotientMap (representative (z + quotientMap a) + -a) =
        quotientMap (representative z) := by
      rw [quotientMap_add, quotientMap_representative, quotientMap_representative,
        quotientMap_neg]
      abel
    obtain ⟨n, hn⟩ := same_quotient_lattice hq
    rw [hn, divergence_periodic hF.2.1]
  rw [he]
  exact (measurePreserving_add_right torusVolume (quotientMap a)).setIntegral_preimage_emb
    (Homeomorph.addRight (quotientMap a)).measurableEmbedding
      (fun z => divergence (fun y => F (y - a)) (representative z)) E

end CubicTorus

namespace CubicTorus

lemma perimeter_translation_le {E : Set Torus} (hE : MeasurableSet E) (a : Cover) :
    perimeter ((fun z => z + quotientMap a) ⁻¹' E) ≤ perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_translation hF a hE]
  have hG : AdmissibleField (fun y => F (y - a)) := by
    simpa [sub_eq_add_neg] using admissible_translate hF (-a)
  exact le_iSup_of_le (fun y => F (y - a)) (le_iSup_of_le hG le_rfl)

lemma perimeter_translation_measurable {E : Set Torus} (hE : MeasurableSet E) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective a
  refine le_antisymm (perimeter_translation_le hE b) ?_
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap b) ⁻¹' E) :=
    (continuous_add_const _).measurable hE
  have hh := perimeter_translation_le hpre (-b)
  have he : (fun z : Torus => z + quotientMap (-b)) ⁻¹'
      ((fun z : Torus => z + quotientMap b) ⁻¹' E) = E := by
    ext z
    simp [quotientMap_neg]
  rwa [he] at hh

theorem perimeter_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (measurePreserving_add_right torusVolume a).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp, ← perimeter_congr_ae he]
  exact perimeter_translation_measurable (measurableSet_toMeasurable _ _) a

lemma volume_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    torusVolume ((fun z => z + a) ⁻¹' E) = torusVolume E :=
  (measurePreserving_add_right torusVolume a).measure_preimage hE

lemma finitePerimeter_translation {E : Set Torus} (hE : FinitePerimeter E) (a : Torus) :
    FinitePerimeter ((fun z => z + a) ⁻¹' E) := by
  refine ⟨hE.1.preimage (measurePreserving_add_right torusVolume a).quasiMeasurePreserving, ?_⟩
  rw [perimeter_translation hE.1]
  exact hE.2

theorem isMinimizerAt_translation {E : Set Torus} {V : ℝ} (hE : IsMinimizerAt V E) (a : Torus) :
    IsMinimizerAt V ((fun z => z + a) ⁻¹' E) := by
  refine ⟨finitePerimeter_translation hE.1 a, ?_, ?_⟩
  · rw [volume_translation hE.1.1, hE.2.1]
  · intro F hF hvF
    rw [perimeter_translation hE.1.1]
    exact hE.2.2 F hF hvF

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

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

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
open Filter
open scoped Topology Convolution RealInnerProductSpace

lemma characteristic_nonneg (E : Set Torus) (x : Torus) : 0 ≤ characteristic E x := by
  rcases characteristic_dichotomy E x with h | h <;> simp [h]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma gradient_const_sub (f : Cover → ℝ) (c : ℝ) (x : Cover) :
    gradient (fun y ↦ c - f y) x = -gradient f x := by
  simp only [gradient, fderiv_const_sub, map_neg]

end CubicTorus

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

lemma coordinateMove_apply (i j : Fin 3) (f : Cover → ℝ) (t : ℝ) (x : Cover) :
    coordinateMove i f t x j = x j + if i = j then t * f x else 0 := by
  by_cases h : i = j <;> simp [coordinateMove, h, eq_comm]

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

lemma fiberPoint_self (i : Fin 3) (x : Cover) : fiberPoint i x (x i) = x := by
  simp [fiberPoint]

lemma fiberPoint_apply_same (i : Fin 3) (x : Cover) (u : ℝ) : fiberPoint i x u i = u := by
  simp [fiberPoint]

lemma norm_fiberPoint_sub (i : Fin 3) (x : Cover) (u v : ℝ) :
    ‖fiberPoint i x u - fiberPoint i x v‖ = |u - v| := by
  have he : fiberPoint i x u - fiberPoint i x v =
      (u - v) • EuclideanSpace.single i 1 := by
    unfold fiberPoint
    module
  rw [he, norm_smul]
  simp

lemma coordinateMove_fiber_strictMono (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) (x : Cover) :
    StrictMono (fun u : ℝ ↦ coordinateMove i f t (fiberPoint i x u) i) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro u v huv
  have hb := hLip.norm_sub_le (fiberPoint i x v) (fiberPoint i x u)
  rw [norm_fiberPoint_sub, Real.norm_eq_abs, abs_of_pos (sub_pos.2 huv)] at hb
  have hc := mul_le_mul_of_nonneg_left hb (abs_nonneg t)
  rw [← abs_mul] at hc
  have hd := (abs_le.1 hc).1
  simp only [coordinateMove_apply, fiberPoint_apply_same, ↓reduceIte]
  nlinarith [mul_pos (sub_pos.2 ht) (sub_pos.2 huv)]

lemma coordinateMove_mapsTo_cube (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) :
    MapsTo (coordinateMove i f t) fundamentalCube fundamentalCube := by
  intro x hx j
  by_cases hij : i = j
  · subst j
    have hmono := coordinateMove_fiber_strictMono i hf hM ht x
    have hzero : coordinateMove i f t (fiberPoint i x 0) i = 0 := by
      rw [coordinateMove_apply, fiberPoint_apply_same,
        hface _ (Or.inl (fiberPoint_apply_same i x 0))]
      simp
    have hone : coordinateMove i f t (fiberPoint i x 1) i = 1 := by
      rw [coordinateMove_apply, fiberPoint_apply_same,
        hface _ (Or.inr (fiberPoint_apply_same i x 1))]
      simp
    have hlo := hmono.monotone (hx i).1
    have hhi := hmono (hx i).2
    rw [hzero, fiberPoint_self] at hlo
    dsimp only at hhi
    rw [hone, fiberPoint_self] at hhi
    exact ⟨hlo, hhi⟩
  · simpa [coordinateMove_apply, hij] using hx j

end CubicTorus

namespace CubicTorus

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

lemma measurableSet_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E) :
    MeasurableSet (coordinateRegion i f t E) := by
  have hc : Continuous (coordinateMove i f t) :=
    continuous_id.add ((continuous_const.mul hf.continuous).smul continuous_const)
  exact (hc.measurableEmbedding (coordinateMove_injective i hf hM ht)).measurableSet_image'
    (measurableSet_fundamentalCube.inter (measurable_quotientMap hE)) |>.preimage
      measurable_representative

lemma coordinateRegion_lift (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) (E : Set Torus) :
    fundamentalCube ∩ quotientMap ⁻¹' (coordinateRegion i f t E) =
      coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  ext x
  constructor
  · rintro ⟨hx, hE⟩
    change representative (quotientMap x) ∈
      coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E) at hE
    rwa [representative_quotientMap_of_mem hx] at hE
  · intro hx
    have hc : x ∈ fundamentalCube := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact coordinateMove_mapsTo_cube i hf hM hface ht hy.1
    refine ⟨hc, ?_⟩
    change representative (quotientMap x) ∈
      coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E)
    rwa [representative_quotientMap_of_mem hc]

lemma integral_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E) (g : Cover → ℝ) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (coordinateRegion i f t E), g x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        coordinateJacobian i f t x * g (coordinateMove i f t x) := by
  rw [coordinateRegion_lift i hf hM hface ht]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_fundamentalCube.inter (measurable_quotientMap hE))
    (fun x _ ↦ (coordinateMove_hasFDerivAt i (hf x) t).hasFDerivWithinAt)
    (coordinateMove_injective i hf hM ht).injOn]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [coordinateMoveDeriv_det, abs_of_pos (coordinateJacobian_pos i
    (fun y ↦ by exact_mod_cast hM y) ht x), smul_eq_mul]

lemma perimeter_coordinateRegion_le (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    perimeter (coordinateRegion i f t E) ≤
      ENNReal.ofReal (1 + 2 * |t| * M) * perimeter E := by
  have hfd := hf.differentiable (by simp)
  have hC : 0 < 1 + 2 * |t| * M := by positivity
  have hMr : ∀ x, ‖fderiv ℝ f x‖ ≤ (M : ℝ) := fun x ↦ by exact_mod_cast hM x
  unfold perimeter at ⊢
  refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
  rw [integral_coordinateRegion i hfd hM hface ht hE]
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

lemma finitePerimeter_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) : FinitePerimeter (coordinateRegion i f t E) := by
  refine ⟨(measurableSet_coordinateRegion i (hf.differentiable (by simp)) hM ht hE).nullMeasurableSet,
    (perimeter_coordinateRegion_le i hf hp hM hface ht hE hP).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP.lt_top

end CubicTorus

namespace CubicTorus

lemma realVolume_lift {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real E = volume.real (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  simp only [Measure.real_def, torusVolume,
    Measure.map_apply measurable_quotientMap hE,
    Measure.restrict_apply (measurable_quotientMap hE), inter_comm]

lemma volume_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real (coordinateRegion i f t E) = torusVolume.real E +
      t * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have hfd := hf.differentiable (by simp)
  have hi : IntegrableOn (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) fundamentalCube :=
    integrableOn_periodic_continuous
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
      (fun n x ↦ by rw [fderiv_periodic hp])
  have hv := integral_coordinateRegion i hfd hM hface ht hE (fun _ ↦ 1)
  simp only [mul_one, coordinateJacobian] at hv
  rw [integral_add (integrable_const 1) ((hi.mono_set inter_subset_left).const_mul t),
    integral_const_mul] at hv
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hv
  rw [realVolume_lift hE,
    realVolume_lift (measurableSet_coordinateRegion i hfd hM ht hE)]
  exact hv

theorem coordinate_variation (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    FinitePerimeter (coordinateRegion i f t E) ∧
    torusVolume.real (coordinateRegion i f t E) = torusVolume.real E +
      t * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f x (EuclideanSpace.single i 1) ∧
    (perimeter (coordinateRegion i f t E)).toReal ≤
      (1 + 2 * |t| * M) * (perimeter E).toReal := by
  refine ⟨finitePerimeter_coordinateRegion i hf hp hM hface ht hE hP,
    volume_coordinateRegion i hf hp hM hface ht hE, ?_⟩
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP)
    (perimeter_coordinateRegion_le i hf hp hM hface ht hE hP)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

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

lemma directionalFlux_add (E : Set Torus) (i : Fin 3) {f g : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    directionalFlux E i (fun x ↦ f x + g x) = directionalFlux E i f + directionalFlux E i g := by
  unfold directionalFlux
  change (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
    fderiv ℝ (f + g) x (EuclideanSpace.single i 1)) = _
  simp only [fderiv_add (hf.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt, add_apply]
  exact integral_add ((integrableOn_directionalDeriv i hf).mono_set inter_subset_left)
    ((integrableOn_directionalDeriv i hg).mono_set inter_subset_left)

lemma exists_wallVariation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0) :
    ∃ D : WallVariation, D.coordinate = i ∧ D.function = f := by
  obtain ⟨M, hM, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  refine ⟨⟨i, f, ⟨M, hM⟩, hf, hp, ?_, hface⟩, rfl, rfl⟩
  intro x
  exact_mod_cast hbound x

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

lemma wallCutoff_contDiff (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (wallCutoff i) := by
  unfold wallCutoff
  fun_prop

lemma wallCutoff_periodic (i : Fin 3) (n : Fin 3 → ℤ) (x : Cover) :
    wallCutoff i (x + latticeVector n) = wallCutoff i x := by
  have he : 2 * Real.pi * (x + latticeVector n) i =
      2 * Real.pi * x i + (n i : ℝ) * (2 * Real.pi) := by
    simp only [PiLp.add_apply, latticeVector]
    ring
  simp only [wallCutoff, he, Real.cos_add_int_mul_two_pi]

lemma wallCutoff_face (i : Fin 3) (x : Cover) (hx : x i = 0 ∨ x i = 1) :
    wallCutoff i x = 0 := by
  rcases hx with hx | hx <;> simp [wallCutoff, hx, Real.cos_two_pi]

lemma wallCutoff_halfShift (i : Fin 3) (x : Cover) :
    wallCutoff i (x + (1 / 2 : ℝ) • EuclideanSpace.single i 1) = 1 - wallCutoff i x := by
  have he : 2 * Real.pi * (x + (1 / 2 : ℝ) • (EuclideanSpace.single i 1 : Cover)) i =
      2 * Real.pi * x i + Real.pi := by
    simp
    ring
  rw [wallCutoff, he, Real.cos_add_pi]
  unfold wallCutoff
  ring

lemma smooth_flux_translation {F : Cover → Cover}
    (hc : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((fun z => z + quotientMap a) ⁻¹' E),
      divergence F x) =
    ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun y => F (y - a)) x := by
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap a) ⁻¹' E) :=
    (continuous_add_const _).measurable hE
  rw [← setIntegral_lift (continuous_divergence hc) (divergence_periodic hp) hpre]
  have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F (y - a)) :=
    hc.comp (contDiff_id.sub contDiff_const)
  have hGp : ∀ n x, F ((x + latticeVector n) - a) = F (x - a) := by
    intro n x
    rw [add_sub_right_comm, hp]
  rw [← setIntegral_lift (continuous_divergence hGc) (divergence_periodic hGp) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (fun y => F (y - a)) (representative (z + quotientMap a))) := by
    funext z
    simp only [sub_eq_add_neg, divergence_translate]
    have hq : quotientMap (representative (z + quotientMap a) + -a) =
        quotientMap (representative z) := by
      rw [quotientMap_add, quotientMap_representative, quotientMap_representative,
        quotientMap_neg]
      abel
    obtain ⟨n, hn⟩ := same_quotient_lattice hq
    rw [hn, divergence_periodic hp]
  rw [he]
  exact (measurePreserving_add_right torusVolume (quotientMap a)).setIntegral_preimage_emb
    (Homeomorph.addRight (quotientMap a)).measurableEmbedding
      (fun z => divergence (fun y => F (y - a)) (representative z)) E

lemma directionalFlux_translation (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x, f (x + latticeVector n) = f x)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) i (fun x ↦ f (x + a)) =
      directionalFlux E i f := by
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f (x + a) • (EuclideanSpace.single i 1 : Cover)) :=
    (hf.comp (contDiff_id.add contDiff_const)).smul contDiff_const
  have hFp : ∀ n x, f ((x + latticeVector n) + a) • (EuclideanSpace.single i 1 : Cover) =
      f (x + a) • EuclideanSpace.single i 1 := by
    intro n x
    rw [add_right_comm, hp]
  have hh := smooth_flux_translation hFc hFp a hE
  simp only [sub_add_cancel] at hh
  simp_rw [divergence_smul_const (hf.differentiable (by simp)).differentiableAt] at hh
  unfold directionalFlux
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (divergence_smul_const
    ((hf.comp (contDiff_id.add contDiff_const)).differentiable (by simp)).differentiableAt
    (EuclideanSpace.single i 1)).symm

theorem exists_positive_wallVariation {E : Set Torus} (hE : MeasurableSet E)
    (hP : 0 < perimeter E) :
    ∃ (a : Cover) (D : WallVariation),
      0 < directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) D.coordinate D.function := by
  obtain ⟨i, f, hf, hp, hflux⟩ := exists_positive_directionalFlux hP
  let f₀ : Cover → ℝ := fun x ↦ wallCutoff i x * f x
  let f₁ : Cover → ℝ := fun x ↦ (1 - wallCutoff i x) * f x
  have hc₀ : ContDiff ℝ (⊤ : ℕ∞) f₀ := (wallCutoff_contDiff i).mul hf
  have hc₁ : ContDiff ℝ (⊤ : ℕ∞) f₁ := (contDiff_const.sub (wallCutoff_contDiff i)).mul hf
  have hp₀ : ∀ n x, f₀ (x + latticeVector n) = f₀ x := by
    intro n x
    dsimp only [f₀]
    rw [wallCutoff_periodic, hp]
  have hp₁ : ∀ n x, f₁ (x + latticeVector n) = f₁ x := by
    intro n x
    dsimp only [f₁]
    rw [wallCutoff_periodic, hp]
  have he : (fun x ↦ f₀ x + f₁ x) = f := by
    funext x
    dsimp only [f₀, f₁]
    ring
  have hs : 0 < directionalFlux E i f₀ + directionalFlux E i f₁ := by
    rw [← directionalFlux_add E i hc₀ hc₁, he]
    exact hflux
  by_cases hpos : 0 < directionalFlux E i f₀
  · have hface₀ : ∀ x, x i = 0 ∨ x i = 1 → f₀ x = 0 := by
      intro x hx
      simp [f₀, wallCutoff_face i x hx]
    obtain ⟨D, hi, hfD⟩ := exists_wallVariation_of_function i hc₀ hp₀ hface₀
    refine ⟨0, D, ?_⟩
    have hz : quotientMap 0 = 0 := by ext j; simp [quotientMap]
    simpa only [hi, hfD, hz, add_zero, preimage_id'] using hpos
  · have hpos₁ : 0 < directionalFlux E i f₁ := by linarith
    let a : Cover := (1 / 2 : ℝ) • EuclideanSpace.single i 1
    let g : Cover → ℝ := fun x ↦ f₁ (x + a)
    have hgc : ContDiff ℝ (⊤ : ℕ∞) g := hc₁.comp (contDiff_id.add contDiff_const)
    have hgp : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp only [g]
      rw [add_right_comm, hp₁]
    have hgf : ∀ x, x i = 0 ∨ x i = 1 → g x = 0 := by
      intro x hx
      dsimp only [g, f₁, a]
      rw [wallCutoff_halfShift, wallCutoff_face i x hx]
      ring
    obtain ⟨D, hi, hfD⟩ := exists_wallVariation_of_function i hgc hgp hgf
    refine ⟨a, D, ?_⟩
    rw [hi, hfD]
    change 0 < directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) i (fun x ↦ f₁ (x + a))
    rwa [directionalFlux_translation i hc₁ hp₁ a hE]

end CubicTorus

namespace CubicTorus

lemma translate_not_mem_tsupport {Y : Type*} [Zero Y] {f : Cover → Y}
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    x + latticeVector n ∉ tsupport f := by
  intro h
  apply hn
  ext i
  have hi := hs h i
  simp only [PiLp.add_apply, latticeVector] at hi
  have hlo : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).2]
  have hhi : (n i : ℝ) < 1 := by linarith [(hx i).1]
  have hνlo : (-1 : ℤ) < n i := by exact_mod_cast hlo
  have hνhi : n i < (1 : ℤ) := by exact_mod_cast hhi
  change n i = 0
  omega

lemma latticePeriodize_eventuallyEq {Y : Type*} [NormedAddCommGroup Y]
    {f : Cover → Y} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    latticePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s, hlocal⟩ := finite_lattice_support_near hc x
  have hz (n : Fin 3 → ℤ) (hn : n ≠ 0) :
      ∀ᶠ y in 𝓝 x, f (y + latticeVector n) = 0 := by
    have h := notMem_tsupport_iff_eventuallyEq.mp (translate_not_mem_tsupport hs hx hn)
    exact h.comp_tendsto (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x, ∀ n ∈ s, n ≠ 0 → f (y + latticeVector n) = 0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n = 0
    · exact Eventually.of_forall fun y h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun y h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1), hfin] with y hy hz
  unfold latticePeriodize
  rw [tsum_eq_single (0 : Fin 3 → ℤ)]
  · simp only [latticeVector_zero, add_zero]
  · intro n hn
    by_cases hs : n ∈ s
    · exact hz n hs hn
    · exact hlocal y hy n hs

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma compactCell_coordinates (z : CompactCell) (i : Fin 3) :
    0 ≤ (z : Cover) i ∧ (z : Cover) i ≤ 1 := by
  obtain ⟨x, hx, he⟩ := z.property
  rw [← he]
  exact ⟨hx.1 i, hx.2 i⟩

end CubicTorus

namespace CubicTorus

lemma measurableSet_coordinateBox (r : ℝ) : MeasurableSet (coordinateBox r) := by
  simp only [coordinateBox, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_lt (measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))) measurable_const

lemma coordinateBox_lift_preimage {r : ℝ} (hr : r ∈ Icc 0 1) :
    (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹'
      (fundamentalCube ∩ quotientMap ⁻¹' coordinateBox r) =
      univ.pi (fun _ : Fin 3 ↦ Ico 0 r) := by
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i < 1) ∧
    (∀ i, ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) < r)) ↔ _
  constructor
  · rintro ⟨hc, hs⟩ i _
    have he : ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i :=
      AddCircle.equivIco_coe_of_mem (by simpa using hc i)
    exact ⟨(hc i).1, he ▸ hs i⟩
  · intro hx
    have hc : ∀ i, 0 ≤ x i ∧ x i < 1 := fun i ↦
      ⟨(hx i (mem_univ i)).1, (hx i (mem_univ i)).2.trans_le hr.2⟩
    refine ⟨hc, fun i ↦ ?_⟩
    rw [AddCircle.equivIco_coe_of_mem (by simpa using hc i)]
    exact (hx i (mem_univ i)).2

lemma volume_coordinateBox {r : ℝ} (hr : r ∈ Icc 0 1) :
    torusVolume (coordinateBox r) = ENNReal.ofReal (r ^ 3) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_coordinateBox r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_coordinateBox r)), inter_comm]
  have hm := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    ((measurableSet_fundamentalCube.inter
      (measurable_quotientMap (measurableSet_coordinateBox r))).nullMeasurableSet)
  rw [coordinateBox_lift_preimage hr] at hm
  rw [← hm, Real.volume_pi_Ico]
  simp [← ENNReal.ofReal_pow hr.1, Finset.prod_const]

end CubicTorus

namespace CubicTorus
open Filter

lemma representative_norm_le_box {r : ℝ} (hr : 0 ≤ r) {x : Torus}
    (hx : x ∈ coordinateBox r) : ‖representative x‖ ≤ 3 * r := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have hb (i : Fin 3) : ‖(representative x).ofLp i‖ ^ 2 ≤ r ^ 2 := by
    have h0 := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).2.1
    have h1 := hx i
    change ‖((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ)‖ ^ 2 ≤ r ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦ hb i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc
    _ ≤ 3 * r ^ 2 := by exact_mod_cast hs
    _ ≤ (3 * r) ^ 2 := by nlinarith [sq_nonneg r]

theorem bv_cubical_isoperimetric {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) {r : ℝ} (hr : r ∈ Icc 0 1) :
    (torusVolume E).toReal * (r ^ 3 - (torusVolume E).toReal) ≤
      3 * r ^ 4 * (perimeter E).toReal := by
  let B := coordinateBox r
  let ν := torusVolume.restrict B
  let V := (torusVolume E).toReal
  let P := (perimeter E).toReal
  have hB : MeasurableSet B := measurableSet_coordinateBox r
  have hvol : ν.real univ = r ^ 3 := by
    simp only [ν, Measure.real, Measure.restrict_apply_univ, B, volume_coordinateBox hr,
      ENNReal.toReal_ofReal (pow_nonneg hr.1 3)]
  let g : Torus × Torus → ℝ := fun z ↦
    characteristic E z.1 * (1 - characteristic E (z.1 + z.2))
  have hgm : Measurable g := (measurable_characteristic hE |>.comp measurable_fst).mul
    (measurable_const.sub (measurable_characteristic hE |>.comp (measurable_fst.add measurable_snd)))
  have hgb (z : Torus × Torus) : |g z| ≤ 1 := by
    rcases characteristic_dichotomy E z.1 with h | h <;>
      rcases characteristic_dichotomy E (z.1 + z.2) with h' | h' <;> simp [g, h, h']
  have hgi : Integrable g (torusVolume.prod ν) :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
  have hchi (x : Torus) : Integrable (fun a ↦ characteristic E (x + a)) torusVolume :=
    Integrable.of_bound ((measurable_characteristic hE).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable 1
        (Eventually.of_forall fun a ↦ characteristic_bound E (x + a))
  have hchiB (x : Torus) : (∫ a, characteristic E (x + a) ∂ν) ≤ V := by
    calc
      _ ≤ ∫ a, characteristic E (x + a) ∂torusVolume :=
        setIntegral_le_integral (hchi x) (Eventually.of_forall fun a ↦ characteristic_nonneg E _)
      _ = V := by rw [integral_add_left_eq_self, integral_characteristic hE.nullMeasurableSet]
  have hinner (x : Torus) : characteristic E x * (r ^ 3 - V) ≤ ∫ a, g (x, a) ∂ν := by
    change _ ≤ ∫ a, characteristic E x * (1 - characteristic E (x + a)) ∂ν
    rw [integral_const_mul, integral_sub (integrable_const _) (hchi x).integrableOn,
      integral_const, smul_eq_mul, mul_one, hvol]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left (hchiB x) _) (characteristic_nonneg E x)
  have hlow : V * (r ^ 3 - V) ≤ ∫ x, ∫ a, g (x, a) ∂ν ∂torusVolume := by
    calc
      _ = ∫ x, characteristic E x * (r ^ 3 - V) ∂torusVolume := by
        rw [integral_mul_const, integral_characteristic hE.nullMeasurableSet]
      _ ≤ _ := integral_mono ((integrable_characteristic hE).mul_const _) hgi.integral_prod_left hinner
  have hupper (a : Torus) : (∫ x, g (x, a) ∂torusVolume) ≤ ‖representative a‖ * P := by
    have hi : Integrable (fun x ↦ |characteristic E (x + a) - characteristic E x|) torusVolume := by
      apply Integrable.of_bound
        (((measurable_characteristic hE).comp (measurable_id.add_const a)).sub
          (measurable_characteristic hE)).abs.aestronglyMeasurable 1
      exact Eventually.of_forall fun x ↦ by
        rcases characteristic_dichotomy E (x + a) with h | h <;>
          rcases characteristic_dichotomy E x with h' | h' <;> simp [h, h']
    calc
      _ ≤ ∫ x, |characteristic E (x + a) - characteristic E x| ∂torusVolume := by
        apply integral_mono (Integrable.of_bound
          (hgm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
            (Eventually.of_forall fun x ↦ hgb (x, a))) hi
        intro x
        rcases characteristic_dichotomy E (x + a) with h | h <;>
          rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
      _ ≤ _ := by simpa only [quotientMap_neg, quotientMap_representative, sub_neg_eq_add, norm_neg] using
        characteristic_translation_bound hE hP (-representative a)
  have hup : (∫ a, ∫ x, g (x, a) ∂torusVolume ∂ν) ≤ 3 * r ^ 4 * P := by
    calc
      _ ≤ ∫ a, (3 * r * P) ∂ν := by
        apply integral_mono_ae hgi.integral_prod_right (integrable_const _)
        filter_upwards [ae_restrict_mem hB] with a ha
        exact (hupper a).trans (mul_le_mul_of_nonneg_right
          (representative_norm_le_box hr.1 ha) ENNReal.toReal_nonneg)
      _ = _ := by rw [integral_const, smul_eq_mul, hvol]; ring
  exact hlow.trans ((integral_integral_swap hgi).le.trans hup)

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_WeightedPerimeter
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

theorem bv_isoperimetric_small_of_measurable {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) (hV : (torusVolume E).toReal ≤ 1 / 2) :
    (torusVolume E).toReal ^ (2 / 3 : ℝ) ≤ 12 * (perimeter E).toReal := by
  let V := (torusVolume E).toReal
  let P := (perimeter E).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  by_cases hz : V = 0
  · change V ^ (2 / 3 : ℝ) ≤ 12 * P
    rw [hz, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    positivity
  have hVp : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hz)
  let r := (2 * V) ^ (1 / 3 : ℝ)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hr3 : r ^ 3 = 2 * V := by
    dsimp only [r]
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (by positivity : 0 ≤ 2 * V)
      (by norm_num : (3 : ℕ) ≠ 0)
  have hr1 : r ≤ 1 := by
    have hh : 2 * V ≤ 1 := by dsimp only [V]; linarith
    dsimp only [r]
    exact (Real.rpow_le_rpow (by positivity) hh (by norm_num)).trans_eq (Real.one_rpow _)
  have hi := bv_cubical_isoperimetric hE hP ⟨hr0.le, hr1⟩
  change V * (r ^ 3 - V) ≤ 3 * r ^ 4 * P at hi
  rw [hr3] at hi
  have hi' : V ^ 2 ≤ 3 * r ^ 4 * P := by nlinarith [hi]
  have hs : r ^ 4 * (r ^ 2 - 12 * P) ≤ 0 := by
    have hsq := congrArg (fun a : ℝ ↦ a ^ 2) hr3
    nlinarith [hsq]
  have hr2 : r ^ 2 ≤ 12 * P := by
    have hh := nonpos_of_mul_nonpos_right hs (pow_pos hr0 4)
    linarith
  have he : (2 * V) ^ (2 / 3 : ℝ) = r ^ 2 := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 2 * V)]
    congr 1
    norm_num
  change V ^ (2 / 3 : ℝ) ≤ 12 * P
  calc
    _ ≤ (2 * V) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hV0 (by linarith) (by norm_num)
    _ = r ^ 2 := he
    _ ≤ _ := hr2

theorem bv_isoperimetric_small {E : Set Torus} (hE : FinitePerimeter E)
    (hV : (torusVolume E).toReal ≤ 1 / 2) :
    (torusVolume E).toReal ^ (2 / 3 : ℝ) ≤ 12 * (perimeter E).toReal := by
  have he := hE.1.toMeasurable_ae_eq
  have hp := perimeter_congr_ae he
  have hv : torusVolume (toMeasurable torusVolume E) = torusVolume E :=
    measure_congr he
  have hh := bv_isoperimetric_small_of_measurable
    (measurableSet_toMeasurable torusVolume E) (hp ▸ hE.2.ne) (by simpa only [hv] using hV)
  simpa only [hp, hv] using hh

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma exists_admissible_flux_gt (E : Set Torus) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Cover → Cover) (_hF : AdmissibleField F),
      (perimeter E).toReal - ε < ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  by_cases h : (perimeter E).toReal < ε
  · refine ⟨fun _ ↦ 0, admissible_zero, ?_⟩
    simpa only [divergence_zero, integral_zero] using sub_neg.mpr h
  · have hn : 0 ≤ (perimeter E).toReal - ε := sub_nonneg.mpr (le_of_not_gt h)
    by_contra! hnone
    have hb : perimeter E ≤ ENNReal.ofReal ((perimeter E).toReal - ε) := by
      exact iSup_le fun F ↦ iSup_le fun hF ↦ ENNReal.ofReal_le_ofReal (hnone F hF)
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal hn] at hh
    linarith

end CubicTorus

namespace CubicTorus

lemma regionDistance_nonneg (E F : Set Torus) : 0 ≤ regionDistance E F :=
  integral_nonneg (fun _ ↦ norm_nonneg _)

lemma abs_realVolume_sub_le_regionDistance {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    |torusVolume.real E - torusVolume.real F| ≤ regionDistance E F := by
  rw [Measure.real_def, Measure.real_def, ← integral_characteristic hE.nullMeasurableSet,
    ← integral_characteristic hF.nullMeasurableSet,
    ← integral_sub (integrable_characteristic hE) (integrable_characteristic hF)]
  exact norm_integral_le_integral_norm (fun x : Torus ↦ characteristic E x - characteristic F x)

lemma regionDistance_translation (E F : Set Torus) (a : Torus) :
    regionDistance ((fun z ↦ z + a) ⁻¹' E) ((fun z ↦ z + a) ⁻¹' F) = regionDistance E F := by
  have he (x : Torus) :
      characteristic ((fun z ↦ z + a) ⁻¹' E) x = characteristic E (x + a) := by
    by_cases hx : x + a ∈ E <;> simp [characteristic, hx]
  have hf (x : Torus) :
      characteristic ((fun z ↦ z + a) ⁻¹' F) x = characteristic F (x + a) := by
    by_cases hx : x + a ∈ F <;> simp [characteristic, hx]
  unfold regionDistance
  simp_rw [he, hf]
  exact (measurePreserving_add_right torusVolume a).integral_comp
    (Homeomorph.addRight a).measurableEmbedding
      (fun x : Torus ↦ ‖characteristic E x - characteristic F x‖)

lemma characteristic_mul_eq_indicator (E : Set Torus) (g : Torus → ℝ) :
    (fun x ↦ characteristic E x * g x) = E.indicator g := by
  funext x
  by_cases hx : x ∈ E <;> simp [characteristic, hx]

lemma abs_weighted_characteristic_sub_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) {g : Torus → ℝ}
    (hg : Measurable g) {M : ℝ} (hb : ∀ x, ‖g x‖ ≤ M) :
    |(∫ x, characteristic E x * g x ∂torusVolume) -
      (∫ x, characteristic F x * g x ∂torusVolume)| ≤ M * regionDistance E F := by
  have hi : Integrable g torusVolume := Integrable.of_bound hg.aestronglyMeasurable M
    (Filter.Eventually.of_forall hb)
  have hiE : Integrable (fun x ↦ characteristic E x * g x) torusVolume := by
    rw [characteristic_mul_eq_indicator]
    exact hi.indicator hE
  have hiF : Integrable (fun x ↦ characteristic F x * g x) torusVolume := by
    rw [characteristic_mul_eq_indicator]
    exact hi.indicator hF
  rw [← integral_sub hiE hiF]
  calc
    _ ≤ ∫ x, ‖characteristic E x * g x - characteristic F x * g x‖ ∂torusVolume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, M * ‖characteristic E x - characteristic F x‖ ∂torusVolume := by
      apply integral_mono (hiE.sub hiF).norm
        (((integrable_characteristic hE).sub (integrable_characteristic hF)).norm.const_mul M)
      intro x
      change ‖characteristic E x * g x - characteristic F x * g x‖ ≤
        M * ‖characteristic E x - characteristic F x‖
      rw [← sub_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

lemma directionalFlux_eq_pairing (E : Set Torus) (hE : MeasurableSet E)
    (D : WallVariation) :
    directionalFlux E D.coordinate D.function =
      ∫ x, characteristic E x *
        fderiv ℝ D.function (representative x) (EuclideanSpace.single D.coordinate 1) ∂torusVolume := by
  rw [characteristic_mul_eq_indicator, integral_indicator hE]
  exact (setIntegral_lift
    ((D.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    (fun n x ↦ by rw [fderiv_periodic D.periodic]) hE).symm

lemma WallVariation.directionalDeriv_bound (D : WallVariation) (x : Cover) :
    ‖fderiv ℝ D.function x (EuclideanSpace.single D.coordinate 1)‖ ≤ (D.bound : ℝ) := by
  have hM : ‖fderiv ℝ D.function x‖ ≤ (D.bound : ℝ) := by exact_mod_cast D.derivative_bound x
  simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ D.function x)
    (EuclideanSpace.single D.coordinate 1)).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

lemma WallVariation.flux_lipschitz (D : WallVariation) {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    |directionalFlux E D.coordinate D.function - directionalFlux F D.coordinate D.function| ≤
      (D.bound : ℝ) * regionDistance E F := by
  rw [directionalFlux_eq_pairing E hE, directionalFlux_eq_pairing F hF]
  apply abs_weighted_characteristic_sub_le hE hF
    (((D.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.comp
      measurable_representative)
  intro x
  exact D.directionalDeriv_bound _

end CubicTorus

namespace CubicTorus

lemma positive_flux_nearby (D : WallVariation) {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hδ : 0 < directionalFlux E D.coordinate D.function)
    (hd : regionDistance E F < directionalFlux E D.coordinate D.function /
      (4 * ((D.bound : ℝ) + 1))) :
    directionalFlux E D.coordinate D.function / 2 <
      directionalFlux F D.coordinate D.function := by
  have hh := (le_abs_self _).trans (D.flux_lipschitz hE hF)
  have hd' := (lt_div_iff₀ (by positivity : 0 < 4 * ((D.bound : ℝ) + 1))).1 hd
  have hnon := regionDistance_nonneg E F
  have hM := D.bound.coe_nonneg
  nlinarith

theorem local_comparison_of_positive_flux {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E) (D : WallVariation)
    (hδ : 0 < directionalFlux E D.coordinate D.function) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ F : Set Torus,
      MeasurableSet F → perimeter F ≠ ⊤ → regionDistance E F < ε →
      (perimeter E).toReal ≤ (perimeter F).toReal + C * regionDistance E F := by
  let δ := directionalFlux E D.coordinate D.function
  let M : ℝ := D.bound
  let p := (perimeter E).toReal
  refine ⟨δ / (4 * (M + 1)), 4 * M * p / δ, by positivity, by positivity, ?_⟩
  intro F hF hFP hd
  have hδF := positive_flux_nearby D hE hF hδ hd
  let δF := directionalFlux F D.coordinate D.function
  let d := regionDistance E F
  have hd0 : 0 ≤ d := regionDistance_nonneg _ _
  have hM : 0 ≤ M := D.bound.coe_nonneg
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hδ0 : 0 < δ := hδ
  have hf0 : 0 < δF := by dsimp only [δF]; linarith
  have hδF' : δ / 2 < δF := hδF
  let t := (torusVolume.real E - torusVolume.real F) / δF
  have ht_abs : |t| ≤ d / δF := by
    dsimp only [t]
    rw [abs_div, abs_of_pos hf0]
    exact div_le_div_of_nonneg_right (abs_realVolume_sub_le_regionDistance hE hF) hf0.le
  have ht2 : |t| ≤ 2 * d / δ := by
    apply ht_abs.trans
    apply (div_le_div_iff₀ hf0 hδ0).2
    nlinarith
  have hd' : d * (4 * (M + 1)) < δ :=
    (lt_div_iff₀ (by positivity : 0 < 4 * (M + 1))).1 hd
  have htM : |t| * M < 1 := by
    have hh := mul_le_mul_of_nonneg_right ht2 hM
    have hh' : (2 * d / δ) * M < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hδ0]
      nlinarith
    exact hh.trans_lt hh'
  obtain ⟨hG, hGv, hGP⟩ := coordinate_variation D.coordinate D.smooth D.periodic
    D.derivative_bound D.faces htM hF hFP
  have hvol : torusVolume (coordinateRegion D.coordinate D.function t F) = torusVolume E := by
    have hv : torusVolume.real (coordinateRegion D.coordinate D.function t F) =
        torusVolume.real E := by
      rw [hGv]
      change torusVolume.real F + t * δF = torusVolume.real E
      dsimp only [t]
      field_simp
      ring
    have hh := congrArg ENNReal.ofReal hv
    simpa only [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
  have hminimal : p ≤ (1 + 2 * |t| * M) * (perimeter F).toReal := by
    apply (ENNReal.toReal_mono hG.2.ne (hmin.2.2 _ hG (hvol.trans hmin.2.1))).trans hGP
  by_cases hl : p ≤ (perimeter F).toReal
  · exact hl.trans (le_add_of_nonneg_right (by positivity))
  · have hl' : (perimeter F).toReal ≤ p := le_of_not_ge hl
    have hscale : 2 * |t| * M ≤ (4 * M / δ) * d := by
      have hh := mul_le_mul_of_nonneg_right ht2 (by positivity : 0 ≤ 2 * M)
      calc
        2 * |t| * M = |t| * (2 * M) := by ring
        _ ≤ (2 * d / δ) * (2 * M) := hh
        _ = (4 * M / δ) * d := by ring
    have h1 := mul_le_mul_of_nonneg_right hscale (ENNReal.toReal_nonneg (a := perimeter F))
    have h2 := mul_le_mul_of_nonneg_left hl' (by positivity : 0 ≤ (4 * M / δ) * d)
    have heq : ((4 * M / δ) * d) * p = (4 * M * p / δ) * d := by ring
    nlinarith

end CubicTorus

namespace CubicTorus

lemma regionDistance_congr_ae {E E' F F' : Set Torus}
    (hE : E =ᵐ[torusVolume] E') (hF : F =ᵐ[torusVolume] F') :
    regionDistance E F = regionDistance E' F' := by
  apply integral_congr_ae
  filter_upwards [hE, hF] with x hx hy
  have hx' : x ∈ E ↔ x ∈ E' := Iff.of_eq hx
  have hy' : x ∈ F ↔ x ∈ F' := Iff.of_eq hy
  by_cases ha : x ∈ E <;> by_cases hb : x ∈ F <;> simp_all [characteristic]

theorem isMinimizerAt_local_quasiminimal {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ F : Set Torus,
      FinitePerimeter F → regionDistance E F < ε →
      (perimeter E).toReal ≤ (perimeter F).toReal + C * regionDistance E F := by
  let E₀ := toMeasurable torusVolume E
  have hE₀ : MeasurableSet E₀ := measurableSet_toMeasurable _ _
  have he : E₀ =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hm₀ : IsMinimizerAt V E₀ := (isMinimizerAt_congr_ae he).2 hmin
  obtain ⟨a, D, hδ⟩ := exists_positive_wallVariation hE₀
    (perimeter_pos_of_volume hV hm₀.1.1 hm₀.2.1)
  let R : Torus → Torus := fun z ↦ z + quotientMap a
  have hRm : Measurable R := (continuous_add_const _).measurable
  obtain ⟨ε, C, heps, hC, hcompare⟩ := local_comparison_of_positive_flux
    (isMinimizerAt_translation hm₀ (quotientMap a)) (hE₀.preimage hRm) D hδ
  refine ⟨ε, C, heps, hC, ?_⟩
  intro F hF hd
  let F₀ := toMeasurable torusVolume F
  have hF₀ : MeasurableSet F₀ := measurableSet_toMeasurable _ _
  have hf : F₀ =ᵐ[torusVolume] F := hF.1.toMeasurable_ae_eq
  have hfp : FinitePerimeter F₀ := (finitePerimeter_congr_ae hf).2 hF
  have hdist : regionDistance (R ⁻¹' E₀) (R ⁻¹' F₀) = regionDistance E F := by
    rw [regionDistance_translation, regionDistance_congr_ae he hf]
  have hh := hcompare (R ⁻¹' F₀) (hF₀.preimage hRm)
    (finitePerimeter_translation hfp (quotientMap a)).2.ne (hdist ▸ hd)
  rw [hdist, perimeter_translation hm₀.1.1, perimeter_translation hfp.1,
    perimeter_congr_ae he, perimeter_congr_ae hf] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma divergence_add_fields {F G : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (hG : DifferentiableAt ℝ G point) :
    divergence (fun y ↦ F y + G y) point = divergence F point + divergence G point := by
  change (∑ i : Fin 3, (fderiv ℝ (F + G) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_add hF hG]
  simp [divergence, Finset.sum_add_distrib]

lemma admissible_convex_cutoff {w : Cover → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    (hb : ∀ x, w x ∈ Icc 0 1)
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    AdmissibleField (fun x ↦ w x • F x + (1 - w x) • G x) := by
  refine ⟨(hw.smul hF.1).add ((contDiff_const.sub hw).smul hG.1), ?_, ?_⟩
  · intro n x
    dsimp only
    rw [hp, hF.2.1, hG.2.1]
  · intro x
    calc
      _ ≤ ‖w x • F x‖ + ‖(1 - w x) • G x‖ := norm_add_le _ _
      _ = w x * ‖F x‖ + (1 - w x) * ‖G x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hb x).1, abs_of_nonneg (sub_nonneg.mpr (hb x).2)]
      _ ≤ w x * 1 + (1 - w x) * 1 := add_le_add
        (mul_le_mul_of_nonneg_left (hF.2.2 x) (hb x).1)
        (mul_le_mul_of_nonneg_left (hG.2.2 x) (sub_nonneg.mpr (hb x).2))
      _ = 1 := by ring

lemma cutoff_partition_flux_le {E : Set Torus} (hP : perimeter E ≠ ⊤)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    (hb : ∀ x, w x ∈ Icc 0 1)
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      (w x * divergence F x + (1 - w x) * divergence G x)) ≤
    (perimeter E).toReal + 2 *
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, ‖gradient w x‖ := by
  let H : Cover → Cover := fun x ↦ w x • F x + (1 - w x) • G x
  have hH : AdmissibleField H := admissible_convex_cutoff hw hp hb hF hG
  have hd (x) : divergence H x = w x * divergence F x +
      (1 - w x) * divergence G x + ⟪gradient w x, F x - G x⟫ := by
    have hwd : DifferentiableAt ℝ (fun y : Cover ↦ w y • F y) x := by
      convert! ((hw.smul hF.1).differentiable (by simp)) x using 1
      all_goals try with_reducible_and_instances rfl
    have hgd : DifferentiableAt ℝ (fun y : Cover ↦ (1 - w y) • G y) x := by
      convert! (((show ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Cover ↦ 1 - w y) from contDiff_const.sub hw).smul hG.1).differentiable (by simp)) x using 1
      all_goals try with_reducible_and_instances rfl
    dsimp only [H]
    rw [divergence_add_fields hwd hgd,
      divergence_smul_function (hw.differentiable (by simp)).differentiableAt
        (hF.1.differentiable (by simp)).differentiableAt,
      divergence_smul_function ((show ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ 1 - w x)
        from contDiff_const.sub hw).differentiable (by simp)).differentiableAt
        (hG.1.differentiable (by simp)).differentiableAt,
      gradient_const_sub, inner_neg_left, inner_sub_right]
    ring
  have hii : IntegrableOn (fun x ↦ ⟪gradient w x, F x - G x⟫)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous
      ((gradient_contDiff hw).continuous.inner (hF.1.continuous.sub hG.1.continuous))
      (fun n x ↦ by simp only [Pi.sub_apply, gradient_periodic hp, hF.2.1, hG.2.1])).mono_set inter_subset_left
  have hign : IntegrableOn (fun x ↦ ‖gradient w x‖)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous (gradient_contDiff hw).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])).mono_set inter_subset_left
  have hiH := (integrableOn_divergence hH.1).mono_set (s := fundamentalCube ∩ quotientMap ⁻¹' E)
    inter_subset_left
  have heq : (fun x ↦ w x * divergence F x + (1 - w x) * divergence G x) =
      (fun x ↦ divergence H x - ⟪gradient w x, F x - G x⟫) := by
    funext x
    rw [hd]
    ring
  rw [heq, integral_sub hiH hii]
  have hflux := (le_abs_self _).trans (abs_flux_le_perimeter hP hH)
  have herror : -(∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      ⟪gradient w x, F x - G x⟫) ≤
      2 * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, ‖gradient w x‖ := by
    rw [← integral_neg, ← integral_const_mul]
    apply integral_mono hii.neg (hign.const_mul 2)
    intro x
    have hg : ‖F x - G x‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hF.2.2 x, hG.2.2 x])
    calc
      _ ≤ |⟪gradient w x, F x - G x⟫| := neg_le_abs _
      _ ≤ ‖gradient w x‖ * ‖F x - G x‖ := abs_real_inner_le_norm _ _
      _ ≤ _ := by nlinarith [norm_nonneg (gradient w x)]
  linarith

end CubicTorus

namespace CubicTorus

lemma smoothTransition_deriv_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.smoothTransition.zero_of_nonpos hx]
  exact Real.smoothTransition.nonneg y

lemma smoothTransition_deriv_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.smoothTransition.one_of_one_le hx]
  exact Real.smoothTransition.le_one y

lemma smoothTransition_exists_deriv_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x, ‖deriv Real.smoothTransition x‖ ≤ K := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (2 : ℕ∞))).continuous_deriv (by norm_num)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  by_cases h0 : x < 0
  · rw [smoothTransition_deriv_zero_of_nonpos h0.le, norm_zero]
    exact (zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  by_cases h1 : 1 < x
  · rw [smoothTransition_deriv_zero_of_one_le h1.le, norm_zero]
    exact (zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  exact (hM x ⟨le_of_not_gt h0, le_of_not_gt h1⟩).trans (le_max_left _ _)

lemma sublevelCutoff_contDiff {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (t ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelCutoff q t ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const ε)

lemma sublevelCutoff_periodic {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x) (t ε : ℝ) :
    ∀ n x, sublevelCutoff q t ε (x + latticeVector n) = sublevelCutoff q t ε x := by
  intro n x
  simp only [sublevelCutoff, hp]

lemma sublevelCutoff_mem_Icc (q : Cover → ℝ) (t ε : ℝ) (x : Cover) :
    sublevelCutoff q t ε x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma fderiv_sublevelCutoff {q : Cover → ℝ} {x : Cover}
    (hq : DifferentiableAt ℝ q x) (t ε : ℝ) :
    fderiv ℝ (sublevelCutoff q t ε) x =
      (deriv Real.smoothTransition ((t - q x) / ε) / ε) • (-fderiv ℝ q x) := by
  have hd : DifferentiableAt ℝ Real.smoothTransition ((t - q x) / ε) :=
    (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by norm_num) _
  have hi := (hq.hasFDerivAt.const_sub t).const_smul ε⁻¹
  have hi' : HasFDerivAt (fun y : Cover ↦ (t - q y) / ε)
      (ε⁻¹ • (-fderiv ℝ q x)) x := by
    convert! hi using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp [div_eq_inv_mul]
  have ho := hd.hasDerivAt.comp_hasFDerivAt x hi'
  calc
    _ = deriv Real.smoothTransition ((t - q x) / ε) • (ε⁻¹ • (-fderiv ℝ q x)) := by
      convert! ho.fderiv using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := by simp only [div_eq_mul_inv, smul_smul]

lemma norm_gradient_eq_norm_fderiv (f : Cover → ℝ) (x : Cover) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ Cover).symm.norm_map _

lemma sublevelCutoff_gradient_bound {q : Cover → ℝ}
    (hq : Differentiable ℝ q) {K : ℝ}
    (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : Cover) :
    ‖gradient (sublevelCutoff q t ε) x‖ ≤ (K / ε) * ‖gradient q x‖ := by
  rw [norm_gradient_eq_norm_fderiv, fderiv_sublevelCutoff (hq x),
    norm_smul, norm_div, norm_neg, Real.norm_of_nonneg hε.le,
    norm_gradient_eq_norm_fderiv]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hK _) hε.le) (norm_nonneg _)

lemma sublevelCutoff_gradient_zero {q : Cover → ℝ}
    (hq : Differentiable ℝ q) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : Cover)
    (hx : q x ≤ t - ε ∨ t ≤ q x) :
    gradient (sublevelCutoff q t ε) x = 0 := by
  apply (InnerProductSpace.toDual ℝ Cover).injective
  simp only [gradient, LinearIsometryEquiv.apply_symm_apply, map_zero]
  rw [fderiv_sublevelCutoff (hq x)]
  have hd : deriv Real.smoothTransition ((t - q x) / ε) = 0 := by
    rcases hx with hx | hx
    · apply smoothTransition_deriv_zero_of_one_le
      apply (le_div_iff₀ hε).2
      linarith
    · exact smoothTransition_deriv_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le)
  rw [hd, zero_div, zero_smul]

end CubicTorus

namespace CubicTorus

lemma perimeter_partition_le_of_flux_bound {E B : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hB : MeasurableSet B) {C : ℝ}
    (hb : ∀ (F G : Cover → Cover), AdmissibleField F → AdmissibleField G →
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B), divergence F x) +
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E \ B), divergence G x) ≤ C) :
    FinitePerimeter (E ∩ B) ∧ FinitePerimeter (E \ B) ∧
      (perimeter (E ∩ B)).toReal + (perimeter (E \ B)).toReal ≤ C := by
  have ha : perimeter (E ∩ B) ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    simpa only [divergence_zero, integral_zero, add_zero] using hb F (fun _ ↦ 0) hF admissible_zero
  have hd : perimeter (E \ B) ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro G
    apply iSup_le
    intro hG
    apply ENNReal.ofReal_le_ofReal
    simpa only [divergence_zero, integral_zero, zero_add] using hb (fun _ ↦ 0) G admissible_zero hG
  refine ⟨⟨hE.inter hB.nullMeasurableSet, ha.trans_lt ENNReal.ofReal_lt_top⟩,
    ⟨hE.diff hB.nullMeasurableSet, hd.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F, hF, hf⟩ := exists_admissible_flux_gt (E ∩ B) (half_pos hε)
  obtain ⟨G, hG, hg⟩ := exists_admissible_flux_gt (E \ B) (half_pos hε)
  linarith [hb F G hF hG]

lemma partition_flux_tendsto {E B : Set Torus} (hB : MeasurableSet B)
    {w : ℕ → Cover → ℝ} (hw : ∀ n, Continuous (w n))
    (hb : ∀ n x, w n x ∈ Icc (0 : ℝ) 1)
    (ht : ∀ x, Tendsto (fun n ↦ w n x) atTop (𝓝 (characteristic B (quotientMap x))))
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    Tendsto (fun n ↦ ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      w n x * divergence F x + (1 - w n x) * divergence G x) atTop
      (𝓝 ((∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B), divergence F x) +
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E \ B), divergence G x)) := by
  have hiF := (integrableOn_divergence hF.1).mono_set
    (s := fundamentalCube ∩ quotientMap ⁻¹' E) inter_subset_left
  have hiG := (integrableOn_divergence hG.1).mono_set
    (s := fundamentalCube ∩ quotientMap ⁻¹' E) inter_subset_left
  have hh := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E))
    (bound := fun x ↦ |divergence F x| + |divergence G x|)
    (F := fun n x ↦ w n x * divergence F x + (1 - w n x) * divergence G x)
    (f := fun x ↦ characteristic B (quotientMap x) * divergence F x +
      (1 - characteristic B (quotientMap x)) * divergence G x)
    (fun n ↦ (((hw n).mul (continuous_divergence hF.1)).add
      ((continuous_const.sub (hw n)).mul (continuous_divergence hG.1))).aestronglyMeasurable)
    (hiF.abs.add hiG.abs) (fun n ↦ Eventually.of_forall fun x ↦ ?_)
    (Eventually.of_forall fun x ↦ (ht x |>.mul tendsto_const_nhds).add
      ((tendsto_const_nhds.sub (ht x)).mul tendsto_const_nhds))
  · have heq : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        characteristic B (quotientMap x) * divergence F x +
        (1 - characteristic B (quotientMap x)) * divergence G x) =
        (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B), divergence F x) +
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E \ B), divergence G x := by
      have hp (x : Cover) : characteristic B (quotientMap x) * divergence F x +
          (1 - characteristic B (quotientMap x)) * divergence G x =
          (quotientMap ⁻¹' B).indicator (divergence F) x +
          (quotientMap ⁻¹' Bᶜ).indicator (divergence G) x := by
        classical
        by_cases hx : quotientMap x ∈ B <;> simp [characteristic, hx]
      simp_rw [hp]
      rw [integral_add (hiF.indicator (measurable_quotientMap hB))
        (hiG.indicator (measurable_quotientMap hB.compl)),
        integral_indicator (measurable_quotientMap hB),
        integral_indicator (measurable_quotientMap hB.compl),
        Measure.restrict_restrict (measurable_quotientMap hB),
        Measure.restrict_restrict (measurable_quotientMap hB.compl)]
      rw [show (quotientMap ⁻¹' B) ∩ (fundamentalCube ∩ quotientMap ⁻¹' E) =
          fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B) by ext x; simp only [mem_inter_iff, mem_preimage]; tauto,
        show (quotientMap ⁻¹' Bᶜ) ∩ (fundamentalCube ∩ quotientMap ⁻¹' E) =
          fundamentalCube ∩ quotientMap ⁻¹' (E \ B) by ext x; simp only [mem_inter_iff, mem_preimage, mem_compl_iff, Set.mem_sdiff]; tauto]
    exact heq ▸ hh
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ |w n x * divergence F x| + |(1 - w n x) * divergence G x| := abs_add_le _ _
      _ = w n x * |divergence F x| + (1 - w n x) * |divergence G x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hb n x).1,
          abs_of_nonneg (sub_nonneg.mpr (hb n x).2)]
      _ ≤ _ := add_le_add (mul_le_of_le_one_left (abs_nonneg _) (hb n x).2)
        (mul_le_of_le_one_left (abs_nonneg _) (by linarith [(hb n x).1]))

end CubicTorus

namespace CubicTorus

lemma measurableSet_sublevelRegion {q : Cover → ℝ} (hq : Measurable q) (t : ℝ) :
    MeasurableSet (sublevelRegion q t) :=
  measurableSet_lt (hq.comp measurable_representative) measurable_const

lemma mem_sublevelRegion_quotient {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x) (t : ℝ) (x : Cover) :
    quotientMap x ∈ sublevelRegion q t ↔ q x < t := by
  simp only [sublevelRegion, mem_ofPred_eq, periodic_representative hp]

lemma sublevelRegion_mono (q : Cover → ℝ) : Monotone (sublevelRegion q) := by
  intro s t hst z hz
  exact hz.trans_le hst

lemma sublevelVolume_mono (E : Set Torus) (q : Cover → ℝ) :
    Monotone (sublevelVolume E q) := by
  intro s t hst
  exact measureReal_mono (inter_subset_inter_right E (sublevelRegion_mono q hst))

lemma sublevelCutoff_gradient_integral_le {E : Set Torus} (hE : MeasurableSet E)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {K M t ε : ℝ}
    (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    (hgrad : ∀ x, q x < t → ‖gradient q x‖ ≤ M) (hε : 0 < ε) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      ‖gradient (sublevelCutoff q t ε) x‖) ≤
      K * M * ((sublevelVolume E q t - sublevelVolume E q (t - ε)) / ε) := by
  let A := sublevelRegion q t \ sublevelRegion q (t - ε)
  have hmA : MeasurableSet A := (measurableSet_sublevelRegion hq.continuous.measurable t).diff
    (measurableSet_sublevelRegion hq.continuous.measurable (t - ε))
  have hqdiff := hq.differentiable (by simp)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hb (x : Cover) : ‖gradient (sublevelCutoff q t ε) x‖ ≤
      (quotientMap ⁻¹' A).indicator (fun _ ↦ K * M / ε) x := by
    classical
    by_cases hx : x ∈ quotientMap ⁻¹' A
    · rw [Set.indicator_of_mem hx]
      have hxt : q x < t := (mem_sublevelRegion_quotient hp t x).1 hx.1
      calc
        _ ≤ (K / ε) * ‖gradient q x‖ := sublevelCutoff_gradient_bound hqdiff hK hε t x
        _ ≤ (K / ε) * M := mul_le_mul_of_nonneg_left (hgrad x hxt) (div_nonneg hK0 hε.le)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hx]
      rw [sublevelCutoff_gradient_zero hqdiff hε t x, norm_zero]
      have hn : ¬(q x < t ∧ ¬q x < t - ε) := by
        simpa only [A, mem_preimage, Set.mem_sdiff, mem_sublevelRegion_quotient hp] using hx
      rcases le_or_gt t (q x) with h | h
      · exact Or.inr h
      · exact Or.inl (le_of_lt (not_not.mp (fun hh ↦ hn ⟨h, hh⟩)))
  have hig : IntegrableOn (fun x ↦ ‖gradient (sublevelCutoff q t ε) x‖)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous (gradient_contDiff (sublevelCutoff_contDiff hq t ε)).continuous.norm
      (fun n x ↦ by rw [gradient_periodic (sublevelCutoff_periodic hp t ε)])).mono_set inter_subset_left
  have hic : IntegrableOn (fun _ : Cover ↦ K * M / ε)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous continuous_const (fun _ _ ↦ rfl)).mono_set inter_subset_left
  have hh := integral_mono hig (hic.indicator (measurable_quotientMap hmA)) hb
  rw [integral_indicator (measurable_quotientMap hmA),
    Measure.restrict_restrict (measurable_quotientMap hmA)] at hh
  have heq : quotientMap ⁻¹' A ∩ (fundamentalCube ∩ quotientMap ⁻¹' E) =
      fundamentalCube ∩ quotientMap ⁻¹' (E ∩ A) := by ext x; simp only [mem_inter_iff, mem_preimage]; tauto
  rw [heq, integral_const] at hh
  simp only [Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul] at hh
  change _ ≤ volume.real (fundamentalCube ∩ quotientMap ⁻¹' (E ∩ A)) * (K * M / ε) at hh
  rw [← realVolume_lift (hE.inter hmA)] at hh
  have hsets : E ∩ A = (E ∩ sublevelRegion q t) \ (E ∩ sublevelRegion q (t - ε)) := by
    ext z; simp only [A, mem_inter_iff, Set.mem_sdiff]; tauto
  have hsubset : E ∩ sublevelRegion q (t - ε) ⊆ E ∩ sublevelRegion q t :=
    inter_subset_inter_right E (sublevelRegion_mono q (by linarith))
  rw [hsets, measureReal_sdiff hsubset
    (hE.inter (measurableSet_sublevelRegion hq.continuous.measurable (t - ε)))] at hh
  change _ ≤ (sublevelVolume E q t - sublevelVolume E q (t - ε)) * (K * M / ε) at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicTorus

namespace CubicTorus

lemma sublevelCutoff_tendsto {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (t : ℝ) (x : Cover) :
    Tendsto (fun n ↦ sublevelCutoff q t (ε n) x) atTop
      (𝓝 (characteristic (sublevelRegion q t) (quotientMap x))) := by
  classical
  by_cases hx : q x < t
  · have hmem := (mem_sublevelRegion_quotient hp t x).2 hx
    have he : ∀ᶠ n in atTop, sublevelCutoff q t (ε n) x = 1 := by
      filter_upwards [hεlim.eventually (gt_mem_nhds (sub_pos.mpr hx))] with n hn
      apply Real.smoothTransition.one_of_one_le
      apply (le_div_iff₀ (hε n)).2
      linarith
    rw [characteristic, indicator_of_mem hmem]
    exact tendsto_const_nhds.congr' (he.mono fun _ hn ↦ hn.symm)
  · have hmem : quotientMap x ∉ sublevelRegion q t :=
      fun h ↦ hx ((mem_sublevelRegion_quotient hp t x).1 h)
    rw [characteristic, indicator_of_notMem hmem]
    have he (n) : sublevelCutoff q t (ε n) x = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hx)) (hε n).le
    simpa only [he] using (tendsto_const_nhds (x := (0 : ℝ)) :
      Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

lemma tendsto_backward_quotient_of_hasDerivAt {m : ℝ → ℝ} {d t : ℝ}
    (hm : HasDerivAt m d t) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ (m t - m (t - ε n)) / ε n) atTop (𝓝 d) := by
  have hlim : Tendsto (fun n ↦ t - ε n) atTop (𝓝[≠] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using tendsto_const_nhds.sub hεlim, Eventually.of_forall fun n ↦ ?_⟩
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [hε n]
  have hs := hm.tendsto_slope.comp hlim
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [Function.comp_apply, slope_def_field, show t - ε n - t = -(ε n) by ring, div_neg]
  ring

theorem perimeter_sublevel_partition {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hp : ∀ n x, q (x + latticeVector n) = q x)
    {K M t d : ℝ} (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    (hgrad : ∀ x, q x < t → ‖gradient q x‖ ≤ M)
    (hd : HasDerivAt (sublevelVolume E q) d t) :
    FinitePerimeter (E ∩ sublevelRegion q t) ∧
    FinitePerimeter (E \ sublevelRegion q t) ∧
    (perimeter (E ∩ sublevelRegion q t)).toReal +
      (perimeter (E \ sublevelRegion q t)).toReal ≤ (perimeter E).toReal + 2 * K * M * d := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n ↦ by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb := measurableSet_sublevelRegion hq.continuous.measurable t
  apply perimeter_partition_le_of_flux_bound hE.nullMeasurableSet hb
  intro F G hF hG
  have hlim := partition_flux_tendsto (E := E) hb
    (fun n ↦ (sublevelCutoff_contDiff hq t (ε n)).continuous)
    (fun n x ↦ sublevelCutoff_mem_Icc q t (ε n) x)
    (sublevelCutoff_tendsto hp hε helim t) hF hG
  have hh := tendsto_backward_quotient_of_hasDerivAt hd hε helim
  have hrlim : Tendsto (fun n ↦ (perimeter E).toReal + 2 * K * M *
      ((sublevelVolume E q t - sublevelVolume E q (t - ε n)) / ε n)) atTop
        (𝓝 ((perimeter E).toReal + 2 * K * M * d)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hh)
  apply le_of_tendsto_of_tendsto' hlim hrlim
  intro n
  calc
    _ ≤ (perimeter E).toReal + 2 * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        ‖gradient (sublevelCutoff q t (ε n)) x‖ :=
      cutoff_partition_flux_le hP (sublevelCutoff_contDiff hq t (ε n))
        (sublevelCutoff_periodic hp t (ε n)) (sublevelCutoff_mem_Icc q t (ε n)) hF hG
    _ ≤ (perimeter E).toReal + 2 * (K * M *
        ((sublevelVolume E q t - sublevelVolume E q (t - ε n)) / ε n)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (sublevelCutoff_gradient_integral_le hE hq hp hK hgrad (hε n)) (show (0 : ℝ) ≤ 2 by norm_num))
    _ = _ := by ring

end CubicTorus

namespace CubicTorus

lemma regionDistance_sdiff {E B : Set Torus} (hE : NullMeasurableSet E torusVolume)
    (hB : NullMeasurableSet B torusVolume) :
    regionDistance E (E \ B) = torusVolume.real (E ∩ B) := by
  have heq (x : Torus) : ‖characteristic E x - characteristic (E \ B) x‖ =
      characteristic (E ∩ B) x := by
    classical
    by_cases he : x ∈ E <;> by_cases hb : x ∈ B <;> simp [characteristic, he, hb]
  unfold regionDistance
  simp_rw [heq]
  exact integral_characteristic (hE.inter hB)

theorem isMinimizerAt_sublevel_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (q : Cover → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) q → (∀ n x, q (x + latticeVector n) = q x) →
      ∀ K M t d : ℝ, (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      (∀ x, q x < t → ‖gradient q x‖ ≤ M) →
      HasDerivAt (sublevelVolume E q) d t → sublevelVolume E q t < η →
      (perimeter (E ∩ sublevelRegion q t)).toReal ≤
        C * sublevelVolume E q t + 2 * K * M * d := by
  obtain ⟨η, C, hη, hC, hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η, C, hη, hC, ?_⟩
  intro q hq hp K M t d hK hgrad hd ht
  obtain ⟨_, hdiff, hpart⟩ := perimeter_sublevel_partition hE hmin.1.2.ne hq hp hK hgrad hd
  have hdist : regionDistance E (E \ sublevelRegion q t) = sublevelVolume E q t :=
    regionDistance_sdiff hmin.1.1 (measurableSet_sublevelRegion hq.continuous.measurable t).nullMeasurableSet
  have hcomp := hc (E \ sublevelRegion q t) hdiff (by rwa [hdist])
  rw [hdist] at hcomp
  linarith

theorem isMinimizerAt_sublevel_density_inequality {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ η C K : ℝ, 0 < η ∧ 0 ≤ C ∧ 0 < K ∧
      ∀ (q : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) q →
      (∀ n x, q (x + latticeVector n) = q x) →
      ∀ᵐ t : ℝ, ∀ M : ℝ, (∀ x, q x < t → ‖gradient q x‖ ≤ M) →
        sublevelVolume E q t < η → sublevelVolume E q t ≤ 1/2 →
        sublevelVolume E q t ^ (2 / 3 : ℝ) ≤
          12 * C * sublevelVolume E q t + 24 * K * M * deriv (sublevelVolume E q) t := by
  obtain ⟨η, C, hη, hC, hc⟩ := isMinimizerAt_sublevel_comparison hV hE hmin
  obtain ⟨K, hKpos, hK⟩ := smoothTransition_exists_deriv_bound
  refine ⟨η, C, K, hη, hC, hKpos, ?_⟩
  intro q hq hp
  filter_upwards [(sublevelVolume_mono E q).ae_differentiableAt] with t ht
  intro M hgrad hm hhalf
  have hcomp := hc q hq hp K M t (deriv (sublevelVolume E q) t) hK hgrad ht.hasDerivAt hm
  obtain ⟨hcut, _, _⟩ := perimeter_sublevel_partition hE hmin.1.2.ne hq hp hK hgrad ht.hasDerivAt
  have hiso := bv_isoperimetric_small hcut hhalf
  change sublevelVolume E q t ^ (2 / 3 : ℝ) ≤ _ at hiso
  linarith

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

lemma measurableSet_cubeBall (r : ℝ) : MeasurableSet (cubeBall r) :=
  Metric.isOpen_ball.measurableSet.preimage measurable_representative

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 1 / 2) :
    Metric.ball cubeCenter r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - cubeCenter‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans_lt hx'
  change ‖x i - (1 / 2 : ℝ)‖ < r at hb
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

lemma cubeBall_lift {r : ℝ} (hr : r ≤ 1 / 2) :
    fundamentalCube ∩ quotientMap ⁻¹' cubeBall r = Metric.ball cubeCenter r := by
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    change representative (quotientMap x) ∈ Metric.ball cubeCenter r at hball
    rwa [representative_quotientMap_of_mem hx] at hball
  · intro hx
    have hm := coverBall_subset_cube hr hx
    refine ⟨hm, ?_⟩
    change representative (quotientMap x) ∈ Metric.ball cubeCenter r
    rwa [representative_quotientMap_of_mem hm]

lemma volume_cubeBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (cubeBall r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeBall r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeBall r)), inter_comm,
    cubeBall_lift hr1, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ r^3), ENNReal.ofReal_pow hr0]

lemma radialCore_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialCore := by
  exact radialBump.contDiff.mul (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma radialCore_compactSupport : HasCompactSupport radialCore :=
  radialBump.hasCompactSupport.mul_right

lemma radialCore_tsupport : tsupport radialCore ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hs : x ∈ tsupport (radialBump : Cover → ℝ) := tsupport_mul_subset_left hx
  rw [radialBump.tsupport_eq] at hs
  have hnorm : ‖x - cubeCenter‖ ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, radialBump] using hs
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans hnorm
  change ‖x i - (1 / 2 : ℝ)‖ ≤ 1 / 3 at hb
  rw [Real.norm_eq_abs, abs_le] at hb
  constructor <;> linarith

lemma radialSquared_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialSquared :=
  contDiff_const.sub (latticePeriodize_contDiff radialCore_contDiff radialCore_compactSupport)

lemma radialSquared_periodic (n : Fin 3 → ℤ) (x : Cover) :
    radialSquared (x + latticeVector n) = radialSquared x := by
  simp only [radialSquared, latticePeriodize_periodic]

lemma radialSquared_eq_on_cube {x : Cover} (hx : x ∈ fundamentalCube) :
    radialSquared x = 1 - radialBump x * (1 - ‖x - cubeCenter‖ ^ 2) := by
  unfold radialSquared
  rw [(latticePeriodize_eventuallyEq radialCore_compactSupport radialCore_tsupport
    (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).eq_of_nhds]
  rfl

lemma radialSquared_eventuallyEq_norm_sq {x : Cover} (hx : ‖x - cubeCenter‖ < 1 / 4) :
    radialSquared =ᶠ[𝓝 x] (fun y ↦ ‖y - cubeCenter‖ ^ 2) := by
  have hc : x ∈ fundamentalCube := coverBall_subset_cube (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have he := latticePeriodize_eventuallyEq radialCore_compactSupport radialCore_tsupport
    (fun i ↦ ⟨(hc i).1, (hc i).2.le⟩)
  have hb := radialBump.eventuallyEq_one_of_mem_ball
    (show x ∈ Metric.ball cubeCenter radialBump.rIn by
      simpa only [Metric.mem_ball, dist_eq_norm, radialBump] using hx)
  filter_upwards [he, hb] with y hy hby
  simp only [radialSquared, hy, radialCore, hby, Pi.one_apply, one_mul, sub_sub_cancel]

lemma radialSquared_sublevel_iff {x : Cover} (hx : x ∈ fundamentalCube)
    {t : ℝ} (ht : t ≤ 1 / 16) :
    radialSquared x < t ↔ ‖x - cubeCenter‖ ^ 2 < t := by
  rw [radialSquared_eq_on_cube hx]
  have hn := norm_nonneg (x - cubeCenter)
  have hb0 : 0 ≤ radialBump x := radialBump.nonneg
  have hb1 : radialBump x ≤ 1 := radialBump.le_one
  have he (h : ‖x - cubeCenter‖ ^ 2 < 1 / 16) : radialBump x = 1 := by
    apply radialBump.one_of_mem_closedBall
    change dist x cubeCenter ≤ 1 / 4
    rw [dist_eq_norm]
    nlinarith
  constructor
  · intro hh
    by_cases h : ‖x - cubeCenter‖ ^ 2 < 1 / 16
    · rw [he h, one_mul, sub_sub_cancel] at hh
      exact hh
    · have hh' : 1 / 16 ≤ ‖x - cubeCenter‖ ^ 2 := le_of_not_gt h
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hh')]
  · intro hh
    rw [he (hh.trans_le ht), one_mul, sub_sub_cancel]
    exact hh

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

lemma sublevelRegion_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) :
    sublevelRegion radialSquared (r ^ 2) = cubeBall r := by
  ext z
  change radialSquared (representative z) < r ^ 2 ↔
    dist (representative z) cubeCenter < r
  rw [radialSquared_sublevel_iff (representative_mem_fundamentalCube _) (by nlinarith), dist_eq_norm]
  exact sq_lt_sq₀ (norm_nonneg _) hr

lemma norm_gradient_radialSquared_of_mem_cube {x : Cover} (hx : x ∈ fundamentalCube)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (hxt : radialSquared x < r ^ 2) :
    ‖gradient radialSquared x‖ ≤ 2 * r := by
  have hnormsq := (radialSquared_sublevel_iff hx (by nlinarith)).1 hxt
  have hnorm : ‖x - cubeCenter‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr).mp hnormsq
  rw [norm_gradient_eq_norm_fderiv,
    (radialSquared_eventuallyEq_norm_sq (hnorm.trans_le hsmall)).fderiv_eq]
  have he : (fun y : Cover ↦ ‖y - cubeCenter‖ ^ 2) =
      (fun y : Cover ↦ ‖y + -cubeCenter‖ ^ 2) := by simp only [sub_eq_add_neg]
  rw [he]
  have hf : fderiv ℝ (fun y : Cover ↦ ‖y + -cubeCenter‖ ^ 2) x =
      fderiv ℝ (fun y : Cover ↦ ‖y‖ ^ 2) (x + -cubeCenter) := by
    convert! fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : Cover ↦ ‖y‖ ^ 2) (x := x) (-cubeCenter) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hf, fderiv_norm_sq_apply, two_smul]
  calc
    _ ≤ ‖innerSL ℝ (x + -cubeCenter)‖ + ‖innerSL ℝ (x + -cubeCenter)‖ := norm_add_le _ _
    _ = 2 * ‖x - cubeCenter‖ := by rw [innerSL_apply_norm]; simp only [sub_eq_add_neg]; ring
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left hnorm.le (by norm_num)

lemma norm_gradient_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (x : Cover)
    (hxt : radialSquared x < r ^ 2) : ‖gradient radialSquared x‖ ≤ 2 * r := by
  have he := periodic_representative radialSquared_periodic x
  have hg := periodic_representative (f := gradient radialSquared)
    (fun n y ↦ gradient_periodic radialSquared_periodic n y) x
  rw [← hg]
  exact norm_gradient_radialSquared_of_mem_cube (representative_mem_fundamentalCube _) hr hsmall (by rwa [he])

end CubicTorus

namespace CubicTorus

lemma dist_representative_cubeCenter (x : Torus) :
    dist (representative x) cubeCenter = dist x (quotientMap cubeCenter) := by
  rw [dist_eq_norm, dist_eq_norm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property
  have hxi : ‖((representative x i - (1 / 2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1 / 2 : ℝ)| := by
    apply (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
    change |((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ) - (1 / 2 : ℝ)| ≤ |(1 : ℝ)| / 2
    norm_num only [abs_one] at *
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hq : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i := by
    exact congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [PiLp.sub_apply, cubeCenter, quotientMap, PiLp.toLp_apply,
    Real.norm_eq_abs, map_sub, hq] using hxi.symm

lemma cubeBall_eq_metricBall (r : ℝ) :
    cubeBall r = Metric.ball (quotientMap cubeCenter) r := by
  ext x
  change dist (representative x) cubeCenter < r ↔ dist x (quotientMap cubeCenter) < r
  rw [dist_representative_cubeCenter]

lemma centeredBall_eq_cubeBall_preimage (r : ℝ) :
    Metric.ball (0 : Torus) r =
      (fun x ↦ x + quotientMap cubeCenter) ⁻¹' cubeBall r := by
  rw [cubeBall_eq_metricBall]
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]

lemma volume_centeredBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (Metric.ball (0 : Torus) r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [centeredBall_eq_cubeBall_preimage,
    volume_translation (measurableSet_cubeBall r).nullMeasurableSet, volume_cubeBall hr0 hr1]

lemma volume_torusBall (a : Torus) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (Metric.ball a r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  have he : Metric.ball a r = (fun z : Torus ↦ z + -a) ⁻¹' Metric.ball 0 r := by
    ext z
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero]
  rw [he, volume_translation Metric.isOpen_ball.measurableSet.nullMeasurableSet, volume_centeredBall hr0 hr1]

lemma localRadialSquared_contDiff (a : Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (localRadialSquared a) :=
  radialSquared_contDiff.comp (contDiff_id.add contDiff_const)

lemma localRadialSquared_periodic (a : Torus) (n : Fin 3 → ℤ) (x : Cover) :
    localRadialSquared a (x + latticeVector n) = localRadialSquared a x := by
  unfold localRadialSquared
  rw [show x + latticeVector n + representative (quotientMap cubeCenter - a) =
    (x + representative (quotientMap cubeCenter - a)) + latticeVector n by abel]
  exact radialSquared_periodic n _

lemma sublevelRegion_localRadialSquared (a : Torus) {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 4) :
    sublevelRegion (localRadialSquared a) (r ^ 2) = Metric.ball a r := by
  ext z
  have hrep := periodic_representative radialSquared_periodic
    (representative z + representative (quotientMap cubeCenter - a))
  rw [quotientMap_add, quotientMap_representative, quotientMap_representative] at hrep
  change radialSquared (representative z + representative (quotientMap cubeCenter - a)) < r ^ 2 ↔ _
  rw [← hrep]
  change z + (quotientMap cubeCenter - a) ∈ sublevelRegion radialSquared (r ^ 2) ↔ _
  rw [sublevelRegion_radialSquared hr hs, cubeBall_eq_metricBall]
  simp only [Metric.mem_ball, dist_eq_norm]
  rw [show z + (quotientMap cubeCenter - a) - quotientMap cubeCenter = z - a by abel]

lemma norm_gradient_localRadialSquared (a : Torus) {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 4)
    (x : Cover) (hx : localRadialSquared a x < r ^ 2) :
    ‖gradient (localRadialSquared a) x‖ ≤ 2 * r := by
  rw [norm_gradient_eq_norm_fderiv]
  have he : fderiv ℝ (localRadialSquared a) x =
      fderiv ℝ radialSquared (x + representative (quotientMap cubeCenter - a)) := by
    convert! fderiv_comp_add_right (𝕜 := ℝ) (f := radialSquared) (x := x)
      (representative (quotientMap cubeCenter - a)) using 1
    all_goals try with_reducible_and_instances rfl
  rw [he, ← norm_gradient_eq_norm_fderiv]
  exact norm_gradient_radialSquared hr hs _ hx

lemma sublevelVolume_localRadialSquared_le (E : Set Torus) (a : Torus) {r t : ℝ}
    (hr : 0 ≤ r) (hs : r ≤ 1 / 4) (ht : t ≤ r ^ 2) :
    sublevelVolume E (localRadialSquared a) t ≤ (2 * r) ^ 3 := by
  calc
    _ ≤ sublevelVolume E (localRadialSquared a) (r ^ 2) := sublevelVolume_mono E _ ht
    _ ≤ torusVolume.real (Metric.ball a r) := by
      unfold sublevelVolume
      rw [sublevelRegion_localRadialSquared a hr hs]
      exact measureReal_mono inter_subset_right
    _ = r ^ 3 * (Real.pi * 4 / 3) := by
      rw [Measure.real_def, volume_torusBall a hr (by linarith), ENNReal.toReal_ofReal (by positivity)]
    _ ≤ (2 * r) ^ 3 := by nlinarith [Real.pi_lt_four, pow_nonneg hr 3]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace CubicTorus

theorem monotone_density_root_lower {m : ℝ → ℝ} (hm : Monotone m)
    (hm0 : ∀ x, 0 ≤ m x) {T a b c : ℝ} (hT : 0 < T) (hb : 0 ≤ b) (hc : 0 < c)
    (hab : b * a ≤ 1 / 2)
    (hpos : ∀ x ∈ Ioc 0 T, 0 < m x)
    (hroot : ∀ x ∈ Ioc 0 T, m x ^ (1 / 3 : ℝ) ≤ a)
    (hode : ∀ᵐ x : ℝ, x ∈ Ioo 0 T →
      m x ^ (2 / 3 : ℝ) ≤ b * m x + c * deriv m x) :
    T / (6 * c) ≤ m T ^ (1 / 3 : ℝ) := by
  let g : ℝ → ℝ := fun x ↦ m x ^ (1 / 3 : ℝ)
  have hg : Monotone g := fun x y hxy ↦ Real.rpow_le_rpow (hm0 x) (hm hxy) (by norm_num)
  have hderiv : ∀ᵐ x : ℝ, x ∈ Ioo 0 T → 1 / (6 * c) ≤ deriv g x := by
    filter_upwards [hm.ae_differentiableAt, hode] with x hmx hode
    intro hx
    have hmx0 : 0 < m x := hpos x ⟨hx.1, hx.2.le⟩
    have hp : 0 < m x ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hmx0 _
    have hgderiv : HasDerivAt g ((1 / 3 : ℝ) * m x ^ (-2 / 3 : ℝ) * deriv m x) x := by
      convert! (Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ)) (Or.inl hmx0.ne')).comp x hmx.hasDerivAt using 1
      all_goals try with_reducible_and_instances rfl
      norm_num [g, Function.comp_def]
    have hpower : m x ^ (1 / 3 : ℝ) * m x ^ (2 / 3 : ℝ) = m x := by
      rw [← Real.rpow_add hmx0]
      norm_num
    have hpower' : m x ^ (-2 / 3 : ℝ) * m x ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hmx0]
      norm_num
    have he : deriv g x * m x ^ (2 / 3 : ℝ) = deriv m x / 3 := by
      rw [hgderiv.deriv]
      calc
        _ = (m x ^ (-2 / 3 : ℝ) * m x ^ (2 / 3 : ℝ)) * deriv m x / 3 := by ring
        _ = _ := by rw [hpower']; ring
    have hbr : b * m x ^ (1 / 3 : ℝ) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (hroot x ⟨hx.1, hx.2.le⟩) hb).trans hab
    have hbm : b * m x ≤ m x ^ (2 / 3 : ℝ) / 2 := by
      have hh := mul_le_mul_of_nonneg_right hbr hp.le
      rw [mul_assoc, hpower] at hh
      linarith
    have hineq := hode hx
    have hbound : (1 - 6 * c * deriv g x) * m x ^ (2 / 3 : ℝ) ≤ 0 := by
      nlinarith [he]
    have hbound' := nonpos_of_mul_nonpos_left hbound hp
    apply (div_le_iff₀ (by positivity : 0 < 6 * c)).2
    nlinarith
  have hlower (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) :
      (T - s) / (6 * c) ≤ g T := by
    have hgi : IntervalIntegrable (deriv g) volume s T := (hg.monotoneOn _).intervalIntegrable_deriv
    have hint := (hg.monotoneOn _).intervalIntegral_deriv_mem_uIcc (a := s) (b := T)
    rw [uIcc_of_le (sub_nonneg.mpr (hg hsT))] at hint
    have haeb : ∀ᵐ x ∂volume.restrict (Icc s T), 1 / (6 * c) ≤ deriv g x := by
      filter_upwards [ae_restrict_of_ae hderiv,
        ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ T} = 0))] with x hd hx hne
      exact hd ⟨hs.trans_le hx.1, hx.2.lt_of_ne hne⟩
    have hil := intervalIntegral.integral_mono_ae_restrict hsT
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ 1 / (6 * c)) volume s T)
      hgi haeb
    rw [intervalIntegral.integral_const, smul_eq_mul] at hil
    simp only [mul_one_div] at hil
    have hgs : 0 ≤ g s := Real.rpow_nonneg (hm0 s) _
    linarith [hint.2]
  let s : ℕ → ℝ := fun n ↦ T / ((n : ℝ) + 1)
  have hs (n) : 0 < s n := by dsimp [s]; positivity
  have hsT (n) : s n ≤ T := by
    dsimp [s]
    exact div_le_self hT.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := T)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, mul_one_div] using hh
  have hlim : Tendsto (fun n ↦ (T - s n) / (6 * c)) atTop (𝓝 (T / (6 * c))) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hs0).div_const (6 * c)
  exact le_of_tendsto_of_tendsto' hlim tendsto_const_nhds (fun n ↦ hlower (s n) (hs n) (hsT n))

theorem monotone_density_lower {m : ℝ → ℝ} (hm : Monotone m)
    (hm0 : ∀ x, 0 ≤ m x) {T a b c : ℝ} (hT : 0 < T) (hb : 0 ≤ b) (hc : 0 < c)
    (hab : b * a ≤ 1 / 2)
    (hpos : ∀ x ∈ Ioc 0 T, 0 < m x)
    (hroot : ∀ x ∈ Ioc 0 T, m x ^ (1 / 3 : ℝ) ≤ a)
    (hode : ∀ᵐ x : ℝ, x ∈ Ioo 0 T →
      m x ^ (2 / 3 : ℝ) ≤ b * m x + c * deriv m x) :
    (T / (6 * c)) ^ 3 ≤ m T := by
  have hh := monotone_density_root_lower hm hm0 hT hb hc hab hpos hroot hode
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ T / (6 * c)) hh 3
  have he : (m T ^ (1 / 3 : ℝ)) ^ 3 = m T := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow (hm0 T) (by norm_num : (3 : ℕ) ≠ 0)
  rwa [he] at hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

theorem isMinimizerAt_volume_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      (∀ s : ℝ, 0 < s → 0 < torusVolume.real (E ∩ Metric.ball a s)) →
      c * r ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a r) := by
  obtain ⟨η, C, K, hη, hC, hK, hode⟩ := isMinimizerAt_sublevel_density_inequality hV hE hmin
  let R := min (1 / 4 : ℝ) (min (η / 16) (1 / (48 * (C + 1))))
  let c := (1 / (288 * K)) ^ 3
  have hR : 0 < R := by dsimp [R]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨R, c, hR, hc, ?_⟩
  intro a r hr hrR hsupport
  have hrsmall : r ≤ 1 / 4 := hrR.trans (min_le_left _ _)
  have hrη : r ≤ η / 16 := hrR.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrC : r ≤ 1 / (48 * (C + 1)) := hrR.trans ((min_le_right _ _).trans (min_le_right _ _))
  let q := localRadialSquared a
  let m := sublevelVolume E q
  have hm : Monotone m := sublevelVolume_mono E q
  have hm0 (t) : 0 ≤ m t := ENNReal.toReal_nonneg
  have hupper {t : ℝ} (ht : t ≤ r ^ 2) : m t ≤ (2 * r) ^ 3 :=
    sublevelVolume_localRadialSquared_le E a hr.le hrsmall ht
  have hroot {t : ℝ} (ht : t ≤ r ^ 2) : m t ^ (1 / 3 : ℝ) ≤ 2 * r := by
    have hh := Real.rpow_le_rpow (hm0 t) (hupper ht) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have he : ((2 * r) ^ 3) ^ (1 / 3 : ℝ) = 2 * r := by
      simpa only [one_div, Nat.cast_ofNat] using
        Real.pow_rpow_inv_natCast (by positivity : 0 ≤ 2 * r) (by norm_num : (3 : ℕ) ≠ 0)
    rwa [he] at hh
  have heta {t : ℝ} (ht : t ≤ r ^ 2) : m t < η := by
    have hrpow : r ^ 3 ≤ r := by
      have hr1 : r ≤ 1 := by linarith
      have := pow_le_pow_left₀ hr.le hr1 2
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr this)]
    have hu := hupper ht
    nlinarith
  have hhalf {t : ℝ} (ht : t ≤ r ^ 2) : m t ≤ 1 / 2 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * r)
      (show 2 * r ≤ 1 / 2 by linarith) 3
    norm_num at hp
    linarith [hupper ht]
  have hpos (t : ℝ) (ht : t ∈ Ioc 0 (r ^ 2)) : 0 < m t := by
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
    have hsr : Real.sqrt t ≤ r := (Real.sqrt_le_iff).2 ⟨hr.le, ht.2⟩
    have he : m t = torusVolume.real (E ∩ Metric.ball a (Real.sqrt t)) := by
      change torusVolume.real (E ∩ sublevelRegion q t) = _
      have hh := sublevelRegion_localRadialSquared a hs0.le (hsr.trans hrsmall)
      rw [Real.sq_sqrt ht.1.le] at hh
      rw [hh]
    rw [he]
    exact hsupport _ hs0
  have haeb : ∀ᵐ t : ℝ, t ∈ Ioo 0 (r ^ 2) →
      m t ^ (2 / 3 : ℝ) ≤ 12 * C * m t + (48 * K * r) * deriv m t := by
    filter_upwards [hode q (localRadialSquared_contDiff a) (localRadialSquared_periodic a)] with t ht
    intro htr
    have hgrad (x : Cover) (hx : q x < t) : ‖gradient q x‖ ≤ 2 * r :=
      norm_gradient_localRadialSquared a hr.le hrsmall x (hx.trans htr.2)
    have hh := ht (2 * r) hgrad (heta htr.2.le) (hhalf htr.2.le)
    change m t ^ (2 / 3 : ℝ) ≤ 12 * C * m t + 24 * K * (2 * r) * deriv m t at hh
    nlinarith [hh]
  have hab : (12 * C) * (2 * r) ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 48 * (C + 1))).1 hrC
    nlinarith
  have hlower := monotone_density_lower hm hm0 (sq_pos_of_pos hr)
    (show 0 ≤ 12 * C by positivity) (show 0 < 48 * K * r by positivity) hab hpos
    (fun t ht ↦ hroot ht.2) haeb
  have he : (r ^ 2 / (6 * (48 * K * r))) ^ 3 = c * r ^ 3 := by
    dsimp only [c]
    field_simp
    ring
  rw [he] at hlower
  change _ ≤ torusVolume.real (E ∩ sublevelRegion (localRadialSquared a) (r ^ 2)) at hlower
  rwa [sublevelRegion_localRadialSquared a hr.le hrsmall] at hlower

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma mem_volumeSupport_iff (E : Set Torus) (a : Torus) :
    a ∈ volumeSupport E ↔ ∀ r : ℝ, 0 < r →
      0 < torusVolume.real (E ∩ Metric.ball a r) := by
  rw [volumeSupport, Metric.nhds_basis_ball.mem_measureSupport]
  simp only [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_comm]
  exact forall_congr' fun r ↦ imp_congr_right fun _ ↦
    (ENNReal.toReal_pos_iff.trans (and_iff_left (measure_lt_top _ _))).symm

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

theorem isMinimizerAt_two_sided_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ a ∈ volumeSupport E ∩ volumeSupport Eᶜ,
      ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a r) ∧
      c * r ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a r) := by
  obtain ⟨R₁, c₁, hR₁, hc₁, hd₁⟩ := isMinimizerAt_volume_density hV hE hmin
  have hVc : 1 - V ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2], by linarith [hV.1]⟩
  obtain ⟨R₂, c₂, hR₂, hc₂, hd₂⟩ := isMinimizerAt_volume_density hVc hE.compl
    ((isMinimizerAt_compl ⟨hV.1.le, hV.2.le⟩).2 hmin)
  refine ⟨min R₁ R₂, min c₁ c₂, lt_min hR₁ hR₂, lt_min hc₁ hc₂, ?_⟩
  intro a ha r hr hrR
  constructor
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (hd₁ a r hr (hrR.trans (min_le_left _ _)) ((mem_volumeSupport_iff E a).1 ha.1))
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans
      (hd₂ a r hr (hrR.trans (min_le_right _ _)) ((mem_volumeSupport_iff Eᶜ a).1 ha.2))

instance torusVolume_doubling : IsUnifLocDoublingMeasure torusVolume := by
  refine ⟨27, ?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))] with r hr hs a
  have hrpos : 0 < r := hr
  change r < 1 / 6 at hs
  calc
    torusVolume (Metric.closedBall a (2 * r)) ≤ torusVolume (Metric.ball a (3 * r)) :=
      measure_mono (Metric.closedBall_subset_ball (by linarith))
    _ = (27 : ℝ≥0∞) * torusVolume (Metric.ball a r) := by
      rw [volume_torusBall a (by positivity) (by linarith),
        volume_torusBall a hrpos.le (by linarith), ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 27)]
      congr 1
      ring
    _ ≤ (27 : ℝ≥0∞) * torusVolume (Metric.closedBall a r) := by
      gcongr
      exact Metric.ball_subset_closedBall

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

lemma volumeSupport_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    volumeSupport E = volumeSupport F := by
  unfold volumeSupport
  rw [Measure.restrict_congr_set h]

lemma volumeSupport_eq_closure {E : Set Torus} (hE : IsOpen E) :
    volumeSupport E = closure E := by
  apply Subset.antisymm
  · exact Measure.support_restrict_subset.trans inter_subset_left
  · apply closure_minimal _ (isClosed_volumeSupport E)
    have hh := Measure.interior_inter_support (μ := torusVolume) (s := E)
    change E ⊆ (torusVolume.restrict E).support
    simpa only [hE.interior_eq, Measure.support_eq_univ, inter_univ] using hh

lemma isMinimizerAt_closure_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    closure (openRepresentative E) = volumeSupport E := by
  rw [← volumeSupport_eq_closure (isOpen_openRepresentative E)]
  exact volumeSupport_congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin)

lemma isMinimizerAt_frontier_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    frontier (openRepresentative E) = volumeSupport E ∩ volumeSupport Eᶜ := by
  rw [frontier, (isOpen_openRepresentative E).interior_eq,
    isMinimizerAt_closure_openRepresentative hV hE hmin]
  simp only [openRepresentative, sdiff_eq, compl_compl]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma integral_spatialNormalMeasure (μ : FiniteMeasure NormalBundle) {f : Torus → ℝ}
    (hf : Measurable f) :
    (∫ x, f x ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z, f (normalProjection z) ∂(μ : Measure NormalBundle) := by
  change (∫ x, f x ∂Measure.map normalProjection (μ : Measure NormalBundle)) = _
  exact integral_map normalProjection_continuous.measurable.aemeasurable hf.aestronglyMeasurable

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

lemma norm_quotientMap_le (x : Cover) : ‖quotientMap x‖ ≤ ‖x‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) QuotientAddGroup.norm_mk_le_norm 2

lemma quotientMap_shortestLift (x : Torus) : quotientMap (shortestLift x) = x := by
  simp only [shortestLift, quotientMap_sub, quotientMap_representative, add_sub_cancel_right]

lemma norm_shortestLift (x : Torus) : ‖shortestLift x‖ = ‖x‖ := by
  have hh := dist_representative_cubeCenter (x + quotientMap cubeCenter)
  simpa only [dist_eq_norm, add_sub_cancel_right, shortestLift] using hh

lemma smoothApprox_zero_outside_ball {g : Cover → ℝ} {a : Torus} {r s : ℝ}
    (hz : ∀ x, quotientMap x ∉ Metric.ball a r → g x = 0) (n : ℕ)
    (hn : (mollifier n).rOut ≤ s) {x : Cover}
    (hx : quotientMap x ∉ Metric.ball a (r + s)) : smoothApprox g n x = 0 := by
  rw [smoothApprox, convolution_def]
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro y
  by_cases hy : (mollifier n).normed volume y = 0
  · simp [hy]
  have hyn : ‖y‖ < (mollifier n).rOut := by
    have hh : y ∈ Function.support ((mollifier n).normed volume) := hy
    rw [(mollifier n).support_normed_eq] at hh
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hxy : quotientMap (x - y) ∉ Metric.ball a r := by
    intro hmem
    apply hx
    change dist (quotientMap x) a < r + s
    have ht := dist_triangle (quotientMap x) (quotientMap (x - y)) a
    have he : dist (quotientMap x) (quotientMap (x - y)) = ‖quotientMap y‖ := by
      rw [dist_eq_norm, quotientMap_sub, sub_sub_cancel]
    rw [he] at ht
    have hm : dist (quotientMap (x - y)) a < r := hmem
    linarith [norm_quotientMap_le y]
  simp [ContinuousLinearMap.lsmul_apply, hz (x - y) hxy]

end CubicTorus

end
end

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma isNormalMeasure_compl {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsNormalMeasure Eᶜ (μ.map reverseNormal) := by
  constructor
  · have hm : ((μ.map reverseNormal).mass : ℝ) = (μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal
        (Measure.map_apply continuous_reverseNormal.measurable MeasurableSet.univ
          (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ, FiniteMeasure.mass, FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map, Measure.real, ENNReal.toReal] using hh
    rw [hm, hμ.1, perimeter_compl hE.nullMeasurableSet]
  · intro F hF
    change (∫ z, normalTest F hF.1.continuous z
      ∂Measure.map reverseNormal (μ : Measure NormalBundle)) = _
    rw [integral_map continuous_reverseNormal.measurable.aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable]
    change (∫ z, ⟪-(z.2 : Cover), F (z.1 : Cover)⟫ ∂(μ : Measure NormalBundle)) = _
    simp_rw [inner_neg_left, integral_neg]
    rw [integral_divergence_compl hE.nullMeasurableSet hF, ← hμ.2 F hF]
    rfl

lemma spatialNormalMeasure_reverse (μ : FiniteMeasure NormalBundle) :
    spatialNormalMeasure (μ.map reverseNormal) = spatialNormalMeasure μ := by
  apply Subtype.ext
  change Measure.map normalProjection (Measure.map reverseNormal (μ : Measure NormalBundle)) = _
  rw [Measure.map_map normalProjection_continuous.measurable continuous_reverseNormal.measurable]
  rfl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVTangentialBlowup
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma normalOscillation_nonneg (σ : FiniteMeasure Torus) (N : Torus → Cover)
    (c : Torus) (n : Cover) (r : ℝ) : 0 ≤ normalOscillation σ N c n r :=
  div_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (sq_nonneg _)

lemma integrable_norm_sub_normal {σ : FiniteMeasure Torus} {N : Torus → Cover}
    (hN : Measurable N) (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) (n : Cover) :
    Integrable (fun x ↦ ‖N x - n‖) (σ : Measure Torus) := by
  apply Integrable.of_bound (hN.sub_const n).norm.aestronglyMeasurable (1 + ‖n‖)
  filter_upwards [hn] with x hx
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  simpa only [hx] using norm_sub_le (N x) n

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

lemma smoothApprox_nonneg {g : Cover → ℝ} (hg : ∀ x, 0 ≤ g x) (k : ℕ) (x : Cover) :
    0 ≤ smoothApprox g k x := by
  rw [smoothApprox, convolution_def]
  exact integral_nonneg fun y ↦ mul_nonneg ((mollifier k).nonneg_normed y) (hg _)

lemma flux_ordered_lower_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    (hf0 : ∀ x, 0 ≤ f x)
    {B : Set Torus} (hB : MeasurableSet B) (hz : ∀ x, quotientMap x ∉ B → f x = 0)
    {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in B, ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun x ↦ f x • a) x := by
  have hfa := hf.smul_const a
  rw [← normalMeasure_flux hμ hfa (fun m x ↦ by rw [hp])
    (show 0 < ‖a‖ + 1 by positivity) (fun x ↦ by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg a) (hb x)).trans (by linarith))]
  let g : Torus → ℝ := B.indicator (fun x ↦ -(‖a‖ * ‖N x - n‖))
  have hg : Measurable g := (((hN.sub_const n).norm.const_mul _).neg).indicator hB
  have hi : Integrable g (spatialNormalMeasure μ : Measure Torus) :=
    (((integrable_norm_sub_normal hN hn n).const_mul _).neg).indicator hB
  have him : Integrable (fun z : NormalBundle ↦ g (normalProjection z))
      (μ : Measure NormalBundle) :=
    (integrable_map_measure hg.aestronglyMeasurable
      normalProjection_continuous.measurable.aemeasurable).mp hi
  have hnt := (normalTest _ hfa.continuous).continuous.integrable_of_hasCompactSupport
    (μ := (μ : Measure NormalBundle)) (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono_ae him hnt (show ∀ᵐ z ∂(μ : Measure NormalBundle),
      g (normalProjection z) ≤ normalTest (fun x ↦ f x • a) hfa.continuous z from by
    filter_upwards [hpolar] with z hz'
    by_cases hzB : normalProjection z ∈ B
    · simp only [g, indicator_of_mem hzB, normalTest, ContinuousMap.coe_mk,
        real_inner_smul_right]
      change -(‖a‖ * ‖N (quotientMap z.1) - n‖) ≤ f z.1 * ⟪(z.2 : Cover), a⟫
      rw [← hz']
      have hn' := (abs_le.mp (abs_real_inner_le_norm (N (quotientMap z.1) - n) a)).1
      rw [inner_sub_left] at hn'
      have hf1 := (le_abs_self (f z.1)).trans (hb z.1)
      have hnonneg := mul_nonneg (norm_nonneg a) (norm_nonneg (N (quotientMap z.1) - n))
      have hm := mul_le_mul_of_nonneg_left (show -(‖a‖ * ‖N (quotientMap z.1) - n‖) ≤
        ⟪N (quotientMap z.1), a⟫ by nlinarith) (hf0 z.1)
      nlinarith
    · simp [g, hzB, normalTest, hz z.1 hzB])
  rw [← integral_spatialNormalMeasure μ hg] at hh
  simpa only [g, integral_indicator hB, integral_neg, integral_const_mul] using hh

theorem smooth_test_ordered_translation_lower_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    (hf0 : ∀ x, 0 ≤ f x)
    {c : Torus} {r : ℝ} (hz : ∀ x, quotientMap x ∉ Metric.ball c r → f x = 0)
    {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in Metric.ball c (r + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x) := by
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
  have ht (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      -(‖a‖ * ∫ x in Metric.ball c (r + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a := by
    let g : Cover → ℝ := fun x ↦ f (x + t • a)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
    have hp' : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp [g]
      rw [add_right_comm, hp]
    have hzero (x : Cover) (hx : quotientMap x ∉ Metric.ball c (r + ‖a‖)) : g x = 0 := by
      have hm : quotientMap (x + t • a) ∉ Metric.ball c r := by
        intro hx'
        apply hx
        change dist (quotientMap x) c < r + ‖a‖
        have hh := dist_triangle (quotientMap x) (quotientMap (x + t • a)) c
        have he : dist (quotientMap x) (quotientMap (x + t • a)) = ‖quotientMap (t • a)‖ := by
          rw [dist_eq_norm, quotientMap_add, sub_add_cancel_left, norm_neg]
        rw [he] at hh
        have hs : ‖t • a‖ ≤ ‖a‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1.le]
          exact mul_le_of_le_one_left (norm_nonneg a) ht.2
        have hx'' : dist (quotientMap (x + t • a)) c < r := hx'
        linarith [norm_quotientMap_le (t • a)]
      simp [g, hz _ hm]
    have hh := flux_ordered_lower_bound hμ hN hpolar hn hg hp' (fun x ↦ hb _)
      (fun x ↦ hf0 _) Metric.isOpen_ball.measurableSet hzero ha
    simpa only [divergence_smul_const (hg.differentiable (by simp)).differentiableAt,
      g, fderiv_comp_add_right] using hh
  calc
    _ = ∫ t in Ioc (0 : ℝ) 1, -(‖a‖ * ∫ x in Metric.ball c (r + ‖a‖),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) := by simp
    _ ≤ ∫ t in Ioc (0 : ℝ) 1, ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f (x + t • a) a := by
      apply integral_mono_ae (integrable_const _) hi.integral_prod_right
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht'
      exact ht t ht'
    _ = _ := by rw [← integral_integral_swap hi]; simp_rw [hFTC]

theorem measurable_test_ordered_translation_lower_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) (hg0 : ∀ x, 0 ≤ g x) {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, quotientMap x ∉ Metric.ball c r → g x = 0) {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in Metric.ball c (r + s + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x) := by
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
  apply ge_of_tendsto hi
  filter_upwards [mollifier_rOut_tendsto.eventually (ge_mem_nhds hs)] with n hnr
  exact smooth_test_ordered_translation_lower_bound hμ hN hpolar hn
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n)
    (smoothApprox_nonneg hg0 n) (fun x hx ↦ smoothApprox_zero_outside_ball hz n hnr hx) ha

lemma torus_test_ordered_translation_lower_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {g : Torus → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) (hg0 : ∀ x, 0 ≤ g x)
    {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, x ∉ Metric.ball c r → g x = 0) {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in Metric.ball c (r + s + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in E, (g (x + quotientMap a) - g x) ∂torusVolume := by
  rw [setIntegral_lift_measurable (f := fun x => g (x + quotientMap a) - g x)
    ((hg.comp (measurable_id.add_const _)).sub hg) hE]
  have hp : ∀ n x, g (quotientMap (x + latticeVector n)) = g (quotientMap x) := by
    intro n x
    rw [quotientMap_add, quotientMap_latticeVector, add_zero]
  simpa only [Function.comp_def, quotientMap_add] using
    measurable_test_ordered_translation_lower_bound hμ hN hpolar hn (hg.comp measurable_quotientMap) hp
      (fun x => hb (quotientMap x)) (fun x ↦ hg0 _) hs (fun x hx ↦ hz _ hx) ha

lemma orderDefect_nonneg (E : Set Torus) (a x : Torus) : 0 ≤ orderDefect E a x := by
  rcases characteristic_dichotomy E x with h | h <;>
    rcases characteristic_dichotomy E (x - a) with h' | h' <;> simp [orderDefect, h, h']

lemma orderDefect_bound (E : Set Torus) (a x : Torus) : |orderDefect E a x| ≤ 1 := by
  rcases characteristic_dichotomy E x with h | h <;>
    rcases characteristic_dichotomy E (x - a) with h' | h' <;> simp [orderDefect, h, h']

lemma measurable_orderDefect {E : Set Torus} (hE : MeasurableSet E) (a : Torus) :
    Measurable (orderDefect E a) :=
  (measurable_characteristic hE).mul (measurable_const.sub
    ((measurable_characteristic hE).comp (measurable_id.sub_const _)))

theorem characteristic_ordered_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (c : Torus) {r s : ℝ} (hs : 0 < s) {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    (∫ x in Metric.ball c r, orderDefect E (quotientMap a) x ∂torusVolume) ≤
      ‖a‖ * ∫ x in Metric.ball c (r + s + ‖a‖),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := by
  let g : Torus → ℝ := (Metric.ball c r).indicator (orderDefect E (quotientMap a))
  have hg : Measurable g := (measurable_orderDefect hE _).indicator Metric.isOpen_ball.measurableSet
  have hb (x) : |g x| ≤ 1 := by
    by_cases hx : x ∈ Metric.ball c r
    · simpa only [g, indicator_of_mem hx] using orderDefect_bound E (quotientMap a) x
    · simp [g, hx]
  have hg0 : ∀ x, 0 ≤ g x := indicator_nonneg fun _ _ ↦ orderDefect_nonneg _ _ _
  have hz (x : Torus) (hx : x ∉ Metric.ball c r) : g x = 0 := indicator_of_notMem hx _
  have hh := torus_test_ordered_translation_lower_bound hE hμ hN hpolar hn hg hb hg0 hs hz ha
  rw [integral_difference_test hE hg hb] at hh
  have heq (x) : (characteristic E (x - quotientMap a) - characteristic E x) * g x =
      -((Metric.ball c r).indicator (orderDefect E (quotientMap a)) x) := by
    by_cases hx : x ∈ Metric.ball c r
    · simp only [g, indicator_of_mem hx]
      rcases characteristic_dichotomy E x with h | h <;>
        rcases characteristic_dichotomy E (x - quotientMap a) with h' | h' <;>
          simp [orderDefect, h, h']
    · simp [g, hx]
  simp_rw [heq] at hh
  rwa [integral_neg, integral_indicator Metric.isOpen_ball.measurableSet, neg_le_neg_iff] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

theorem ordered_volume_product_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {U W : Set Torus} (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUE : U ⊆ Eᶜ) (hWE : W ⊆ E) (c : Torus) {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 4)
    (hUB : U ⊆ Metric.ball c r) (hWB : W ⊆ Metric.ball c r) (n : Cover)
    (hordered : ∀ x ∈ U, ∀ z ∈ W, 0 ≤ ⟪n, shortestLift (z - x)⟫) :
    torusVolume.real U * torusVolume.real W ≤ 128 * r ^ 4 *
      ∫ x in Metric.ball c (4 * r), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := by
  let B := Metric.ball c r
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  let f : Torus × Torus → ℝ := fun z ↦ characteristic U (z.2 - z.1) * characteristic W z.2
  have hfm : Measurable f :=
    ((measurable_characteristic hU).comp (measurable_snd.sub measurable_fst)).mul
      ((measurable_characteristic hW).comp measurable_snd)
  have hfb (z : Torus × Torus) : |f z| ≤ 1 := by
    dsimp [f]
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound U _)).trans
      (characteristic_bound W _)
  have hfi : Integrable f (torusVolume.prod torusVolume) :=
    Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall hfb)
  let I : Torus → ℝ := fun a ↦ ∫ x, f (a, x) ∂torusVolume
  have hIi : Integrable I torusVolume := hfi.integral_prod_left
  have hIeq : (∫ a, I a ∂torusVolume) = torusVolume.real U * torusVolume.real W := by
    rw [show (∫ a, I a ∂torusVolume) = ∫ x, ∫ a, f (a, x) ∂torusVolume ∂torusVolume from
      integral_integral_swap hfi]
    have hinner (x : Torus) : (∫ a, f (a, x) ∂torusVolume) =
        torusVolume.real U * characteristic W x := by
      dsimp only [f]
      rw [integral_mul_const, integral_sub_left_eq_self, integral_characteristic hU.nullMeasurableSet]
      rfl
    simp_rw [hinner]
    rw [integral_const_mul, integral_characteristic hW.nullMeasurableSet]
    rfl
  have hIz (a : Torus) (ha : a ∉ Metric.ball 0 (2 * r)) : I a = 0 := by
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ W
    · by_cases hx' : x - a ∈ U
      · have hdist : ‖a‖ < 2 * r := by
          have hh := dist_triangle x c (x - a)
          have hxB : dist x c < r := (hWB hx)
          have hxB' : dist (x - a) c < r := (hUB hx')
          rw [dist_eq_norm, sub_sub_cancel] at hh
          rw [dist_comm c (x - a)] at hh
          linarith
        exact False.elim (ha (by simpa only [Metric.mem_ball, dist_zero_right] using hdist))
      · simp [f, characteristic, hx']
    · simp [f, characteristic, hx]
  let P := ∫ x in Metric.ball c (4 * r), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)
  have hPn : 0 ≤ P := integral_nonneg fun _ ↦ norm_nonneg _
  have hIbound (a : Torus) (ha : a ∈ Metric.ball 0 (2 * r)) : I a ≤ 2 * r * P := by
    have han : ‖a‖ < 2 * r := by simpa only [Metric.mem_ball, dist_zero_right] using ha
    by_cases hex : ∃ x : Torus, x ∈ W ∧ x - a ∈ U
    · obtain ⟨x₀, hx₀, hx₀'⟩ := hex
      have horder : 0 ≤ ⟪n, shortestLift a⟫ := by
        simpa only [sub_sub_cancel] using hordered (x₀ - a) hx₀' x₀ hx₀
      let g : Torus → ℝ := orderDefect E a
      have hgm : Measurable g := measurable_orderDefect hE a
      have hgb (x : Torus) : ‖g x‖ ≤ 1 := orderDefect_bound E a x
      have hgi : Integrable g torusVolume :=
        Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
      have hminor (x : Torus) : f (a, x) ≤ B.indicator g x := by
        by_cases hx : x ∈ W
        · by_cases hx' : x - a ∈ U
          · have hxE : x ∈ E := hWE hx
            have hxE' : x - a ∉ E := hUE hx'
            simp [f, characteristic, hx, hx', g, B, hWB hx, hxE, hxE', orderDefect]
          · simp only [f, characteristic, indicator_of_notMem hx', zero_mul]
            exact indicator_nonneg (fun _ _ ↦ orderDefect_nonneg _ _ _) _
        · simp only [f, characteristic, indicator_of_notMem hx, mul_zero]
          exact indicator_nonneg (fun _ _ ↦ orderDefect_nonneg _ _ _) _
      have hleft : I a ≤ ∫ x in B, g x ∂torusVolume := by
        rw [← integral_indicator hB]
        apply integral_mono _ (hgi.indicator hB) hminor
        exact Integrable.of_bound (hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
          (Eventually.of_forall fun x ↦ hfb (a, x))
      have htrans := characteristic_ordered_translation_bound hE hμ hN hpolar hn c (r := r) hr horder
      rw [norm_shortestLift, quotientMap_shortestLift] at htrans
      have hpmono : (∫ x in Metric.ball c (r + r + ‖a‖),
          ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤ P :=
        setIntegral_mono_set (integrable_norm_sub_normal hN hn n).integrableOn
          (Eventually.of_forall fun _ ↦ norm_nonneg _) (Eventually.of_forall fun _ hx ↦
            Metric.ball_subset_ball (by linarith : r + r + ‖a‖ ≤ 4 * r) hx)
      exact hleft.trans (htrans.trans ((mul_le_mul_of_nonneg_left hpmono (norm_nonneg a)).trans
        (mul_le_mul_of_nonneg_right han.le hPn)))
    · have heq : I a = 0 := by
        apply integral_eq_zero_of_ae
        apply Eventually.of_forall
        intro x
        by_cases hx : x ∈ W
        · have hx' : x - a ∉ U := fun hx' ↦ hex ⟨x, hx, hx'⟩
          simp [f, characteristic, hx']
        · simp [f, characteristic, hx]
      rw [heq]
      positivity
  have hir : (∫ a, I a ∂torusVolume) = ∫ a in Metric.ball 0 (2 * r), I a ∂torusVolume := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro a
    by_cases ha : a ∈ Metric.ball 0 (2 * r)
    · simp [ha]
    · simp [ha, hIz a ha]
  have hbound : (∫ a in Metric.ball 0 (2 * r), I a ∂torusVolume) ≤
      torusVolume.real (Metric.ball (0 : Torus) (2 * r)) * (2 * r * P) := by
    calc
      _ ≤ ∫ _ in Metric.ball 0 (2 * r), (2 * r * P) ∂torusVolume :=
        setIntegral_mono_on hIi.integrableOn (integrable_const _)
          Metric.isOpen_ball.measurableSet hIbound
      _ = _ := by simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have hvol : torusVolume.real (Metric.ball (0 : Torus) (2 * r)) ≤ 64 * r ^ 3 := by
    rw [Measure.real_def, volume_torusBall 0 (by positivity) (by linarith),
      ENNReal.toReal_ofReal (by positivity)]
    nlinarith [Real.pi_lt_four, pow_pos hr 3]
  rw [← hIeq, hir]
  exact hbound.trans ((mul_le_mul_of_nonneg_right hvol (by positivity)).trans (by
    dsimp [P]
    ring_nf
    exact le_rfl))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma shortestLift_quotientMap {x : Cover} (hx : ‖x‖ < 1 / 2) :
    shortestLift (quotientMap x) = x := by
  have hc : x + cubeCenter ∈ fundamentalCube := coverBall_subset_cube (by rfl)
    (by simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hx)
  rw [shortestLift, ← quotientMap_add, representative_quotientMap_of_mem hc, add_sub_cancel_right]

lemma shortestLift_eq_of_lift {a : Torus} {v : Cover} (hv : quotientMap v = a)
    (hn : ‖v‖ < 1 / 2) : shortestLift a = v := by rw [← hv, shortestLift_quotientMap hn]

lemma inner_shortestLift_sub_nonneg {c y x z : Torus} {n : Cover} (hn : ‖n‖ = 1)
    {r t : ℝ} (hyr : dist y c < r) (hxr : dist x c < t) (hzr : dist z y < t)
    (hsmall : r + 2 * t ≤ 1 / 2) (hheight : 2 * t ≤ ⟪n, shortestLift (y - c)⟫) :
    0 ≤ ⟪n, shortestLift (z - x)⟫ := by
  have he : shortestLift (z - x) = shortestLift (y - c) + shortestLift (z - y) -
      shortestLift (x - c) := by
    apply shortestLift_eq_of_lift
    · simp only [quotientMap_sub, quotientMap_add, quotientMap_shortestLift]; abel
    · have hh := (norm_sub_le (shortestLift (y - c) + shortestLift (z - y))
        (shortestLift (x - c))).trans
        (add_le_add (norm_add_le _ _) le_rfl)
      have hy' : ‖shortestLift (y - c)‖ < r := by
        simpa only [norm_shortestLift, ← dist_eq_norm] using hyr
      have hz' : ‖shortestLift (z - y)‖ < t := by
        simpa only [norm_shortestLift, ← dist_eq_norm] using hzr
      have hx' : ‖shortestLift (x - c)‖ < t := by
        simpa only [norm_shortestLift, ← dist_eq_norm] using hxr
      linarith
  rw [he, inner_sub_right, inner_add_right]
  have hx := abs_real_inner_le_norm n (shortestLift (x - c))
  have hz := abs_real_inner_le_norm n (shortestLift (z - y))
  simp only [hn, one_mul, norm_shortestLift, ← dist_eq_norm, abs_le] at hx hz
  linarith [hx.2, hz.1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma ordered_density_normal_oscillation {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {c a b : Torus} {n : Cover} (hnorm : ‖n‖ = 1)
    {r t δ : ℝ} (hr : 0 < r) (hsmall : r ≤ 1 / 16) (ht : 0 < t) (htr : t ≤ r)
    (hδ : 0 < δ) (ha : dist a c < r) (hb : dist b c < r)
    (hda : δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    (hdb : δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball b t))
    (hheight : 2 * t ≤ ⟪n, shortestLift (b - a)⟫) :
    δ ^ 2 * (t / r) ^ 6 ≤ 131072 * normalOscillation (spatialNormalMeasure μ) N c n (8 * r) := by
  have hba : dist b a < 2 * r := by linarith [dist_triangle b c a, dist_comm c a]
  have hUB : Eᶜ ∩ Metric.ball a t ⊆ Metric.ball c (2 * r) := by
    intro x hx
    have hh : dist x a < t := hx.2
    exact show dist x c < 2 * r from by linarith [dist_triangle x a c]
  have hWB : E ∩ Metric.ball b t ⊆ Metric.ball c (2 * r) := by
    intro x hx
    have hh : dist x b < t := hx.2
    exact show dist x c < 2 * r from by linarith [dist_triangle x b c]
  have hsep : ∀ x ∈ Eᶜ ∩ Metric.ball a t, ∀ z ∈ E ∩ Metric.ball b t,
      0 ≤ ⟪n, shortestLift (z - x)⟫ := by
    intro x hx z hz
    exact inner_shortestLift_sub_nonneg hnorm hba hx.2 hz.2 (by linarith) hheight
  have hp := ordered_volume_product_bound hE hμ hN hpolar hn
    (hE.compl.inter Metric.isOpen_ball.measurableSet) (hE.inter Metric.isOpen_ball.measurableSet)
    inter_subset_left inter_subset_left c (by positivity : 0 < 2 * r) (by linarith) hUB hWB n hsep
  have hprod := mul_le_mul hda hdb (by positivity : 0 ≤ δ * t ^ 3) ENNReal.toReal_nonneg
  have hm : (∫ x in Metric.ball c (4 * (2 * r)),
      ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in Metric.closedBall c (8 * r), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := by
    rw [show 4 * (2 * r) = 8 * r by ring]
    exact setIntegral_mono_set (integrable_norm_sub_normal hN hn n).integrableOn
      (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (Eventually.of_forall fun _ hx ↦ Metric.ball_subset_closedBall hx)
  have hh := hprod.trans (hp.trans (mul_le_mul_of_nonneg_left hm (by positivity)))
  apply (mul_le_mul_iff_left₀ (pow_pos hr 6)).mp
  calc
    δ ^ 2 * (t / r) ^ 6 * r ^ 6 = (δ * t ^ 3) * (δ * t ^ 3) := by field_simp
    _ ≤ 128 * (2 * r) ^ 4 * ∫ x in Metric.closedBall c (8 * r),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := hh
    _ = (131072 * normalOscillation (spatialNormalMeasure μ) N c n (8 * r)) * r ^ 6 := by
      rw [normalOscillation]
      field_simp
      ring

lemma normal_oscillation_implies_boundary_flatness {E B : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hd : ∀ a ∈ B, ∀ t : ℝ, 0 < t → t ≤ R →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    {c : Torus} (hc : c ∈ B) {n : Cover} (hnorm : ‖n‖ = 1)
    (hlim : Tendsto (normalOscillation (spatialNormalMeasure μ) N c n) (𝓝[>] 0) (𝓝 0)) :
    BoundaryFlatAt B c n := by
  intro ε hε
  let η := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  have hthreshold : 0 < δ ^ 2 * (η / 4) ^ 6 := by positivity
  have hevent : ∀ᶠ s : ℝ in 𝓝[>] 0,
      131072 * normalOscillation (spatialNormalMeasure μ) N c n s < δ ^ 2 * (η / 4) ^ 6 :=
    (show Tendsto (fun s ↦ 131072 * normalOscillation (spatialNormalMeasure μ) N c n s)
      (𝓝[>] 0) (𝓝 0) from by simpa only [mul_zero] using hlim.const_mul 131072).eventually
        (Iio_mem_nhds hthreshold)
  filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hR (by norm_num : (0 : ℝ) < 1 / 16))),
      eventually_nhdsGT_zero_mul_left (by norm_num : (0 : ℝ) < 8) hevent] with r hr hrsmall hos
  have hrpos : 0 < r := hr
  have hrR : r ≤ R := (show r < min R (1 / 16) from hrsmall).le.trans (min_le_left _ _)
  have hr16 : r ≤ 1 / 16 := (show r < min R (1 / 16) from hrsmall).le.trans (min_le_right _ _)
  let t := η * r / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have htr : t ≤ r := by dsimp [t]; nlinarith
  have htR : t ≤ R := htr.trans hrR
  have hquot : t / r = η / 4 := by dsimp [t]; field_simp
  have hforbid : ∀ a ∈ B, dist a c < r → ∀ b ∈ B, dist b c < r →
      ¬ 2 * t ≤ ⟪n, shortestLift (b - a)⟫ := by
    intro a ha har b hb hbr hh
    have hh' := ordered_density_normal_oscillation hE hμ hN hpolar hn hnorm hrpos hr16 ht htr
      hδ har hbr (hd a ha t ht htR).2 (hd b hb t ht htR).1 hh
    rw [hquot] at hh'
    exact (not_lt_of_ge hh') hos
  intro y hy hyr
  have hcc : dist c c < r := by simpa only [dist_self] using hrpos
  have hl : ⟪n, shortestLift (y - c)⟫ < 2 * t := lt_of_not_ge (hforbid c hc hcc y hy hyr)
  have he : shortestLift (c - y) = -shortestLift (y - c) := by
    apply shortestLift_eq_of_lift
    · rw [quotientMap_neg, quotientMap_shortestLift]; abel
    · rw [norm_neg, norm_shortestLift, ← dist_eq_norm]
      linarith
  have hk := lt_of_not_ge (hforbid y hy hyr c hc hcc)
  rw [he, inner_neg_right] at hk
  have habs : |⟪n, shortestLift (y - c)⟫| < 2 * t := abs_lt.mpr ⟨by linarith, hl⟩
  apply habs.trans_le
  dsimp [t]
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma normalCap_eq_image (c : Torus) (n : Cover) {r : ℝ} (hr : r ≤ 1 / 2) (h : ℝ) :
    normalCap c n r h = (fun v ↦ quotientMap v + c) ''
      (Metric.ball (0 : Cover) r ∩ {v | h < ⟪n, v⟫}) := by
  ext x
  constructor
  · rintro ⟨hx, hh⟩
    refine ⟨shortestLift (x - c), ⟨?_, hh⟩, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, norm_shortestLift, ← dist_eq_norm] using hx
    · simp only [quotientMap_shortestLift]; abel
  · rintro ⟨v, ⟨hv, hh⟩, rfl⟩
    have hv' : ‖v‖ < 1 / 2 := (show ‖v‖ < r by simpa using hv).trans_le hr
    simp only [normalCap, Set.mem_ofPred_eq, add_sub_cancel_right,
      shortestLift_quotientMap hv']
    refine ⟨?_, hh⟩
    rw [dist_eq_norm, add_sub_cancel_right, ← norm_shortestLift, shortestLift_quotientMap hv']
    simpa using hv

lemma isPreconnected_normalCap (c : Torus) (n : Cover) {r : ℝ} (hr : r ≤ 1 / 2) (h : ℝ) :
    IsPreconnected (normalCap c n r h) := by
  rw [normalCap_eq_image c n hr h]
  have hc : Convex ℝ {v : Cover | h < ⟪n, v⟫} :=
    (convex_Ioi h).linear_preimage (innerSL ℝ n).toLinearMap
  exact ((convex_ball (0 : Cover) r).inter hc).isPreconnected.image _
    (continuous_quotientMap.add continuous_const).continuousOn

lemma preconnected_avoids_frontier {U S : Set Torus} (hU : IsOpen U)
    (hS : IsPreconnected S) (h : Disjoint S (frontier U)) :
    S ⊆ U ∨ S ⊆ (closure U)ᶜ := by
  apply hS.subset_or_subset hU isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_right (compl_subset_compl.mpr subset_closure))
  intro x hx
  by_cases hxU : x ∈ U
  · exact Or.inl hxU
  · right
    intro hxcl
    exact Set.disjoint_left.mp h hx (by rw [frontier, hU.interior_eq]; exact ⟨hxcl, hxU⟩)

lemma normalCap_avoids_frontier {U : Set Torus} {c : Torus} {n : Cover} {r ε : ℝ}
    (hflat : ∀ y ∈ frontier U, dist y c < r →
      |⟪n, shortestLift (y - c)⟫| < ε * r) :
    Disjoint (normalCap c n r (ε * r)) (frontier U) := by
  rw [Set.disjoint_left]
  intro y hy hb
  exact (not_lt_of_ge (le_abs_self _)) ((hflat y hb hy.1).trans hy.2)

lemma normalCap_ball_subset {c : Torus} {n : Cover} (hn : ‖n‖ = 1)
    {r ε : ℝ} (hr : 0 < r) (hs : r ≤ 1 / 16) (hε : ε ≤ 1 / 4) :
    Metric.ball (quotientMap ((r / 2) • n) + c) (r / 8) ⊆ normalCap c n r (ε * r) := by
  let b := quotientMap ((r / 2) • n) + c
  have hrn : ‖(r / 2) • n‖ = r / 2 := by rw [norm_smul, hn, mul_one, Real.norm_of_nonneg (by positivity)]
  have hbc : dist b c = r / 2 := by
    rw [dist_eq_norm, show b - c = quotientMap ((r / 2) • n) by dsimp [b]; abel,
      ← norm_shortestLift, shortestLift_quotientMap (by rw [hrn]; linarith), hrn]
  intro x hx
  have hxb : dist x b < r / 8 := hx
  have hxc : dist x c < r := by linarith [dist_triangle x b c]
  refine ⟨hxc, ?_⟩
  have hl : shortestLift (x - c) = shortestLift (x - b) + (r / 2) • n := by
    apply shortestLift_eq_of_lift
    · simp only [quotientMap_add, quotientMap_shortestLift]; dsimp [b]; abel
    · have hh := norm_add_le (shortestLift (x - b)) ((r / 2) • n)
      rw [norm_shortestLift, ← dist_eq_norm, hrn] at hh
      linarith
  rw [hl, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hn]
  have hh := (abs_real_inner_le_norm n (shortestLift (x - b)))
  rw [hn, one_mul, norm_shortestLift, ← dist_eq_norm, abs_le] at hh
  have hm := mul_le_mul_of_nonneg_right hε hr.le
  nlinarith [hh.1]

lemma small_oscillation_outward_cap {E U : Set Torus} (hE : MeasurableSet E)
    (hU : IsOpen U) (hUE : U =ᵐ[torusVolume] E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover}
    (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {c : Torus} {n : Cover} (hnorm : ‖n‖ = 1) {r ε δ : ℝ}
    (hr : 0 < r) (hs : r ≤ 1 / 16) (hε : ε ≤ 1 / 4) (hδ : 0 < δ)
    (hden : δ * (r / 8) ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball c (r / 8)))
    (hflat : ∀ y ∈ frontier U, dist y c < r →
      |⟪n, shortestLift (y - c)⟫| < ε * r)
    (hosc : 131072 * normalOscillation (spatialNormalMeasure μ) N c n (8 * r) <
      δ ^ 2 * (1 / 8) ^ 6) :
    normalCap c n r (ε * r) ⊆ (closure U)ᶜ := by
  rcases preconnected_avoids_frontier hU (isPreconnected_normalCap c n (by linarith) _)
    (normalCap_avoids_frontier hflat) with hi | ho
  · exfalso
    let b := quotientMap ((r / 2) • n) + c
    have hbU : Metric.ball b (r / 8) ⊆ U := (normalCap_ball_subset hnorm hr hs hε).trans hi
    have heq : torusVolume.real (E ∩ Metric.ball b (r / 8)) =
        torusVolume.real (Metric.ball b (r / 8)) := by
      calc
        _ = torusVolume.real (U ∩ Metric.ball b (r / 8)) :=
          measureReal_congr (hUE.symm.inter EventuallyEq.rfl)
        _ = _ := by rw [inter_eq_right.mpr hbU]
    have hvol : torusVolume.real (Metric.ball b (r / 8)) =
        torusVolume.real (Metric.ball c (r / 8)) := by
      simp only [Measure.real_def, volume_torusBall _ (by positivity : 0 ≤ r / 8) (by linarith)]
    have hdb : δ * (r / 8) ^ 3 ≤ torusVolume.real (E ∩ Metric.ball b (r / 8)) := by
      rw [heq, hvol]
      exact hden.trans (measureReal_mono inter_subset_right)
    have hrn : ‖(r / 2) • n‖ = r / 2 := by
      rw [norm_smul, hnorm, mul_one, Real.norm_of_nonneg (by positivity)]
    have hbc : shortestLift (b - c) = (r / 2) • n := by
      rw [show b - c = quotientMap ((r / 2) • n) by dsimp [b]; abel]
      exact shortestLift_quotientMap (by rw [hrn]; linarith)
    have hdist : dist b c < r := by
      rw [dist_eq_norm, ← norm_shortestLift, hbc, hrn]; linarith
    have hheight : 2 * (r / 8) ≤ ⟪n, shortestLift (b - c)⟫ := by
      rw [hbc, inner_smul_right, real_inner_self_eq_norm_sq, hnorm]; nlinarith
    have hh := ordered_density_normal_oscillation hE hμ hN hpolar hn hnorm hr hs
      (by positivity : 0 < r / 8) (by linarith) hδ
      (by simpa only [dist_self] using hr) hdist hden hdb hheight
    have hquot : (r / 8) / r = 1 / 8 := by field_simp
    rw [hquot] at hh
    exact (not_lt_of_ge hh) hosc
  · exact ho

lemma polar_reverse_normal {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) :
    ∀ᵐ z ∂((μ.map reverseNormal) : Measure NormalBundle),
      -N (quotientMap z.1) = (z.2 : Cover) := by
  change ∀ᵐ z ∂Measure.map reverseNormal (μ : Measure NormalBundle), _
  apply (ae_map_iff continuous_reverseNormal.measurable.aemeasurable
    (show MeasurableSet {z : NormalBundle | -N (quotientMap z.1) = (z.2 : Cover)} from
      measurableSet_eq_fun
        (hN.comp (measurable_quotientMap.comp (continuous_subtype_val.comp continuous_fst).measurable)).neg
        (continuous_subtype_val.comp continuous_snd).measurable)).2
  filter_upwards [hpolar] with z hz
  change -N (quotientMap z.1) = -(z.2 : Cover)
  rw [hz]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRadialVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma quotientMap_injective_open_closed_cell {x y : Cover}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 < y i ∧ y i < 1)
    (he : quotientMap x = quotientMap y) : x = y := by
  obtain ⟨n, hn⟩ := same_quotient_lattice he
  have hz (i : Fin 3) : n i = 0 := by
    have he' := congrArg (fun z : Cover ↦ z i) hn
    change x i = y i + (n i : ℝ) at he'
    have hlt : (n i : ℝ) < 1 := by linarith [(hx i).2, (hy i).1]
    have hgt : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).1, (hy i).2]
    have hlt' : n i < (1 : ℤ) := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < n i := by exact_mod_cast hgt
    omega
  rw [show n = 0 from funext hz, latticeVector_zero, add_zero] at hn
  exact hn

lemma quotientMap_image_ball (a : Cover) (r : ℝ) :
    quotientMap '' Metric.ball a r = Metric.ball (quotientMap a) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change dist (quotientMap y) (quotientMap a) < r
    rw [dist_eq_norm, ← quotientMap_sub]
    exact (norm_quotientMap_le _).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  · intro hx
    refine ⟨shortestLift (x - quotientMap a) + a, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_shortestLift] using hx
    · rw [quotientMap_add, quotientMap_shortestLift, sub_add_cancel]

lemma compactCell_mem_quotient_ball_iff (z : CompactCell) (a : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    quotientMap z ∈ Metric.ball (quotientMap a) r ↔ (z : Cover) ∈ Metric.ball a r := by
  constructor
  · intro hz
    rw [← quotientMap_image_ball a r] at hz
    obtain ⟨y, hy, he⟩ := hz
    have he' := quotientMap_injective_open_closed_cell (compactCell_coordinates z) (hc hy) he.symm
    rwa [he']
  · intro hz
    rw [← quotientMap_image_ball a r]
    exact ⟨z, hz, rfl⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_sq_cauchy_finite {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    {f : α → ℝ} (hf : Integrable f ν) (hf2 : Integrable (fun x ↦ f x ^ 2) ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ν.real univ * ∫ x, f x ^ 2 ∂ν := by
  by_cases hzero : ν univ = 0
  · rw [Measure.measure_univ_eq_zero.mp hzero]
    simp
  have hmass : 0 < ν.real univ := ENNReal.toReal_pos hzero (measure_ne_top _ _)
  let m := (∫ x, f x ∂ν) / ν.real univ
  have hpoly : 0 ≤ (∫ x, f x ^ 2 ∂ν) - (2 * m) * (∫ x, f x ∂ν) + ν.real univ * m ^ 2 := by
    have hh : 0 ≤ ∫ x, (f x - m) ^ 2 ∂ν := integral_nonneg (fun _ ↦ sq_nonneg _)
    have he : (fun x ↦ (f x - m) ^ 2) = (fun x ↦ (f x ^ 2 - (2 * m) * f x) + m ^ 2) := by
      funext x
      ring
    have hip : Integrable (fun x ↦ f x ^ 2 - (2 * m) * f x) ν := hf2.sub (hf.const_mul (2 * m))
    rw [he, integral_add hip (integrable_const (m ^ 2)),
      integral_sub hf2 (hf.const_mul (2 * m)), integral_const_mul, integral_const, smul_eq_mul] at hh
    exact hh
  have he : ν.real univ * ((∫ x, f x ^ 2 ∂ν) - (2 * m) * (∫ x, f x ∂ν) + ν.real univ * m ^ 2) =
      ν.real univ * (∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 := by
    dsimp [m]
    field_simp
    ring
  have hh := mul_nonneg hmass.le hpoly
  rw [he] at hh
  linarith

lemma normalOscillation_sq_le_excess (σ : FiniteMeasure Torus) {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) {n : Cover} (hnorm : ‖n‖ = 1)
    (a : Torus) {r A : ℝ} (hr : 0 < r)
    (hmass : (σ : Measure Torus).real (Metric.closedBall a r) ≤ A * r ^ 2) :
    normalOscillation σ N a n r ^ 2 ≤ A * normalExcess σ N a n r := by
  have hi : Integrable (fun x ↦ ‖N x - n‖) (σ : Measure Torus) := by
    apply Integrable.of_bound (hN.sub_const _).norm.aestronglyMeasurable 2
    filter_upwards [hn] with x hx
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [hx, hnorm, one_add_one_eq_two] using norm_sub_le (N x) n
  have hi2 : Integrable (fun x ↦ ‖N x - n‖ ^ 2) (σ : Measure Torus) := by
    apply Integrable.of_bound ((hN.sub_const _).norm.pow_const 2).aestronglyMeasurable 4
    filter_upwards [hn] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb : ‖N x - n‖ ≤ 2 := by simpa only [hx, hnorm, one_add_one_eq_two] using norm_sub_le (N x) n
    nlinarith [norm_nonneg (N x - n)]
  have hc := integral_sq_cauchy_finite ((σ : Measure Torus).restrict (Metric.closedBall a r))
    hi.integrableOn hi2.integrableOn
  rw [Measure.real_def, Measure.restrict_apply_univ] at hc
  have hh := hc.trans (mul_le_mul_of_nonneg_right hmass (integral_nonneg fun _ ↦ sq_nonneg _))
  rw [normalOscillation, normalExcess]
  apply (mul_le_mul_iff_right₀ (pow_pos hr 4)).mp
  convert hh using 1 <;> field_simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVTriangleRegion
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma small_oscillation_boundary_flat {E B : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {R δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ a ∈ B, ∀ t : ℝ, 0 < t → t ≤ R →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    {c : Torus} (hc : c ∈ B) {n : Cover} (hnorm : ‖n‖ = 1)
    {r ε : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hr16 : r ≤ 1/16)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hosc : 131072 * normalOscillation (spatialNormalMeasure μ) N c n (8*r) < δ^2*(ε/4)^6) :
    ∀ y ∈ B, dist y c < r → |⟪n,shortestLift (y-c)⟫| < ε*r := by
  let t := ε * r / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have htr : t ≤ r := by dsimp [t]; nlinarith
  have htR : t ≤ R := htr.trans hrR
  have hquot : t / r = ε / 4 := by dsimp [t]; field_simp
  have hforbid : ∀ a ∈ B, dist a c < r → ∀ b ∈ B, dist b c < r →
      ¬ 2 * t ≤ ⟪n, shortestLift (b - a)⟫ := by
    intro a ha har b hb hbr hh
    have hh' := ordered_density_normal_oscillation hE hμ hN hpolar hn hnorm hr hr16 ht htr
      hδ har hbr (hd a ha t ht htR).2 (hd b hb t ht htR).1 hh
    rw [hquot] at hh'
    exact (not_lt_of_ge hh') hosc
  intro y hy hyr
  have hcc : dist c c < r := by simpa only [dist_self] using hr
  have hl : ⟪n, shortestLift (y - c)⟫ < 2 * t := lt_of_not_ge (hforbid c hc hcc y hy hyr)
  have he : shortestLift (c - y) = -shortestLift (y - c) := by
    apply shortestLift_eq_of_lift
    · rw [quotientMap_neg, quotientMap_shortestLift]; abel
    · rw [norm_neg, norm_shortestLift, ← dist_eq_norm]
      linarith
  have hk := lt_of_not_ge (hforbid y hy hyr c hc hcc)
  rw [he, inner_neg_right] at hk
  have habs : |⟪n, shortestLift (y - c)⟫| < 2 * t := abs_lt.mpr ⟨by linarith, hl⟩
  apply habs.trans_le
  dsimp [t]
  nlinarith

theorem isMinimizerAt_quantitative_trapping {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧ ∀ μ : FiniteMeasure NormalBundle,
      IsNormalMeasure E μ → ∀ N : Torus → Cover, Measurable N →
      (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
      (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ c ∈ frontier (openRepresentative E), ∀ n : Cover, ‖n‖ = 1 →
      ∀ r ε : ℝ, 0 < r → r ≤ R → 0 < ε → ε ≤ 1/4 →
        131072*normalOscillation (spatialNormalMeasure μ) N c n (8*r) < δ^2*(ε/4)^6 →
        normalCap c n r (ε*r) ⊆ (closure (openRepresentative E))ᶜ ∧
        normalCap c (-n) r (ε*r) ⊆ openRepresentative E := by
  obtain ⟨R,δ,hR,hδ,hd⟩ := isMinimizerAt_two_sided_density hV hE hmin
  refine ⟨min R (1/16),δ,by positivity,hδ,?_⟩
  intro μ hμ N hN hp hn c hc n hnorm r ε hr hrs hε hεs hosc
  have hrR := hrs.trans (min_le_left _ _)
  have hr16 := hrs.trans (min_le_right _ _)
  have hbc : c ∈ volumeSupport E ∩ volumeSupport Eᶜ := by
    rwa [isMinimizerAt_frontier_openRepresentative hV hE hmin] at hc
  have hflat := small_oscillation_boundary_flat hE hμ hN hp hn hδ hd hbc hnorm
    hr hrR hr16 hε (by linarith) hosc
  have hflatU : ∀ y ∈ frontier (openRepresentative E), dist y c < r →
      |⟪n,shortestLift (y-c)⟫| < ε*r := by
    rwa [isMinimizerAt_frontier_openRepresentative hV hE hmin]
  have hthreshold : δ^2*(ε/4)^6 ≤ δ^2*(1/8)^6 := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 6
  have hout := small_oscillation_outward_cap hE (isOpen_openRepresentative E)
    (isMinimizerAt_openRepresentative_ae hV hE hmin) hμ hN hp hn hnorm hr hr16 hεs hδ
    (hd c hbc (r/8) (by positivity) (by linarith)).2 hflatU (hosc.trans_le hthreshold)
  have hVc : 1-V ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hminc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
  have hn' : ∀ᵐ x ∂(spatialNormalMeasure (μ.map reverseNormal) : Measure Torus), ‖-N x‖ = 1 := by
    simpa only [spatialNormalMeasure_reverse,norm_neg] using hn
  have heq : frontier (openRepresentative Eᶜ) = frontier (openRepresentative E) := by
    rw [isMinimizerAt_frontier_openRepresentative hVc hE.compl hminc,
      isMinimizerAt_frontier_openRepresentative hV hE hmin,compl_compl,inter_comm]
  have hflatC : ∀ y ∈ frontier (openRepresentative Eᶜ), dist y c < r →
      |⟪-n,shortestLift (y-c)⟫| < ε*r := by
    simpa only [heq,inner_neg_left,abs_neg] using hflatU
  have hosceq : normalOscillation (spatialNormalMeasure (μ.map reverseNormal)) (-N) c (-n) (8*r) =
      normalOscillation (spatialNormalMeasure μ) N c n (8*r) := by
    simp only [normalOscillation,spatialNormalMeasure_reverse,Pi.neg_apply,neg_sub_neg,norm_sub_rev n]
  have hin := small_oscillation_outward_cap hE.compl (isOpen_openRepresentative Eᶜ)
    (isMinimizerAt_openRepresentative_ae hVc hE.compl hminc) (isNormalMeasure_compl hE hμ) hN.neg
    (polar_reverse_normal hN hp) hn' (by simpa only [norm_neg] using hnorm) hr hr16 hεs hδ
    (by simpa only [compl_compl] using (hd c hbc (r/8) (by positivity) (by linarith)).1)
    hflatC (by rw [hosceq]; exact hosc.trans_le hthreshold)
  have he : (closure (openRepresentative Eᶜ))ᶜ = openRepresentative E := by
    rw [isMinimizerAt_closure_openRepresentative hVc hE.compl hminc]
    rfl
  exact ⟨hout,he ▸ hin⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVGraphNormalization
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
open Laplacian
namespace CubicTorus

lemma integral_polar_tilt_ball {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (a n : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x in Metric.ball (quotientMap a) r, ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r},
        ‖(z.2 : Cover)-n‖^2 ∂(μ : Measure NormalBundle) := by
  have hs : MeasurableSet {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} :=
    Metric.isOpen_ball.measurableSet.preimage (by fun_prop)
  rw [← integral_indicator Metric.isOpen_ball.measurableSet,
    integral_spatialNormalMeasure μ (((hN.sub_const n).norm.pow_const 2).indicator
      Metric.isOpen_ball.measurableSet), ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [hp] with z hz
  have hm := compactCell_mem_quotient_ball_iff z.1 a r hc
  change (Metric.ball (quotientMap a) r).indicator (fun x ↦ ‖N x-n‖^2) (quotientMap z.1) = _
  by_cases hh : (z.1 : Cover) ∈ Metric.ball a r
  · rw [indicator_of_mem (hm.mpr hh),indicator_of_mem (show z ∈ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hh),hz]
  · rw [indicator_of_notMem (mt hm.mp hh),indicator_of_notMem (show z ∉ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hh)]

lemma polar_tilt_integrable {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N) (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (n : Cover) : Integrable (fun x ↦ ‖N x-n‖^2) (spatialNormalMeasure μ : Measure Torus) := by
  apply Integrable.of_bound ((hN.sub_const n).norm.pow_const 2).aestronglyMeasurable ((1+‖n‖)^2)
  filter_upwards [hu] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [hx] using norm_sub_le (N x) n) 2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma diagonal_strictMono {P : ℕ → ℕ → Prop} (hP : ∀ i, ∀ᶠ j in atTop, P i j) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ i, P i (ψ i) := by
  have hh (i) : ∃ N : ℕ, ∀ j ≥ N, P i j := eventually_atTop.mp (hP i)
  choose N hN using hh
  let ψ : ℕ → ℕ := Nat.rec (N 0) (fun i k ↦ max (N (i+1)) (k+1))
  have hψ : StrictMono ψ := strictMono_nat_of_lt_succ (fun i ↦ by
    change ψ i < max (N (i+1)) (ψ i+1)
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
  refine ⟨ψ,hψ,fun i ↦ hN i _ ?_⟩
  cases i with
  | zero => exact le_rfl
  | succ i => exact le_max_left _ _

lemma oscillation_le_scaled_tilt {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N) (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hnorm : ‖n‖ = 1) (c : Torus) {r e A : ℝ} (hr : 0 < r) (he : 0 ≤ e) (hA : 0 ≤ A)
    (hm : (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (16*r)) ≤ A*(16*r)^2)
    (ht : (∫ x in Metric.closedBall c (17*r), ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2) :
    normalOscillation (spatialNormalMeasure μ) N c n (8*r) ≤ (A+1)*e := by
  have hmass : (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall c (8*r)) ≤ (4*A)*(8*r)^2 := by
    calc
      _ ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (16*r)) :=
        measureReal_mono (Metric.closedBall_subset_ball (by linarith))
      _ ≤ A*(16*r)^2 := hm
      _ = _ := by ring
  have hexc : normalExcess (spatialNormalMeasure μ) N c n (8*r) ≤ e^2/64 := by
    unfold normalExcess
    apply (div_le_iff₀ (by positivity : 0 < (8*r)^2)).mpr
    have hj := (setIntegral_mono_set (polar_tilt_integrable hN hn n).integrableOn
      (Eventually.of_forall fun x ↦ sq_nonneg ‖N x-n‖)
      (Metric.closedBall_subset_closedBall (by linarith : 8*r ≤ 17*r)).eventuallyLE).trans ht
    convert hj using 1
    all_goals first | rfl | ring
  have hh := (normalOscillation_sq_le_excess (spatialNormalMeasure μ) hN hn hnorm c
    (by positivity : 0 < 8*r) hmass).trans (mul_le_mul_of_nonneg_left hexc (by positivity : 0 ≤ 4*A))
  have hrhs : 0 ≤ (A+1)*e := by positivity
  have hpoly : 4*A*(e^2/64) ≤ ((A+1)*e)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (A+1)) (sq_nonneg e),mul_nonneg (sq_nonneg A) (sq_nonneg e),mul_nonneg hA (sq_nonneg e)]
  nlinarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVInteriorMultiplier
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma choose_excess_scale {R K : ℝ} (hR : 0 < R) (hRs : R ≤ 1/8) (hK : 0 ≤ K) :
    ∃ θ ρ ε : ℝ, 0 < θ ∧ 2*θ ≤ R ∧ ρ = θ/34 ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧
      0 < ε ∧ 2*(K*θ^4+ε) ≤ ρ^2/4 := by
  let θ := min (R/2) (1/(1000000*(K+1)))
  have ht : 0 < θ := by dsimp [θ]; positivity
  have htR : 2*θ ≤ R := by have := min_le_left (R/2) (1/(1000000*(K+1))); dsimp [θ]; linarith
  have hts : θ ≤ 1 := by linarith
  have htK : θ*(K+1) ≤ 1/1000000 := by
    have hh := min_le_right (R/2) (1/(1000000*(K+1)))
    have := (le_div_iff₀ (show 0 < 1000000*(K+1) by positivity)).mp hh
    dsimp [θ]
    nlinarith
  have hKt : K*θ ≤ 1/1000000 := by nlinarith
  have hKtt : K*θ^2 ≤ 1/1000000 := by nlinarith [mul_le_mul_of_nonneg_left hts (mul_nonneg hK ht.le)]
  have hK4 : K*θ^4 ≤ (θ/34)^2/64 := by
    have hh := mul_le_mul_of_nonneg_right hKtt (sq_nonneg θ)
    nlinarith [sq_nonneg θ]
  refine ⟨θ,θ/34,(θ/34)^2/64,ht,htR,rfl,by positivity,by linarith,by positivity,?_⟩
  nlinarith [sq_nonneg (θ/34)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma polar_tilt_difference {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (n ν : Cover) (S : Set Torus) :
    (spatialNormalMeasure μ : Measure Torus).real S * ‖n-ν‖^2 ≤
      2*(∫ x in S, ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) +
      2*(∫ x in S, ‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) := by
  have hn := (polar_tilt_integrable hN hu n).integrableOn (s := S)
  have hν := (polar_tilt_integrable hN hu ν).integrableOn (s := S)
  have hh : (∫ _ in S, ‖n-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in S, 2*‖N x-n‖^2+2*‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus) := by
    apply integral_mono (integrable_const _) ((hn.const_mul 2).add (hν.const_mul 2))
    intro x
    have hb : ‖n-ν‖ ≤ ‖N x-n‖+‖N x-ν‖ := by
      have hh := norm_add_le (n-N x) (N x-ν)
      rwa [sub_add_sub_cancel,norm_sub_rev n (N x)] at hh
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖N x-n‖-‖N x-ν‖),norm_nonneg (n-ν),norm_nonneg (N x-n),norm_nonneg (N x-ν)]
  simpa only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,
    integral_add (hn.const_mul 2) (hν.const_mul 2),integral_const_mul] using hh

lemma polar_normal_step_bound {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {c ρ r e : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hρs : ρ ≤ 1)
    (hr : 0 < r) (he : 0 ≤ e) (n ν : Cover)
    (hm : c*(ρ*r)^2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a (ρ*r)))
    (hn : (∫ x in Metric.closedBall a (17*r), ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2)
    (hν : (∫ x in Metric.closedBall a (17*(ρ*r)), ‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ*r)^2*(e/2)^2) :
    ‖n-ν‖ ≤ (2/(Real.sqrt c*ρ))*e := by
  have hsub : Metric.closedBall a (17*(ρ*r)) ⊆ Metric.closedBall a (17*r) :=
    Metric.closedBall_subset_closedBall (by nlinarith)
  have hnt : (∫ x in Metric.closedBall a (17*(ρ*r)), ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) hsub.eventuallyLE).trans hn
  have hm' : c*(ρ*r)^2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a (17*(ρ*r))) :=
    hm.trans (measureReal_mono (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by nlinarith [mul_pos hρ hr] : ρ*r ≤ 17*(ρ*r)))))
  have hd := (mul_le_mul_of_nonneg_right hm' (sq_nonneg ‖n-ν‖)).trans
    (polar_tilt_difference hN hu n ν (Metric.closedBall a (17*(ρ*r))))
  have ha : c*ρ^2*‖n-ν‖^2 ≤ 4*e^2 := by
    have hpow : (ρ*r)^2*(e/2)^2 ≤ r^2*e^2 := by
      have hh := mul_le_mul_of_nonneg_right hρs (hr.le)
      have hrr : 0 ≤ ρ*r := mul_nonneg hρ.le hr.le
      nlinarith [sq_nonneg (r-ρ*r),sq_nonneg (r+ρ*r),mul_nonneg (sq_nonneg r) (sq_nonneg e),
        mul_nonneg (show 0 ≤ r^2-(ρ*r)^2 by nlinarith) (sq_nonneg e)]
    have hh : (c*ρ^2*‖n-ν‖^2)*r^2 ≤ (4*e^2)*r^2 := by nlinarith only [hd,hnt,hν,hpow]
    exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).mp hh
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hs2 := Real.sq_sqrt hc.le
  have heq : (2 / (Real.sqrt c*ρ))*e = (2*e)/(Real.sqrt c*ρ) := by ring
  rw [heq]
  apply (le_div_iff₀ (mul_pos hs hρ)).mpr
  have heqsq : (‖n-ν‖*(Real.sqrt c*ρ))^2 = c*ρ^2*‖n-ν‖^2 := by
    rw [mul_pow,mul_pow,hs2]
    ring
  have haa : (‖n-ν‖*(Real.sqrt c*ρ))^2 ≤ (2*e)^2 := by rw [heqsq]; nlinarith only [ha]
  nlinarith [mul_nonneg (norm_nonneg (n-ν)) (mul_pos hs hρ).le]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma dependent_sequence {α : Type*} (P : ℕ → α → Prop) (Q : ℕ → α → α → Prop)
    {x₀ : α} (h₀ : P 0 x₀)
    (hstep : ∀ i x, P i x → ∃ y, P (i+1) y ∧ Q i x y) :
    ∃ f : ℕ → α, f 0 = x₀ ∧ ∀ i, P i (f i) ∧ Q i (f i) (f (i+1)) := by
  classical
  let step (i : ℕ) (x : {x // P i x}) : {x // P (i+1) x} :=
    ⟨Classical.choose (hstep i x x.property), (Classical.choose_spec (hstep i x x.property)).1⟩
  let f (i : ℕ) : {x // P i x} := Nat.rec (motive := fun i ↦ {x // P i x}) ⟨x₀,h₀⟩ step i
  refine ⟨fun i ↦ (f i).val,rfl,?_⟩
  intro i
  exact ⟨(f i).property,(Classical.choose_spec (hstep i (f i) (f i).property)).2⟩

lemma geometric_error_ratio {ρ r e : ℝ} (hρ : 0 < ρ) (hρs : ρ ≤ 1/16)
    (hr : 0 < r) (he : 0 < e) (i : ℕ) :
    (ρ^i*r)/(((1/2:ℝ)^i*e)^2) ≤ r/e^2 := by
  have hscalar : (ρ^i*r)/(((1/2:ℝ)^i*e)^2) = (4*ρ)^i*(r/e^2) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm i 2, pow_mul,
      show (1/2:ℝ)^2 = 1/4 by norm_num]
    calc
      _ = (ρ^i/(1/4:ℝ)^i)*(r/e^2) := by ring
      _ = (ρ/(1/4:ℝ))^i*(r/e^2) := by rw [← div_pow ρ (1/4:ℝ) i]
      _ = _ := by congr 2; ring
  rw [hscalar]
  have hh : (4*ρ)^i ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  exact (mul_le_mul_of_nonneg_right hh (div_nonneg hr.le (sq_pos_of_pos he).le)).trans_eq (one_mul _)

lemma excess_normal_iteration (T : Cover → ℝ → ℝ) {r₀ ρ δ C : ℝ}
    (hρ : 0 < ρ) (hρs : ρ ≤ 1/16)
    (hstep : ∀ (n : Cover) (r e : ℝ), ‖n‖ = 1 → 0 < r → r ≤ r₀ →
      0 < e → e ≤ δ → r/e^2 ≤ δ → T n r ≤ r^2*e^2 →
      ∃ ν : Cover, ‖ν‖ = 1 ∧ T ν (ρ*r) ≤ (ρ*r)^2*(e/2)^2 ∧ ‖n-ν‖ ≤ C*e)
    {n₀ : Cover} {r e : ℝ} (hn₀ : ‖n₀‖ = 1) (hr : 0 < r) (hrr : r ≤ r₀)
    (he : 0 < e) (heδ : e ≤ δ) (hrel : r/e^2 ≤ δ) (ht : T n₀ r ≤ r^2*e^2) :
    ∃ (n : ℕ → Cover) (ν : Cover), n 0 = n₀ ∧ (∀ i, ‖n i‖ = 1) ∧ ‖ν‖ = 1 ∧
      Tendsto n atTop (𝓝 ν) ∧
      (∀ i, T (n i) (ρ^i*r) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2) ∧
      (∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i) := by
  let ri (i : ℕ) := ρ^i*r
  let ei (i : ℕ) := (1/2:ℝ)^i*e
  have hri (i) : 0 < ri i := by dsimp [ri]; positivity
  have hri_le (i) : ri i ≤ r₀ := by
    apply le_trans _ hrr
    have hh : ρ^i ≤ 1 := pow_le_one₀ hρ.le (by linarith)
    exact (mul_le_mul_of_nonneg_right hh hr.le).trans_eq (one_mul _)
  have hei (i) : 0 < ei i := by dsimp [ei]; positivity
  have hei_le (i) : ei i ≤ δ := by
    apply le_trans _ heδ
    have hh : (1/2:ℝ)^i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact (mul_le_mul_of_nonneg_right hh he.le).trans_eq (one_mul _)
  have hi_rel (i) : ri i/(ei i)^2 ≤ δ := (geometric_error_ratio hρ hρs hr he i).trans hrel
  have hris (i) : ri (i+1) = ρ*ri i := by dsimp [ri]; rw [pow_succ]; ring
  have heis (i) : ei (i+1) = ei i/2 := by dsimp [ei]; rw [pow_succ]; ring
  let P (i : ℕ) (n : Cover) := ‖n‖ = 1 ∧ T n (ri i) ≤ (ri i)^2*(ei i)^2
  let Q (i : ℕ) (n ν : Cover) := ‖n-ν‖ ≤ C*ei i
  have hP₀ : P 0 n₀ := by simpa [P,ri,ei] using And.intro hn₀ ht
  have hPs : ∀ i n, P i n → ∃ ν, P (i+1) ν ∧ Q i n ν := by
    intro i n hn
    obtain ⟨ν,hν,hνt,hchange⟩ := hstep n (ri i) (ei i) hn.1 (hri i) (hri_le i)
      (hei i) (hei_le i) (hi_rel i) hn.2
    exact ⟨ν,⟨hν,by simpa only [hris,heis] using hνt⟩,hchange⟩
  obtain ⟨n,hn0,hn⟩ := dependent_sequence P Q hP₀ hPs
  have hbound (i) : dist (n i) (n (i+1)) ≤ (C*e)*(1/2:ℝ)^i := by
    rw [dist_eq_norm]
    convert (hn i).2 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [Q,ei]
    ring
  obtain ⟨ν,hνlim⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1/2) (C*e) (by norm_num) hbound)
  have hν : ‖ν‖ = 1 := by
    have hlim := hνlim.norm
    exact tendsto_nhds_unique hlim (by simpa only [(hn _).1.1] using (tendsto_const_nhds (x := (1:ℝ))))
  refine ⟨n,ν,hn0,fun i ↦ (hn i).1.1,hν,hνlim,fun i ↦ (hn i).1.2,?_⟩
  intro i
  have hh := dist_le_of_le_geometric_of_tendsto (1/2) (C*e) (by norm_num) hbound hνlim i
  rw [dist_eq_norm] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

lemma coords (c : InteriorCenter) (i : Fin 3) :
    3/8 ≤ (c : Cover) i ∧ (c : Cover) i ≤ 5/8 := by
  have hh := (PiLp.norm_apply_le ((c : Cover)-cubeCenter) i).trans c.property
  change ‖(c : Cover) i-(1/2:ℝ)‖ ≤ 1/8 at hh
  rw [Real.norm_eq_abs, abs_le] at hh
  constructor <;> linarith

variable {c : InteriorCenter}

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 3 / 8) :
    Metric.ball (c : Cover) r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - (c : Cover)‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - (c : Cover)) i).trans_lt hx'
  change ‖x i - (c : Cover) i‖ < r at hb
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

lemma radialCore_compactSupport : HasCompactSupport (radialCore c) :=
  (radialBump c).hasCompactSupport.mul_right

lemma radialCore_tsupport : tsupport (radialCore c) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hs : x ∈ tsupport ((radialBump c) : Cover → ℝ) := tsupport_mul_subset_left hx
  rw [(radialBump c).tsupport_eq] at hs
  have hnorm : ‖x - (c : Cover)‖ ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, radialBump] using hs
  have hb := (PiLp.norm_apply_le (x - (c : Cover)) i).trans hnorm
  change ‖x i - (c : Cover) i‖ ≤ 1 / 3 at hb
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_le] at hb
  constructor <;> linarith

lemma radialSquared_eventuallyEq_norm_sq {x : Cover} (hx : ‖x - (c : Cover)‖ < 1 / 4) :
    (radialSquared c) =ᶠ[𝓝 x] (fun y ↦ ‖y - (c : Cover)‖ ^ 2) := by
  have hc : x ∈ fundamentalCube := coverBall_subset_cube (by norm_num : (1 / 4 : ℝ) ≤ 3 / 8)
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have he := latticePeriodize_eventuallyEq (radialCore_compactSupport (c := c)) radialCore_tsupport
    (fun i ↦ ⟨(hc i).1, (hc i).2.le⟩)
  have hb := (radialBump c).eventuallyEq_one_of_mem_ball
    (show x ∈ Metric.ball (c : Cover) (radialBump c).rIn by
      simpa only [Metric.mem_ball, dist_eq_norm, radialBump] using hx)
  filter_upwards [he, hb] with y hy hby
  simp only [radialSquared, hy, radialCore, hby, Pi.one_apply, one_mul, sub_sub_cancel]

lemma closedBall_interior {r : ℝ} (hr : r < 3/8) :
    Metric.closedBall (c : Cover) r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := (PiLp.norm_apply_le (x-(c : Cover)) i).trans
    (show ‖x-(c : Cover)‖ ≤ r from hx)
  change ‖x i-(c : Cover) i‖ ≤ r at hh
  rw [Real.norm_eq_abs,abs_le] at hh
  have hc := coords c i
  constructor <;> linarith

end CubicTorus.MovingCenter

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVMovingTrappedDecay
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_trapping_subsequence {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
      (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
      (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ c : ℕ → Torus, (∀ i, c i ∈ frontier (openRepresentative E)) → ∀ (n : ℕ → Cover) (r e : ℕ → ℝ),
      (∀ i, ‖n i‖ = 1) → (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) →
      (∀ i, 0 ≤ e i) → Tendsto e atTop (𝓝 0) →
      (∀ i, (∫ x in Metric.closedBall (c i) (17*r i), ‖N x-n i‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∃ (ψ : ℕ → ℕ) (α : ℕ → ℝ), StrictMono ψ ∧ Tendsto α atTop (𝓝 0) ∧
        (∀ i, 0 < α i ∧ α i < 1/4) ∧
        ∀ i, normalCap (c (ψ i)) (n (ψ i)) (r (ψ i)) (α i*r (ψ i)) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (c (ψ i)) (-(n (ψ i))) (r (ψ i)) (α i*r (ψ i)) ⊆ openRepresentative E := by
  obtain ⟨R,δ,hR,hδ,htrap⟩ := isMinimizerAt_quantitative_trapping hV hE hmin
  obtain ⟨S,A,hS,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  refine ⟨min R (S/16),by positivity,?_⟩
  intro μ hμ N hN hp hu c hc n r e hn hr hrr he helim ht
  let o i := normalOscillation (spatialNormalMeasure μ) N (c i) (n i) (8*r i)
  have hob (i) : o i ≤ (A+1)*e i :=
    oscillation_le_scaled_tilt hN hu (hn i) (c i) (hr i) (he i) hA.le
      (harea μ hμ (c i) (16*r i) (by have hh := hr i; positivity) (by have hh := (hrr i).trans (min_le_right _ _); linarith)) (ht i)
  have holim : Tendsto o atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i ↦ div_nonneg (integral_nonneg fun x ↦ norm_nonneg _) (sq_nonneg _))
      (Eventually.of_forall hob)
    simpa only [mul_zero] using helim.const_mul (A+1)
  let α (i : ℕ) : ℝ := 1/((i:ℝ)+8)
  have hα (i) : 0 < α i ∧ α i < 1/4 := by
    have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg i
    dsimp [α]
    constructor
    · positivity
    · rw [div_lt_iff₀ (by positivity : 0 < (i:ℝ)+8)]
      linarith
  have hαlim : Tendsto α atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 8).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hevent (i) : ∀ᶠ j in atTop, 131072*o j < δ^2*(α i/4)^6 :=
    (show Tendsto (fun j ↦ 131072*o j) atTop (𝓝 0) from by simpa only [mul_zero] using holim.const_mul 131072).eventually
      (gt_mem_nhds (by have hh := (hα i).1; positivity))
  obtain ⟨ψ,hψ,hsmall⟩ := diagonal_strictMono hevent
  refine ⟨ψ,α,hψ,hαlim,hα,fun i ↦ ?_⟩
  exact htrap μ hμ N hN hp hu (c (ψ i)) (hc (ψ i)) (n (ψ i)) (hn _) (r (ψ i)) (α i)
    (hr _) ((hrr _).trans (min_le_left _ _)) (hα i).1 (hα i).2.le (hsmall i)

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_actual_sequential_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (c : ℕ → InteriorCenter), (∀ i, quotientMap (c i : Cover) ∈ frontier (openRepresentative E)) →
      ∀ (n : ℕ → Cover) (r e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto e atTop (𝓝 0) → Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ (ψ : ℕ → ℕ) (p : Plane →L[ℝ] ℝ), StrictMono ψ ∧ ∀ᶠ i in atTop,
        (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
          (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
          (r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by
  obtain ⟨r₀,R,K,hr₀,hR,hRs,hK,hdec⟩ := isMinimizerAt_trapped_sequential_decay hV hE hmin
  obtain ⟨r₁,hr₁,htrap⟩ := isMinimizerAt_trapping_subsequence hV hE hmin
  refine ⟨min r₀ r₁,R,K,by positivity,hR,hRs,hK,?_⟩
  intro μ hμ H hH N hN hp hu c hc n r e hn hr hrr he hes helim hrel ht θ ε hθ hθR hε
  obtain ⟨ψ,α,hψ,hαlim,hα,hcap⟩ := htrap μ hμ N hN hp hu (fun i ↦ quotientMap (c i : Cover)) hc
    n r e hn hr (fun i ↦ (hrr i).trans (min_le_right _ _)) (fun i ↦ (he i).le) helim ht
  obtain ⟨χ,p,hχ,hsmall⟩ := hdec μ hμ H hH N hN hp hu (c ∘ ψ) (n ∘ ψ) (r ∘ ψ) α (e ∘ ψ)
    (fun i ↦ hn (ψ i)) (fun i ↦ hr (ψ i)) (fun i ↦ (hrr (ψ i)).trans (min_le_left _ _))
    (fun i ↦ (hα i).1.le) (fun i ↦ (hα i).2) (fun i ↦ he (ψ i)) (fun i ↦ hes (ψ i))
    hαlim (helim.comp hψ.tendsto_atTop) (hrel.comp hψ.tendsto_atTop) hcap
    (fun i ↦ ht (ψ i)) θ ε hθ hθR hε
  exact ⟨ψ ∘ χ,p,hψ.comp hχ,hsmall⟩

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma spatial_tilt_closedBall_le_oriented {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hn : ‖n‖ = 1) {s r : ℝ} (hsr : s < r) (hr : r < 1/4) :
    (∫ x in Metric.closedBall (quotientMap (c : Cover)) s, ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ 2*(bundleOrientedExcess c) μ n r := by
  have hi : Integrable (fun z : NormalBundle ↦ ‖(z.2 : Cover)-n‖^2) (μ : Measure NormalBundle) :=
    (show Continuous (fun z : NormalBundle ↦ ‖(z.2 : Cover)-n‖^2) from by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsub : {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball (c : Cover) r} ⊆ {z | (radialSquared c) z.1 < r^2} := by
    intro z hz
    have hh : ‖(z.1 : Cover)-(c : Cover)‖ < r := by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_eq_norm] using hz
    change (radialSquared c) z.1 < r^2
    rw [(radialSquared_eventuallyEq_norm_sq (hh.trans hr)).eq_of_nhds]
    nlinarith [norm_nonneg ((z.1 : Cover)-(c : Cover))]
  calc
    _ ≤ ∫ x in Metric.ball (quotientMap (c : Cover)) r, ‖N x-n‖^2
        ∂(spatialNormalMeasure μ : Measure Torus) :=
      setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
        (Eventually.of_forall fun x ↦ sq_nonneg _) (Metric.closedBall_subset_ball hsr).eventuallyLE
    _ = ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball (c : Cover) r}, ‖(z.2 : Cover)-n‖^2
        ∂(μ : Measure NormalBundle) := integral_polar_tilt_ball hN hp _ _ _
      (Metric.ball_subset_closedBall.trans (closedBall_interior (by linarith)))
    _ ≤ ∫ z in {z : NormalBundle | (radialSquared c) z.1 < r^2}, ‖(z.2 : Cover)-n‖^2
        ∂(μ : Measure NormalBundle) :=
      setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun z ↦ sq_nonneg _) hsub.eventuallyLE
    _ = 2*(bundleOrientedExcess c) μ n r := by
      unfold bundleOrientedExcess
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ by
        dsimp only
        rw [norm_sub_sq_real,z.2.property,hn]
        ring

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_epsilon_improvement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ c : InteriorCenter, quotientMap (c : Cover) ∈ frontier (openRepresentative E) → ∀ (n : Cover) (r e : ℝ), ‖n‖ = 1 → 0 < r → r ≤ r₀ →
        0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
        ∃ ν : Cover, ‖ν‖ = 1 ∧
          (∫ x in Metric.closedBall (quotientMap (c : Cover)) (r*θ/2), ‖N x-ν‖^2
            ∂(spatialNormalMeasure μ : Measure Torus)) ≤ 2*r^2*e^2*(K*θ^4+ε) := by
  obtain ⟨r₀,R,K,hr₀,hR,hRs,hK,hseq⟩ := isMinimizerAt_actual_sequential_decay hV hE hmin
  refine ⟨min r₀ (1/4),R,K,by positivity,hR,hRs,hK,?_⟩
  intro μ hμ H hH N hN hp hu θ ε hθ hθR hε
  by_contra! hbad
  let d (i : ℕ) : ℝ := min (1/((i:ℝ)+1)) (1/2)
  have hdpos (i) : 0 < d i := by dsimp [d]; positivity
  have hds (i) : d i ≤ 1/2 := min_le_right _ _
  have hdlim : Tendsto d atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i ↦ (hdpos i).le) (Eventually.of_forall fun i ↦ min_le_left _ _)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (i) := hbad (d i) (hdpos i)
  choose c hc n r e hn hr hrr he hed hrel ht hno using hex
  have helim : Tendsto e atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i ↦ (he i).le) (Eventually.of_forall hed) hdlim
  have hrellim : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i ↦ div_nonneg (hr i).le (sq_nonneg _)) (Eventually.of_forall hrel) hdlim
  obtain ⟨ψ,p,hψ,hdec⟩ := hseq μ hμ H hH N hN hp hu c hc n r e hn hr
    (fun i ↦ (hrr i).trans (min_le_left _ _)) he (fun i ↦ (hed i).trans (hds i)) helim hrellim ht θ ε hθ hθR hε
  obtain ⟨i,hi⟩ := hdec.exists
  let ν := graphSlopeNormal (n (ψ i)) (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)
  have hν : ‖ν‖ = 1 := graphSlopeNormal_unit (hn _) _
  have hrθ : r (ψ i)*θ < 1/4 := by
    have hrs := (hrr (ψ i)).trans (min_le_right _ _)
    have hθs : θ < 1 := by linarith
    exact (mul_lt_of_lt_one_right (hr _) hθs).trans_le hrs
  have hs := spatial_tilt_closedBall_le_oriented (c:=c (ψ i)) hN hp hu hν (by have hh := hr (ψ i); nlinarith : r (ψ i)*θ/2 < r (ψ i)*θ) hrθ
  have hh := hs.trans (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 2))
  have hnob := hno (ψ i) ν hν
  have heq : 2*((r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε)) = 2*(r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by ring
  rw [heq] at hh
  exact (not_lt_of_ge hh) hnob

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_excess_contraction {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ ρ : ℝ, 0 < r₀ ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ c : InteriorCenter, quotientMap (c : Cover) ∈ frontier (openRepresentative E) → ∀ (n : Cover) (r e : ℝ), ‖n‖ = 1 → 0 < r → r ≤ r₀ →
        0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
        ∃ ν : Cover, ‖ν‖ = 1 ∧
          (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*(ρ*r)), ‖N x-ν‖^2
            ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ*r)^2*(e/2)^2 := by
  obtain ⟨r₀,R,K,hr₀,hR,hRs,hK,himp⟩ := isMinimizerAt_epsilon_improvement hV hE hmin
  obtain ⟨θ,ρ,ε,hθ,hθR,hρeq,hρ,hρs,hε,hsmall⟩ := choose_excess_scale hR hRs hK
  refine ⟨r₀,ρ,hr₀,hρ,hρs,?_⟩
  intro μ hμ H hH N hN hp hu
  obtain ⟨δ,hδ,hstep⟩ := himp μ hμ H hH N hN hp hu θ ε hθ hθR hε
  refine ⟨δ,hδ,?_⟩
  intro c hc n r e hn hr hrr he heδ hrel ht
  obtain ⟨ν,hν,hνt⟩ := hstep c hc n r e hn hr hrr he heδ hrel ht
  refine ⟨ν,hν,?_⟩
  have heq : 17*(ρ*r) = r*θ/2 := by rw [hρeq]; ring
  rw [heq]
  apply hνt.trans
  have hh := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (sq_nonneg r) (sq_nonneg e))
  nlinarith only [hh]

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_uniform_tilt_iteration {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
    ∃ r₀ ρ C : ℝ, 0 < r₀ ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧ 0 < C ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ a : InteriorCenter,
        quotientMap (a : Cover) ∈ frontier (openRepresentative E) →
      ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖ = 1 → 0 < r → r ≤ r₀ →
        0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap (a : Cover)) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ (n : ℕ → Cover) (ν : Cover), n 0 = n₀ ∧ (∀ i, ‖n i‖ = 1) ∧ ‖ν‖ = 1 ∧
        Tendsto n atTop (𝓝 ν) ∧
        (∀ i, (∫ x in Metric.closedBall (quotientMap (a : Cover)) (17*(ρ^i*r)), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2) ∧
        (∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i) := by
  obtain ⟨R₀,ρ,hR₀,hρ,hρs,hstep⟩ := isMinimizerAt_excess_contraction hV hE hmin
  obtain ⟨R,c,hR,hcpos,hd⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let C := 2/(Real.sqrt c*ρ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min R₀ R,ρ,C,lt_min hR₀ hR,hρ,hρs,hC,?_⟩
  intro μ hμ N hN hp hu
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hc hμ
  obtain ⟨δ,hδ,hdec⟩ := hstep μ hμ H hH N hN hp hu
  refine ⟨δ,hδ,?_⟩
  intro a ha n₀ r e hn₀ hr hrr he heδ hrel ht
  let T (n : Cover) (r : ℝ) := ∫ x in Metric.closedBall (quotientMap (a : Cover)) (17*r),
    ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)
  apply excess_normal_iteration T hρ hρs _ hn₀ hr hrr he heδ hrel ht
  intro n s d hn hs hsR hdpos hdδ hsd hT
  obtain ⟨ν,hν,hνT⟩ := hdec a ha n s d hn hs (hsR.trans (min_le_left _ _)) hdpos hdδ hsd hT
  refine ⟨ν,hν,hνT,?_⟩
  have ha' := ha
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin] at ha'
  have hρ1 : ρ ≤ 1 := by linarith
  have hρsR : ρ*s ≤ R := (mul_le_of_le_one_left hs.le hρ1).trans (hsR.trans (min_le_right _ _))
  exact polar_normal_step_bound hN hu (quotientMap (a : Cover)) hcpos hρ hρ1 hs hdpos.le n ν
    (hd μ hμ _ ha' (ρ*s) (mul_pos hρ hs) hρsR) hT hνT

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma polar_tilt_triangle {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (n ν : Cover) (S : Set Torus) :
    (∫ x in S, ‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      2*(∫ x in S, ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) +
      2*(spatialNormalMeasure μ : Measure Torus).real S*‖n-ν‖^2 := by
  have hn := (polar_tilt_integrable hN hu n).integrableOn (s := S)
  have hν := (polar_tilt_integrable hN hu ν).integrableOn (s := S)
  calc
    _ ≤ ∫ x in S, 2*‖N x-n‖^2+2*‖n-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus) := by
      apply integral_mono hν ((hn.const_mul 2).add (integrable_const _))
      intro x
      have hb : ‖N x-ν‖ ≤ ‖N x-n‖+‖n-ν‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (N x-n) (n-ν)
      dsimp only [Pi.add_apply]
      nlinarith [sq_nonneg (‖N x-n‖-‖n-ν‖), norm_nonneg (N x-ν),
        norm_nonneg (N x-n), norm_nonneg (n-ν)]
    _ = _ := by rw [integral_add (hn.const_mul 2) (integrable_const _),integral_const_mul,
                    integral_const,smul_eq_mul,measureReal_restrict_apply_univ]; ring

lemma iterated_tilt_limit_excess {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {ρ r e A C : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (he : 0 ≤ e) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (n : ℕ → Cover) (ν : Cover)
    (hm : ∀ s : ℝ, 0 < s → s ≤ r →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a s) ≤ A*s^2)
    (ht : ∀ i, (∫ x in Metric.closedBall a (17*(ρ^i*r)), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2)
    (hc : ∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i)
    {s : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    ∃ i : ℕ, ρ^(i+1)*r < s ∧ s ≤ ρ^i*r ∧
      normalExcess (spatialNormalMeasure μ) N a ν s ≤
        (2/ρ^2+8*A*C^2)*e^2*(1/2:ℝ)^(2*i) := by
  obtain ⟨i,hi,hsi⟩ := exists_nat_pow_near_of_lt_one (div_pos hs hr)
    ((div_le_one hr).2 hsr) hρ hρ1
  have hi' : ρ^(i+1)*r < s := (lt_div_iff₀ hr).mp hi
  have hsi' : s ≤ ρ^i*r := (div_le_iff₀ hr).mp hsi
  refine ⟨i,hi',hsi',?_⟩
  have hri : 0 < ρ^i*r := mul_pos (pow_pos hρ _) hr
  have hsub : Metric.closedBall a s ⊆ Metric.closedBall a (17*(ρ^i*r)) :=
    Metric.closedBall_subset_closedBall (by linarith)
  have htn : (∫ x in Metric.closedBall a s, ‖N x-n i‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      (ρ^i*r)^2*((1/2:ℝ)^i*e)^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu (n i)).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) hsub.eventuallyLE).trans (ht i)
  have hbound : 0 ≤ 2*C*e*(1/2:ℝ)^i :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) he) (by positivity)
  have hcn : ‖n i-ν‖^2 ≤ (2*C*e*(1/2:ℝ)^i)^2 :=
    (sq_le_sq₀ (norm_nonneg _) hbound).mpr (hc i)
  have htν := polar_tilt_triangle hN hu (n i) ν (Metric.closedBall a s)
  have hmass := mul_le_mul_of_nonneg_right (hm s hs hsr) (sq_nonneg ‖n i-ν‖)
  have hmass' := mul_le_mul_of_nonneg_left hcn (show 0 ≤ A*s^2 by positivity)
  have hrad : (ρ^i*r)^2 ≤ s^2/ρ^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).2
    rw [pow_succ] at hi'
    have hh : ρ*(ρ^i*r) < s := by nlinarith only [hi']
    have hh2 := pow_le_pow_left₀ (mul_pos hρ hri).le hh.le 2
    nlinarith only [hh2]
  have hrad' := mul_le_mul_of_nonneg_right hrad (sq_nonneg ((1/2:ℝ)^i*e))
  rw [normalExcess]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).2
  have heq : 2*(s^2/ρ^2)*((1/2:ℝ)^i*e)^2 + 2*(A*s^2)*(2*C*e*(1/2:ℝ)^i)^2 =
      ((2/ρ^2+8*A*C^2)*e^2*(1/2:ℝ)^(2*i))*s^2 := by
    rw [Nat.mul_comm 2 i, pow_mul]
    ring
  rw [← heq]
  nlinarith only [htν,htn,hmass,hmass',hrad']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma iterated_tilt_limit_excess_tendsto {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {ρ r e A C : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (he : 0 ≤ e) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (n : ℕ → Cover) (ν : Cover)
    (hm : ∀ s : ℝ, 0 < s → s ≤ r →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a s) ≤ A*s^2)
    (ht : ∀ i, (∫ x in Metric.closedBall a (17*(ρ^i*r)), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2)
    (hc : ∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i) :
    Tendsto (normalExcess (spatialNormalMeasure μ) N a ν) (𝓝[>] 0) (𝓝 0) := by
  let K := (2/ρ^2+8*A*C^2)*e^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : Tendsto (fun i : ℕ ↦ K*(1/2:ℝ)^(2*i)) atTop (𝓝 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1)).const_mul K
    simpa only [pow_mul, show (1/2:ℝ)^2 = 1/4 by norm_num, mul_zero] using hh
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [] with s
    exact hb.trans_le (div_nonneg (integral_nonneg fun x ↦ sq_nonneg _) (sq_nonneg s))
  · intro b hb
    obtain ⟨j,hj⟩ := (hq.eventually (Iio_mem_nhds hb)).exists
    have hjpos : 0 < ρ^(j+1)*r := by positivity
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hjpos)] with s hs hsrj
    have hspos : 0 < s := hs
    have hsr : s ≤ r := (show s < ρ^(j+1)*r from hsrj).le.trans
      (mul_le_of_le_one_left hr.le (pow_le_one₀ hρ.le hρ1.le))
    obtain ⟨i,hi,hsi,hexc⟩ := iterated_tilt_limit_excess hN hu a hρ hρ1 hr he hA hC n ν hm ht hc hspos hsr
    have hji : j ≤ i := by
      by_contra! hij
      have hh := mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hρ.le hρ1.le (Nat.succ_le_succ hij.le)) hr.le
      exact (not_lt_of_ge hh) (hi.trans (show s < ρ^(j+1)*r from hsrj))
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
        (Nat.mul_le_mul_left 2 hji)) hK
    exact (hexc.trans hh).trans_lt hj

lemma iterated_tilt_limit_oscillation_tendsto {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {ρ r e A C : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (he : 0 ≤ e) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (n : ℕ → Cover) {ν : Cover} (hν : ‖ν‖ = 1)
    (hm : ∀ s : ℝ, 0 < s → s ≤ r →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a s) ≤ A*s^2)
    (ht : ∀ i, (∫ x in Metric.closedBall a (17*(ρ^i*r)), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2)
    (hc : ∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i) :
    Tendsto (normalOscillation (spatialNormalMeasure μ) N a ν) (𝓝[>] 0) (𝓝 0) := by
  have htend := iterated_tilt_limit_excess_tendsto hN hu a hρ hρ1 hr he hA hC n ν hm ht hc
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0,
      normalOscillation (spatialNormalMeasure μ) N a ν s ≤
        Real.sqrt (A*normalExcess (spatialNormalMeasure μ) N a ν s) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with s hs hsr
    have hh := normalOscillation_sq_le_excess (spatialNormalMeasure μ) hN hu hν a hs (hm s hs hsr.le)
    have hnex : 0 ≤ A*normalExcess (spatialNormalMeasure μ) N a ν s :=
      mul_nonneg hA (div_nonneg (integral_nonneg fun x ↦ sq_nonneg _) (sq_nonneg s))
    have hsqrt := Real.sq_sqrt hnex
    have hsnon := Real.sqrt_nonneg (A*normalExcess (spatialNormalMeasure μ) N a ν s)
    nlinarith only [hh,hsqrt,hsnon]
  apply squeeze_zero' (Eventually.of_forall fun s ↦ normalOscillation_nonneg _ _ _ _ _) hb
  simpa only [mul_zero,Real.sqrt_zero] using (htend.const_mul A).sqrt

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma polar_normal_nearby_centers {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a b : Torus) {c r e : ℝ} (hc : 0 < c) (hr : 0 < r) (he : 0 ≤ e)
    (ha : c*r^2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r))
    (hab : dist a b ≤ r) (ν ω : Cover)
    (htν : (∫ x in Metric.closedBall a (2*r), ‖N x-ν‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2)
    (htω : (∫ x in Metric.closedBall b (2*r), ‖N x-ω‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2) :
    ‖ν-ω‖ ≤ (2/Real.sqrt c)*e := by
  have hsuba : Metric.ball a r ⊆ Metric.closedBall a (2*r) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hsubb : Metric.ball a r ⊆ Metric.closedBall b (2*r) := by
    intro x hx
    have hx' : dist x a < r := hx
    change dist x b ≤ 2*r
    linarith [dist_triangle x a b]
  have hν : (∫ x in Metric.ball a r, ‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu ν).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) hsuba.eventuallyLE).trans htν
  have hω : (∫ x in Metric.ball a r, ‖N x-ω‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu ω).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) hsubb.eventuallyLE).trans htω
  have hd := (mul_le_mul_of_nonneg_right ha (sq_nonneg ‖ν-ω‖)).trans
    (polar_tilt_difference hN hu ν ω (Metric.ball a r))
  have hh : c*‖ν-ω‖^2 ≤ 4*e^2 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).mp
    nlinarith only [hd,hν,hω]
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hs2 := Real.sq_sqrt hc.le
  have heq : (2/Real.sqrt c)*e = (2*e)/Real.sqrt c := by ring
  rw [heq]
  apply (le_div_iff₀ hs).2
  have hsquared : (‖ν-ω‖*Real.sqrt c)^2 ≤ (2*e)^2 := by
    rw [mul_pow,hs2]
    nlinarith only [hh]
  nlinarith [mul_nonneg (norm_nonneg (ν-ω)) hs.le]

lemma continuousOn_of_uniform_normal_tilt {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (S : Set Cover) (ν : Cover → Cover) {c : ℝ} (hc : 0 < c)
    (r e : ℕ → ℝ) (hr : ∀ i, 0 < r i) (he : ∀ i, 0 ≤ e i)
    (helim : Tendsto e atTop (𝓝 0))
    (hm : ∀ a ∈ S, ∀ i, c*(r i)^2 ≤
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap a) (r i)))
    (ht : ∀ a ∈ S, ∀ i, (∫ x in Metric.closedBall (quotientMap a) (2*r i), ‖N x-ν a‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) :
    ContinuousOn ν S := by
  rw [Metric.continuousOn_iff]
  intro a ha ε hε
  have hl : Tendsto (fun i ↦ (2/Real.sqrt c)*e i) atTop (𝓝 0) := by
    simpa only [mul_zero] using helim.const_mul (2/Real.sqrt c)
  obtain ⟨i,hi⟩ := (hl.eventually (Iio_mem_nhds hε)).exists
  refine ⟨r i,hr i,?_⟩
  intro b hb hba
  have hdist : dist (quotientMap a) (quotientMap b) ≤ r i := by
    rw [dist_eq_norm, ← quotientMap_sub]
    apply (norm_quotientMap_le _).trans
    rw [← dist_eq_norm,dist_comm]
    exact hba.le
  have hh := polar_normal_nearby_centers hN hu (quotientMap a) (quotientMap b) hc (hr i) (he i)
    (hm a ha i) hdist (ν a) (ν b) (ht a ha i) (ht b hb i)
  rw [dist_eq_norm,norm_sub_rev]
  exact hh.trans_lt hi

lemma polar_tilt_limit_two_radius {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {r e A C : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (n ν : Cover)
    (hm : (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a (2*r)) ≤ 16*A*r^2)
    (ht : (∫ x in Metric.closedBall a (17*r), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2)
    (hc : ‖n-ν‖ ≤ 2*C*e) :
    (∫ x in Metric.closedBall a (2*r), ‖N x-ν‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (2+128*A*C^2)*r^2*e^2 := by
  have htn : (∫ x in Metric.closedBall a (2*r), ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) (Metric.closedBall_subset_closedBall
      (by linarith : 2*r ≤ 17*r)).eventuallyLE).trans ht
  have hcn := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have hmass := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖n-ν‖)
  have hmass' := mul_le_mul_of_nonneg_left hcn (show 0 ≤ 16*A*r^2 by positivity)
  have hh := polar_tilt_triangle hN hu n ν (Metric.closedBall a (2*r))
  nlinarith only [htn,hmass,hmass',hh]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVFlatBlowupRegular
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_moving_normal_modulus_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
    ∃ r₀ C K ρ : ℝ, 0 < r₀ ∧ 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (c₀ : Cover), ‖c₀-cubeCenter‖ ≤ 1/16 → ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖ = 1 →
        0 < r → r ≤ r₀ → 0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap c₀) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ ν : Cover → Cover,
        ContinuousOn ν (quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128)) ∧
        (∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          ‖ν a‖ = 1 ∧ ‖n₀-ν a‖ ≤ C*e ∧
          BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) (ν a)) ∧
        ∀ i : ℕ, ∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          ∀ b ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
            dist a b ≤ ρ^i*(r/2) → dist (ν a) (ν b) ≤ K*e*(1/2 : ℝ)^i := by
  classical
  obtain ⟨R₀,ρ,C,hR₀,hρ,hρs,hC,hiter⟩ := isMinimizerAt_uniform_tilt_iteration hV hE hmin hcenter
  obtain ⟨U,A,hU,hA,hupper⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨L,c,hL,hc,hlower⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  obtain ⟨D,d,hD,hd,hdensity⟩ := isMinimizerAt_two_sided_density hV hE hmin
  let r₀ := min R₀ (min (U/2) (min L (1/8)))
  let M := 2+128*A*C^2
  have hM : 0 < M := by dsimp [M]; positivity
  let K := 4*Real.sqrt M/Real.sqrt c
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨r₀,4*C,K,ρ,by dsimp [r₀]; positivity,by positivity,hK,hρ,hρs,?_⟩
  intro μ hμ N hN hp hu
  obtain ⟨δ₀,hδ₀,hiteration⟩ := hiter μ hμ N hN hp hu
  refine ⟨δ₀/2,by positivity,?_⟩
  intro c₀ hc₀ n₀ r e hn₀ hr hrr he heδ hratio htilt
  have hrR : r ≤ R₀ := hrr.trans (min_le_left _ _)
  have hrU : r ≤ U/2 := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrL : r ≤ L := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrs : r ≤ 1/8 := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have heδ₀ : 2*e ≤ δ₀ := by linarith
  have hratio' : (r/2)/(2*e)^2 ≤ δ₀ := by
    have heq : (r/2)/(2*e)^2 = (r/e^2)/8 := by ring
    rw [heq]
    linarith
  let S := quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128)
  have hdata : ∀ a : Cover, ∃ ν : Cover, a ∈ S → ‖ν‖ = 1 ∧ ‖n₀-ν‖ ≤ 4*C*e ∧
      BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) ν ∧
      ∀ i : ℕ, (∫ z in Metric.closedBall (quotientMap a) (2*(ρ^i*(r/2))), ‖N z-ν‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*(r/2))^2*
          (Real.sqrt M*((1/2:ℝ)^i*(2*e)))^2 := by
    intro a
    by_cases ha : a ∈ S
    swap
    · exact ⟨n₀,fun h ↦ (ha h).elim⟩
    have hac : ‖a-c₀‖ < r/128 := by simpa only [Metric.mem_ball,dist_eq_norm] using ha.2
    let a' : InteriorCenter := ⟨a,by
      have hh := norm_sub_le_norm_sub_add_norm_sub a c₀ cubeCenter
      linarith⟩
    have hsub : Metric.closedBall (quotientMap a) (17*(r/2)) ⊆
        Metric.closedBall (quotientMap c₀) (17*r) := by
      intro z hz
      have hz' : dist z (quotientMap a) ≤ 17*(r/2) := hz
      have hdist : dist (quotientMap a) (quotientMap c₀) ≤ r/128 := by
        rw [dist_eq_norm, ← quotientMap_sub]
        exact (norm_quotientMap_le _).trans hac.le
      change dist z (quotientMap c₀) ≤ 17*r
      linarith [dist_triangle z (quotientMap a) (quotientMap c₀)]
    have ht' : (∫ z in Metric.closedBall (quotientMap a) (17*(r/2)), ‖N z-n₀‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
      (setIntegral_mono_set (polar_tilt_integrable hN hu n₀).integrableOn
      (Eventually.of_forall fun z ↦ sq_nonneg _) hsub.eventuallyLE).trans htilt
    have ht'' : (∫ z in Metric.closedBall (quotientMap (a' : Cover)) (17*(r/2)), ‖N z-n₀‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r/2)^2*(2*e)^2 := by
      convert ht' using 1 <;> first | rfl | ring
    obtain ⟨n,ν,hnzero,hn,hν,hnt,ht,hclose⟩ := hiteration a' ha.1 n₀ (r/2) (2*e) hn₀
      (by positivity) (by linarith) (by positivity) heδ₀ hratio' ht''
    have hmass : ∀ s : ℝ, 0 < s → s ≤ r/2 →
        (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall (quotientMap a) s) ≤ (4*A)*s^2 := by
      intro s hs hsr
      have hh := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : s < 2*s))).trans
        (hupper μ hμ (quotientMap a) (2*s) (by positivity) (by linarith))
      nlinarith only [hh]
    have hosc := iterated_tilt_limit_oscillation_tendsto hN hu (quotientMap a) hρ
      (by linarith : ρ < 1) (by positivity : 0 < r/2) (by positivity : 0 ≤ 2*e)
      (by positivity : 0 ≤ 4*A) hC.le n hν hmass ht hclose
    have hd' : ∀ a ∈ frontier (openRepresentative E), ∀ t : ℝ, 0 < t → t ≤ D →
        d*t^3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
        d*t^3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t) := by
      rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
      exact hdensity
    refine ⟨ν,fun _ ↦ ⟨hν,?_,normal_oscillation_implies_boundary_flatness hE hμ hN hp hu hD hd hd' ha.1 hν hosc,?_⟩⟩
    · have hh := hclose 0
      rw [hnzero,pow_zero,mul_one] at hh
      nlinarith only [hh]
    · intro i
      have hi : 0 < ρ^i*(r/2) := by positivity
      have hir : ρ^i*(r/2) ≤ r/2 := mul_le_of_le_one_left (by positivity)
        (pow_le_one₀ hρ.le (by linarith))
      have hm : (spatialNormalMeasure μ : Measure Torus).real
          (Metric.closedBall (quotientMap a) (2*(ρ^i*(r/2)))) ≤ 16*A*(ρ^i*(r/2))^2 := by
        have hh := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : 2*(ρ^i*(r/2)) < 4*(ρ^i*(r/2))))).trans
          (hupper μ hμ (quotientMap a) (4*(ρ^i*(r/2))) (by positivity) (by linarith))
        nlinarith only [hh]
      have hci : ‖n i-ν‖ ≤ 2*C*((1/2:ℝ)^i*(2*e)) := by
        convert hclose i using 1 <;> first | rfl | ring
      have hh := polar_tilt_limit_two_radius hN hu (quotientMap a) hi hA.le (n i) ν hm (ht i) hci
      rw [mul_pow (Real.sqrt M),Real.sq_sqrt hM.le]
      dsimp [M] at *
      nlinarith only [hh]
  choose ν hν using hdata
  refine ⟨ν,?_,fun a ha ↦ ⟨(hν a ha).1,(hν a ha).2.1,(hν a ha).2.2.1⟩,?_⟩
  · apply continuousOn_of_uniform_normal_tilt hN hu S ν hc
      (fun i ↦ ρ^i*(r/2)) (fun i ↦ Real.sqrt M*((1/2:ℝ)^i*(2*e)))
      (fun i ↦ by positivity) (fun i ↦ by positivity)
    · have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (1/2:ℝ) < 1)).mul_const (2*e)).const_mul (Real.sqrt M)
      simpa only [zero_mul,mul_zero] using hh
    · intro a ha i
      apply hlower μ hμ (quotientMap a)
      · rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
        exact ha.1
      · positivity
      · have hh : ρ^i*(r/2) ≤ r/2 := mul_le_of_le_one_left (by positivity)
          (pow_le_one₀ hρ.le (by linarith))
        linarith
    · exact fun a ha i ↦ (hν a ha).2.2.2 i
  · intro i a ha b hb hab
    have hri : 0 < ρ^i*(r/2) := by positivity
    have hris : ρ^i*(r/2) ≤ r/2 := mul_le_of_le_one_left (by positivity)
      (pow_le_one₀ hρ.le (by linarith))
    have hmass : c*(ρ^i*(r/2))^2 ≤
        (spatialNormalMeasure μ : Measure Torus).real
          (Metric.ball (quotientMap a) (ρ^i*(r/2))) := by
      apply hlower μ hμ (quotientMap a)
      · rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
        exact ha.1
      · exact hri
      · linarith
    have hdist : dist (quotientMap a) (quotientMap b) ≤ ρ^i*(r/2) := by
      rw [dist_eq_norm,← quotientMap_sub]
      exact (norm_quotientMap_le _).trans (by simpa only [dist_eq_norm] using hab)
    have hh := polar_normal_nearby_centers hN hu (quotientMap a) (quotientMap b)
      hc hri (by positivity : 0 ≤ Real.sqrt M*((1/2 : ℝ)^i*(2*e)))
      hmass hdist (ν a) (ν b) ((hν a ha).2.2.2 i) ((hν b hb).2.2.2 i)
    rw [dist_eq_norm]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [K]
    ring

end CubicTorus.MovingCenter

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus_oai := @OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus_oai
