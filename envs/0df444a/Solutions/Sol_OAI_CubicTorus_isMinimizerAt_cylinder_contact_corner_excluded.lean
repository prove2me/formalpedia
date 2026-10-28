-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_cylinder_contact_corner_excluded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:40:53.201347+00:00
-- url     : https://prove2.me/submissions/d3d1718a-5520-4f15-bec6-6bad9b2c2bf5

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_Periodic_profile_hessian_of_CMC
import Theorems.Thm_OAI_CubicTorus_fourCorner_normalized_contradiction
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_four_corner_necessary_data
import Theorems.Thm_OAI_CubicTorus_profile_ge_second_chord

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

theorem finitePerimeter_stripe {V : ℝ} (hV : V ∈ Icc 0 1) : FinitePerimeter (stripe V) :=
  ⟨(measurableSet_stripe V).nullMeasurableSet, (perimeter_stripe_le hV).trans_lt (by norm_num)⟩

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

lemma isoperimetricProfile_zero : isoperimetricProfile 0 = 0 := by
  rw [isoperimetricProfile_eq_of_isMinimizerAt isMinimizerAt_empty, perimeter_empty,
    ENNReal.toReal_zero, zero_div]

lemma isoperimetricProfile_one : isoperimetricProfile 1 = 0 := by
  rw [isoperimetricProfile_eq_of_isMinimizerAt isMinimizerAt_univ]
  have hh : perimeter (univ : Set Torus) = 0 := by
    simpa only [compl_empty, perimeter_empty] using perimeter_compl ((MeasurableSet.empty : MeasurableSet (∅ : Set Torus)).nullMeasurableSet (μ := torusVolume))
  rw [hh, ENNReal.toReal_zero, zero_div]

lemma isoperimetricProfile_pos {V : ℝ} (hV : V ∈ Ioo 0 1) :
    0 < isoperimetricProfile V := by
  obtain ⟨E, hE⟩ := exists_isMinimizerAt hV
  rw [isoperimetricProfile_eq_of_isMinimizerAt hE]
  exact div_pos (ENNReal.toReal_pos (perimeter_pos_of_volume hV hE.1.1 hE.2.1).ne'
    hE.1.2.ne) (by norm_num)

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

lemma continuous_coordinateNormalVelocity (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun z : NormalBundle ↦ coordinateNormalVelocity i f z.1 z.2) := by
  unfold coordinateNormalVelocity
  exact ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).sub
    (((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ) continuous_const).smul
      ((gradient_contDiff hf).continuous.comp (continuous_subtype_val.comp continuous_fst)))

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

lemma inner_coordinateNormalVelocity (i : Fin 3) (f : Cover → ℝ) (x : Cover)
    {n : Cover} (hn : ‖n‖ = 1) :
    ⟪n, coordinateNormalVelocity i f x n⟫ =
      fderiv ℝ f x (EuclideanSpace.single i 1) - n i * fderiv ℝ f x n := by
  simp only [coordinateNormalVelocity, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hn, one_pow, mul_one, inner_gradient_right,
    conj_trivial]
  congr 1
  simp [PiLp.inner_apply, EuclideanSpace.single]

lemma tangentialDivergence_eq_sum {F : Cover → Cover} {x n : Cover}
    (hF : DifferentiableAt ℝ F x) (hn : ‖n‖ = 1) :
    tangentialDivergence F x n = ∑ i : Fin 3,
      ⟪n, coordinateNormalVelocity i (fun y ↦ F y i) x n⟫ := by
  simp_rw [inner_coordinateNormalVelocity _ _ _ hn, fderiv_component hF]
  simp only [Finset.sum_sub_distrib, tangentialDivergence, divergence]
  congr 1
  simp [PiLp.inner_apply, mul_comm]

lemma integral_tangentialDivergence_eq_sum {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (μ : FiniteMeasure NormalBundle) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      ∑ i : Fin 3, ∫ z, ⟪(z.2 : Cover),
        coordinateNormalVelocity i (fun y ↦ F y i) z.1 z.2⟫ ∂(μ : Measure NormalBundle) := by
  have he (z : NormalBundle) := tangentialDivergence_eq_sum (x := (z.1 : Cover))
    (hF.differentiable (by simp)).differentiableAt z.2.property
  simp_rw [he]
  apply integral_finsetSum
  intro i _
  exact (continuous_normalUnit.inner (𝕜 := ℝ)
    (continuous_coordinateNormalVelocity i
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVSharpUpperBound
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
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus.UpperComparison

lemma fieldMove_hasFDerivAt {F : Cover → Cover} {x : Cover}
    (hf : DifferentiableAt ℝ F x) (t : ℝ) :
    HasFDerivAt (fieldMove F t) (fieldMoveDeriv F t x) x :=
  (hasFDerivAt_id x).add (hf.hasFDerivAt.const_smul t)

lemma fieldMoveDeriv_det (F : Cover → Cover) (t : ℝ) (x : Cover) :
    (fieldMoveDeriv F t x).det =
      1 + t * divergence F x + t ^ 2 * secondJacobian F x + t ^ 3 * thirdJacobian F x := by
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : LinearMap.toMatrix B B (fieldMoveDeriv F t x).toLinearMap =
      Matrix.of (fun j k ↦ (if j = k then 1 else 0) + t * derivativeEntry F x j k) := by
    ext j k
    rw [LinearMap.toMatrix_apply]
    change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
      (fieldMoveDeriv F t x ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) j = _
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply]
    simp [fieldMoveDeriv, derivativeEntry]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, he]
  simp [Matrix.det_fin_three, divergence, secondJacobian, thirdJacobian,
    derivativeEntry, Fin.sum_univ_succ]
  ring

lemma fieldMove_injective {F : Cover → Cover} (hf : Differentiable ℝ F)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ M) {t : ℝ}
    (ht : |t| * M < 1) : Function.Injective (fieldMove F t) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro x y hxy
  have he : x - y = (-t) • (F x - F y) := by
    calc
      x - y = fieldMove F t x - fieldMove F t y - t • (F x - F y) := by
        unfold fieldMove
        module
      _ = _ := by rw [hxy, sub_self, zero_sub, neg_smul]
  have hn : ‖x - y‖ = |t| * ‖F x - F y‖ := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg]
  have hh : ‖x - y‖ ≤ |t| * M * ‖x - y‖ := by
    calc
      ‖x - y‖ = |t| * ‖F x - F y‖ := hn
      _ ≤ |t| * ((M : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hLip.norm_sub_le x y) (abs_nonneg _)
      _ = _ := by ring
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

lemma continuous_derivativeEntry {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (i j : Fin 3) : Continuous (fun x ↦ derivativeEntry F x i j) := by
  exact (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma continuous_secondJacobian {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (secondJacobian F) := by
  unfold secondJacobian
  exact (((((continuous_derivativeEntry hf 0 0).mul (continuous_derivativeEntry hf 1 1)).add
    ((continuous_derivativeEntry hf 0 0).mul (continuous_derivativeEntry hf 2 2))).add
    ((continuous_derivativeEntry hf 1 1).mul (continuous_derivativeEntry hf 2 2))).sub
    ((continuous_derivativeEntry hf 0 1).mul (continuous_derivativeEntry hf 1 0))).sub
    ((continuous_derivativeEntry hf 0 2).mul (continuous_derivativeEntry hf 2 0)) |>.sub
    ((continuous_derivativeEntry hf 1 2).mul (continuous_derivativeEntry hf 2 1))

lemma continuous_thirdJacobian {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (thirdJacobian F) := by
  exact (continuous_pi fun i ↦ continuous_pi fun j ↦
    continuous_derivativeEntry hf i j).matrix_det

lemma integral_det_fieldMove {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    {A : Set Cover} (hAc : IsCompact (closure A)) (t : ℝ) :
    (∫ x in A, (fieldMoveDeriv F t x).det) = volume.real A +
      t * (∫ x in A, divergence F x) + t ^ 2 * (∫ x in A, secondJacobian F x) +
      t ^ 3 * (∫ x in A, thirdJacobian F x) := by
  have h1 : IntegrableOn (divergence F) (closure A) volume :=
    (continuous_divergence hf).continuousOn.integrableOn_compact hAc
  have h2 : IntegrableOn (secondJacobian F) (closure A) volume :=
    (continuous_secondJacobian hf).continuousOn.integrableOn_compact hAc
  have h3 : IntegrableOn (thirdJacobian F) (closure A) volume :=
    (continuous_thirdJacobian hf).continuousOn.integrableOn_compact hAc
  have hμ : volume A < ⊤ := (measure_mono subset_closure).trans_lt hAc.measure_lt_top
  have hc : IntegrableOn (fun _ : Cover ↦ (1 : ℝ)) A :=
    integrableOn_const hμ.ne
  simp_rw [fieldMoveDeriv_det]
  rw [integral_add (μ := volume.restrict A) (f := fun x ↦ 1 + t * divergence F x + t^2 * secondJacobian F x)
      (g := fun x ↦ t^3 * thirdJacobian F x)
      (by simpa only [IntegrableOn, Pi.add_def] using
        ((hc.add ((h1.mono_set subset_closure).const_mul t)).add
          ((h2.mono_set subset_closure).const_mul (t^2))))
      ((h3.mono_set subset_closure).const_mul (t^3)),
    integral_add (μ := volume.restrict A) (f := fun x ↦ 1 + t * divergence F x)
      (g := fun x ↦ t^2 * secondJacobian F x)
      (by simpa only [IntegrableOn, Pi.add_def] using
        (hc.add ((h1.mono_set subset_closure).const_mul t)))
      ((h2.mono_set subset_closure).const_mul (t^2)),
    integral_add (μ := volume.restrict A) (f := fun _ : Cover ↦ (1 : ℝ)) (g := fun x ↦ t * divergence F x)
      hc ((h1.mono_set subset_closure).const_mul t)]
  simp only [integral_const_mul, setIntegral_const, smul_eq_mul, mul_one]

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison
open Filter
open scoped Topology

lemma integral_det_fieldMove_le_volume {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {A : Set Cover} (hA : MeasurableSet A)
    (hAc : IsCompact (closure A)) :
    (∫ x in A, (fieldMoveDeriv F t x).det) ≤ volume.real (fieldMove F t '' A) := by
  have hdet : Continuous (fun x ↦ (fieldMoveDeriv F t x).det) :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add ((hf.continuous_fderiv (by simp)).const_smul t))
  have hi : IntegrableOn (fun x ↦ (fieldMoveDeriv F t x).det) A volume :=
    (hdet.continuousOn.integrableOn_compact hAc).mono_set subset_closure
  have hj := integral_image_eq_integral_abs_det_fderiv_smul volume hA
    (fun x (_ : x ∈ A) ↦
      (fieldMove_hasFDerivAt (hf.differentiable (by simp) x) t).hasFDerivWithinAt)
    (fieldMove_injective (hf.differentiable (by simp)) hM ht).injOn (fun _ ↦ (1 : ℝ))
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hj
  rw [hj]
  exact integral_mono hi hi.abs (fun x ↦ le_abs_self _)

lemma realVolume_cover_ball (c : Cover) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.ball c r) = r ^ 3 * (Real.pi * 4 / 3) := by
  simp only [Measure.real_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity :
      0 ≤ Real.pi * 4 / 3)]

lemma fieldMove_ball_subset {F : Cover → Cover} (hF : ∀ x, ‖F x‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (c : Cover) (r : ℝ) :
    fieldMove F t '' Metric.ball c r ⊆ Metric.ball c (r + t) := by
  rintro _ ⟨x, hx, rfl⟩
  have hh : ‖t • F x‖ ≤ t := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_one] using
      mul_le_mul_of_nonneg_left (hF x) ht
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  calc
    ‖fieldMove F t x - c‖ = ‖(x - c) + t • F x‖ := by congr 1; unfold fieldMove; abel
    _ ≤ ‖x - c‖ + ‖t • F x‖ := norm_add_le _ _
    _ < r + t := add_lt_add_of_lt_of_le hx hh

lemma flux_cover_ball_le {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (hF : ∀ x, ‖F x‖ ≤ 1) (c : Cover) {r : ℝ} (hr : 0 < r) :
    (∫ x in Metric.ball c r, divergence F x) ≤ 4 * Real.pi * r ^ 2 := by
  obtain ⟨M, hM0, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  let MN : NNReal := ⟨M, hM0⟩
  have hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ MN := fun x ↦ by exact_mod_cast hbound x
  let P := ∫ x in Metric.ball c r, divergence F x
  let Q := ∫ x in Metric.ball c r, secondJacobian F x
  let R := ∫ x in Metric.ball c r, thirdJacobian F x
  have hind : ∀ t : ℝ, 0 < t → t < 1 / (M + 1) →
      P + t * Q + t ^ 2 * R ≤
        4 * Real.pi * r ^ 2 + 4 * Real.pi * r * t + (Real.pi * 4 / 3) * t ^ 2 := by
    intro t ht0 ht1
    have htM : |t| * MN < 1 := by
      rw [abs_of_pos ht0]
      change t * M < 1
      have hh := (lt_div_iff₀ (by positivity : 0 < M+1)).1 ht1
      nlinarith
    have hv := integral_det_fieldMove_le_volume hf hM htM (A := Metric.ball c r) Metric.isOpen_ball.measurableSet
      (Metric.isBounded_ball.isCompact_closure)
    have hv' : volume.real (fieldMove F t '' Metric.ball c r) ≤
        volume.real (Metric.ball c (r + t)) := by
      exact ENNReal.toReal_mono measure_ball_ne_top (measure_mono (fieldMove_ball_subset hF ht0.le c r))
    rw [integral_det_fieldMove hf Metric.isBounded_ball.isCompact_closure,
      realVolume_cover_ball c hr.le] at hv
    rw [realVolume_cover_ball c (by linarith)] at hv'
    have hh := hv.trans hv'
    change r^3 * (Real.pi*4/3) + t*P + t^2*Q + t^3*R ≤ _ at hh
    apply (mul_le_mul_iff_right₀ ht0).mp
    nlinarith
  have htend₁ : Tendsto (fun t : ℝ ↦ P + t * Q + t^2 * R) (𝓝[>] (0 : ℝ)) (𝓝 P) := by
    have hh : Continuous (fun t : ℝ ↦ P + t * Q + t^2 * R) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have htend₂ : Tendsto (fun t : ℝ ↦ 4 * Real.pi * r^2 + 4 * Real.pi * r * t +
      (Real.pi * 4 / 3) * t^2) (𝓝[>] (0 : ℝ)) (𝓝 (4 * Real.pi * r^2)) := by
    have hh : Continuous (fun t : ℝ ↦ 4 * Real.pi * r^2 + 4 * Real.pi * r * t +
        (Real.pi * 4 / 3) * t^2) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto htend₁ htend₂
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (M+1))).filter_mono nhdsWithin_le_nhds]
    with t ht0 ht1
  exact hind t ht0 ht1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

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

lemma perimeter_cubeBall_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    perimeter (cubeBall r) ≤ ENNReal.ofReal (4 * Real.pi * r ^ 2) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  rw [cubeBall_lift hr1]
  exact ENNReal.ofReal_le_ofReal (flux_cover_ball_le hF.1 hF.2.1 hF.2.2 cubeCenter hr0)

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

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

lemma perimeter_centeredBall_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    perimeter (Metric.ball (0 : Torus) r) ≤ ENNReal.ofReal (4 * Real.pi * r ^ 2) := by
  rw [centeredBall_eq_cubeBall_preimage,
    perimeter_translation (measurableSet_cubeBall r).nullMeasurableSet]
  exact perimeter_cubeBall_le hr0 hr1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma discProjection_norm_le (x : Cover) : ‖discProjection x‖ ≤ ‖x‖ := by
  have hh : ‖discProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [discProjection_apply, Fin.sum_univ_succ]
    nlinarith [sq_nonneg ‖x 0‖]
  nlinarith [norm_nonneg (discProjection x), norm_nonneg x]

lemma continuous_tubeSplit_symm : Continuous tubeSplit.symm := by
  apply (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ ℝ)).continuous_symm.comp
  apply continuous_pi
  intro i
  change Continuous (fun p : ℝ × Plane ↦ tubeSplit.symm p i)
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [tubeSplit_symm_zero] using (continuous_fst : Continuous (fun p : ℝ × Plane ↦ p.1))
  · simp_rw [tubeSplit_symm_succ]
    fun_prop

lemma tubeSplit_measurePreserving : MeasurePreserving tubeSplit := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

lemma measurableSet_coverTube (r : ℝ) : MeasurableSet (coverTube r) :=
  (measurableSet_Ico.prod Metric.isOpen_ball.measurableSet).preimage tubeSplit.measurable

lemma isCompact_closure_coverTube (r : ℝ) : IsCompact (closure (coverTube r)) := by
  have hc : IsCompact (tubeSplit.symm '' (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall discCenter r)) :=
    (isCompact_Icc.prod (isCompact_closedBall discCenter r)).image continuous_tubeSplit_symm
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro x hx
  refine ⟨tubeSplit x, ⟨⟨hx.1.1, hx.1.2.le⟩, Metric.ball_subset_closedBall hx.2⟩, ?_⟩
  exact tubeSplit.symm_apply_apply x

lemma volume_coverTube {r : ℝ} (hr : 0 ≤ r) :
    volume (coverTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [coverTube, tubeSplit_measurePreserving.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
      EuclideanSpace.volume_ball_fin_two]
    simp only [sub_zero, ENNReal.ofReal_one, one_mul]
    rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr]
    ring
  · exact (measurableSet_Ico.prod Metric.isOpen_ball.measurableSet).nullMeasurableSet

lemma volumeReal_coverTube {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coverTube r) = Real.pi * r^2 := by
  rw [Measure.real_def, volume_coverTube hr, ENNReal.toReal_ofReal (by positivity)]

lemma axialProjection_norm_le (x : Cover) : ‖axialProjection x‖ ≤ ‖x‖ := by
  have hh : ‖axialProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_succ, axialProjection_zero, axialProjection_succ, norm_zero,
      zero_pow (by omega : 2 ≠ 0), zero_add]
    nlinarith [sq_nonneg ‖x 0‖]
  nlinarith [norm_nonneg (axialProjection x), norm_nonneg x]

lemma fieldMove_coverTube_subset {F : Cover → Cover} (hF : ∀ x, ‖F x‖ ≤ 1)
    (hF0 : ∀ x, F x 0 = 0) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    fieldMove F t '' coverTube r ⊆ coverTube (r+t) := by
  rintro _ ⟨x, hx, rfl⟩
  change (fieldMove F t x) 0 ∈ Ico (0 : ℝ) 1 ∧
    discProjection (fieldMove F t x) ∈ Metric.ball discCenter (r+t)
  constructor
  · simpa [fieldMove, hF0 x] using hx.1
  · have hb : ‖discProjection (F x)‖ ≤ 1 := (discProjection_norm_le _).trans (hF x)
    have hh : ‖t • discProjection (F x)‖ ≤ t := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_one] using
        mul_le_mul_of_nonneg_left hb ht
    have hd : ‖discProjection x - discCenter‖ < r := by
      simpa only [tubeSplit_apply, Metric.mem_ball, dist_eq_norm] using hx.2
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      _ = ‖(discProjection x - discCenter) + t • discProjection (F x)‖ := by
        congr 1
        simp only [fieldMove, map_add, map_smul]
        abel
      _ ≤ ‖discProjection x - discCenter‖ + ‖t • discProjection (F x)‖ := norm_add_le _ _
      _ < r+t := add_lt_add_of_lt_of_le hd hh

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma tubeSplit_symm_line (u : ℝ) (y : Plane) :
    tubeSplit.symm (u,y) = tubeSplit.symm (0,y) + u • EuclideanSpace.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

lemma hasDerivAt_tubeLine (u : ℝ) (y : Plane) :
    HasDerivAt (fun t : ℝ ↦ tubeSplit.symm (t,y)) (EuclideanSpace.single 0 1) u := by
  have he : (fun t : ℝ ↦ tubeSplit.symm (t,y)) =
      (fun t : ℝ ↦ tubeSplit.symm (0,y) + t • EuclideanSpace.single 0 1) :=
    funext (fun t ↦ tubeSplit_symm_line t y)
  rw [he]
  simpa! only [Pi.add_def, zero_add, one_smul, id_eq] using
    (hasDerivAt_const u (tubeSplit.symm (0,y))).add
      ((hasDerivAt_id u).smul_const (EuclideanSpace.single 0 1))

lemma axial_integral_eq_zero {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (y : Plane) :
    (∫ u in Ico (0 : ℝ) 1, derivativeEntry F (tubeSplit.symm (u,y)) 0 0) = 0 := by
  have hd (u : ℝ) : HasDerivAt (fun u ↦ F (tubeSplit.symm (u,y)) 0)
      (derivativeEntry F (tubeSplit.symm (u,y)) 0 0) u := by
    exact (EuclideanSpace.proj 0).hasFDerivAt.comp_hasDerivAt u
      (((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt u
        (hasDerivAt_tubeLine u y))
  have hc : Continuous (fun u ↦ derivativeEntry F (tubeSplit.symm (u,y)) 0 0) :=
    (continuous_derivativeEntry hf 0 0).comp (continuous_tubeSplit_symm.comp (by fun_prop))
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u) (hc.intervalIntegrable 0 1)]
  have he : tubeSplit.symm (1,y) = tubeSplit.symm (0,y) + latticeVector (Pi.single 0 1) := by
    rw [tubeSplit_symm_line 1 y]
    congr 1
    ext i
    simp [latticeVector, Pi.single_apply]
  rw [he, hp]
  simp

lemma integral_axial_coverTube {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (r : ℝ) :
    (∫ x in coverTube r, derivativeEntry F x 0 0) = 0 := by
  let g : ℝ × Plane → ℝ := fun p ↦ derivativeEntry F (tubeSplit.symm p) 0 0
  have hint : IntegrableOn (fun x ↦ derivativeEntry F x 0 0) (coverTube r) :=
    ((continuous_derivativeEntry hf 0 0).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure
  have hi : IntegrableOn g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r) volume := by
    rw [← tubeSplit_measurePreserving.integrableOn_comp_preimage tubeSplit.measurableEmbedding]
    simpa only [g, Function.comp_def, tubeSplit.symm_apply_apply, coverTube] using hint
  have he := tubeSplit_measurePreserving.setIntegral_preimage_emb tubeSplit.measurableEmbedding
    g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r)
  simp only [g, tubeSplit.symm_apply_apply] at he
  change (∫ x in coverTube r, derivativeEntry F x 0 0) = _ at he
  rw [he]
  change (∫ p in Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r, g p) = 0
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  rw [integral_prod_symm g hi]
  simp only [g, axial_integral_eq_zero hf hp, integral_zero]

lemma divergence_axialProjection {x : Cover} {F : Cover → Cover} (hf : DifferentiableAt ℝ F x) :
    divergence (fun y ↦ axialProjection (F y)) x = divergence F x - derivativeEntry F x 0 0 := by
  have hc : HasFDerivAt (fun y ↦ axialProjection (F y))
      (axialProjection.comp (fderiv ℝ F x)) x :=
    axialProjection.hasFDerivAt.comp x hf.hasFDerivAt
  simp only [divergence, hc.fderiv, ContinuousLinearMap.comp_apply, Fin.sum_univ_succ,
    axialProjection_zero, axialProjection_succ, derivativeEntry]
  ring

lemma flux_axialProjection {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (r : ℝ) :
    (∫ x in coverTube r, divergence (fun y ↦ axialProjection (F y)) x) =
      ∫ x in coverTube r, divergence F x := by
  simp_rw [divergence_axialProjection ((hf.differentiable (by simp)).differentiableAt)]
  rw [integral_sub]
  · rw [integral_axial_coverTube hf hp, sub_zero]
  · exact ((continuous_divergence hf).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure
  · exact ((continuous_derivativeEntry hf 0 0).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison
open Filter
open scoped Topology

lemma flux_coverTube_axial_le {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (hF : ∀ x, ‖F x‖ ≤ 1) (hF0 : ∀ x, F x 0 = 0) {r : ℝ} (hr : 0 < r) :
    (∫ x in coverTube r, divergence F x) ≤ 2 * Real.pi * r := by
  obtain ⟨M, hM0, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  let MN : NNReal := ⟨M, hM0⟩
  have hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ MN := fun x ↦ by exact_mod_cast hbound x
  let P := ∫ x in coverTube r, divergence F x
  let Q := ∫ x in coverTube r, secondJacobian F x
  let R := ∫ x in coverTube r, thirdJacobian F x
  have hind : ∀ t : ℝ, 0 < t → t < 1 / (M+1) →
      P + t*Q + t^2*R ≤ 2 * Real.pi * r + Real.pi*t := by
    intro t ht0 ht1
    have htM : |t| * MN < 1 := by
      rw [abs_of_pos ht0]
      change t*M < 1
      have hh := (lt_div_iff₀ (by positivity : 0 < M+1)).1 ht1
      nlinarith
    have hv := integral_det_fieldMove_le_volume hf hM htM
      (measurableSet_coverTube r) (isCompact_closure_coverTube r)
    have hfin : volume (coverTube (r+t)) ≠ ⊤ := by
      rw [volume_coverTube (by linarith)]
      exact ENNReal.ofReal_ne_top
    have hv' : volume.real (fieldMove F t '' coverTube r) ≤ volume.real (coverTube (r+t)) :=
      ENNReal.toReal_mono hfin (measure_mono (fieldMove_coverTube_subset hF hF0 ht0.le r))
    rw [integral_det_fieldMove hf (isCompact_closure_coverTube r)] at hv
    rw [volumeReal_coverTube (by linarith : 0 ≤ r+t)] at hv'
    rw [volumeReal_coverTube hr.le] at hv
    change Real.pi*r^2 + t*P + t^2*Q + t^3*R ≤ _ at hv
    apply (mul_le_mul_iff_right₀ ht0).mp
    nlinarith [hv.trans hv']
  have htend₁ : Tendsto (fun t : ℝ ↦ P + t*Q + t^2*R) (𝓝[>] (0 : ℝ)) (𝓝 P) := by
    have hh : Continuous (fun t : ℝ ↦ P + t*Q + t^2*R) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have htend₂ : Tendsto (fun t : ℝ ↦ 2*Real.pi*r + Real.pi*t)
      (𝓝[>] (0 : ℝ)) (𝓝 (2*Real.pi*r)) := by
    have hh : Continuous (fun t : ℝ ↦ 2*Real.pi*r + Real.pi*t) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto htend₁ htend₂
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1/(M+1))).filter_mono nhdsWithin_le_nhds]
    with t ht0 ht1
  exact hind t ht0 ht1

lemma flux_coverTube_le {F : Cover → Cover} (hF : AdmissibleField F)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in coverTube r, divergence F x) ≤ 2 * Real.pi * r := by
  rw [← flux_axialProjection hF.1 hF.2.1 r]
  apply flux_coverTube_axial_le (axialProjection.contDiff.comp hF.1)
  · intro n x
    change axialProjection (F (x + latticeVector n)) = axialProjection (F x)
    rw [hF.2.1]
  · intro x
    exact (axialProjection_norm_le _).trans (hF.2.2 x)
  · intro x
    exact axialProjection_zero (F x)
  · exact hr

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma representative_mem_cube (x : Torus) : representative x ∈ fundamentalCube := by
  intro i
  exact ⟨((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.1,
    by simpa! only [representative, PiLp.toLp_apply, zero_add] using
      ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.2⟩

lemma coverTube_subset_cube {r : ℝ} (hr : r ≤ 1/2) : coverTube r ⊆ fundamentalCube := by
  intro x hx i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact hx.1
  · have hnorm : ‖discProjection x - discCenter‖ < r := by
      simpa only [tubeSplit_apply, Metric.mem_ball, dist_eq_norm] using hx.2
    have hi := (PiLp.norm_apply_le (discProjection x - discCenter) j).trans_lt hnorm
    change |x j.succ - (1/2 : ℝ)| < r at hi
    rw [abs_lt] at hi
    constructor <;> linarith

lemma measurableSet_cubeTube (r : ℝ) : MeasurableSet (cubeTube r) :=
  (measurableSet_coverTube r).preimage measurable_representative

lemma cubeTube_lift {r : ℝ} (hr : r ≤ 1/2) :
    fundamentalCube ∩ quotientMap ⁻¹' cubeTube r = coverTube r := by
  ext x
  constructor
  · rintro ⟨hx, ht⟩
    change representative (quotientMap x) ∈ coverTube r at ht
    rwa [representative_quotientMap_of_mem hx] at ht
  · intro ht
    have hx := coverTube_subset_cube hr ht
    refine ⟨hx, ?_⟩
    change representative (quotientMap x) ∈ coverTube r
    rwa [representative_quotientMap_of_mem hx]

lemma volume_cubeTube {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2) :
    torusVolume (cubeTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeTube r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeTube r)), inter_comm,
    cubeTube_lift hr1, volume_coverTube hr0]

lemma perimeter_cubeTube_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2) :
    perimeter (cubeTube r) ≤ ENNReal.ofReal (2 * Real.pi * r) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  rw [cubeTube_lift hr1]
  exact ENNReal.ofReal_le_ofReal (flux_coverTube_le hF hr0)

lemma norm_representative_sub_half (x : Torus) (i : Fin 3) :
    ‖representative x i - (1/2 : ℝ)‖ = ‖x i - ((1/2 : ℝ) : AddCircle (1 : ℝ))‖ := by
  have hi := representative_mem_cube x i
  have hb : |representative x i - (1/2 : ℝ)| ≤ |(1 : ℝ)|/2 := by
    rw [abs_one, abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hn : ‖((representative x i - (1/2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1/2 : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 hb
  have hxi : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i :=
    congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [map_sub, hxi, Real.norm_eq_abs] using hn.symm

lemma mem_cubeTube_iff {r : ℝ} (hr : 0 ≤ r) (x : Torus) :
    x ∈ cubeTube r ↔ x - quotientMap cubeCenter ∈ centeredTube r := by
  change (representative x 0 ∈ Ico (0 : ℝ) 1 ∧
    discProjection (representative x) ∈ Metric.ball discCenter r) ↔ _
  simp only [mem_Ico]
  rw [and_iff_right (representative_mem_cube x 0), Metric.mem_ball, dist_eq_norm,
    ← sq_lt_sq₀ (norm_nonneg _) hr, PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, discProjection_apply, discCenter,
    norm_representative_sub_half]
  rfl

lemma centeredTube_eq_cubeTube_preimage {r : ℝ} (hr : 0 ≤ r) :
    centeredTube r = (fun x ↦ x + quotientMap cubeCenter) ⁻¹' cubeTube r := by
  ext x
  simp only [mem_preimage, mem_cubeTube_iff hr, add_sub_cancel_right]

lemma measurableSet_centeredTube (r : ℝ) : MeasurableSet (centeredTube r) := by
  apply measurableSet_lt
  · fun_prop
  · fun_prop

lemma volume_centeredTube {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2) :
    torusVolume (centeredTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [centeredTube_eq_cubeTube_preimage hr0,
    volume_translation (measurableSet_cubeTube r).nullMeasurableSet,
    volume_cubeTube hr0 hr1]

lemma perimeter_centeredTube_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2) :
    perimeter (centeredTube r) ≤ ENNReal.ofReal (2 * Real.pi * r) := by
  rw [centeredTube_eq_cubeTube_preimage hr0.le,
    perimeter_translation (measurableSet_cubeTube r).nullMeasurableSet]
  exact perimeter_cubeTube_le hr0 hr1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma cube_cuberoot (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ) ≠ 0)

lemma cube_two_thirds (x : ℝ) (hx : 0 ≤ x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma canonicalBall_radius_properties {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    0 < (3*V/(4*Real.pi))^(1/3 : ℝ) ∧
    (3*V/(4*Real.pi))^(1/3 : ℝ) ≤ 1/2 ∧
    ((3*V/(4*Real.pi))^(1/3 : ℝ))^3 * (Real.pi*4/3) = V := by
  have hp := Real.pi_pos
  have hVpos := hV.1
  have hv : 0 < 3*V/(4*Real.pi) := by positivity
  have hc := cube_cuberoot _ hv.le
  refine ⟨Real.rpow_pos_of_pos hv _, ?_, ?_⟩
  · have hbound : 3*V/(4*Real.pi) ≤ (1/2 : ℝ)^3 := by
      apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).2
      nlinarith [Real.pi_gt_three, hV.2]
    have hp3 : Odd (3 : ℕ) := by decide
    apply hp3.strictMono_pow.le_iff_le.1
    rw [hc]
    exact hbound
  · rw [hc]
    field_simp

lemma ballArea_formula {V : ℝ} (hV : 0 ≤ V) :
    4*Real.pi*((3*V/(4*Real.pi))^(1/3 : ℝ))^2 =
      (36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ) := by
  apply (show Odd (3 : ℕ) by decide).pow_injective
  have hc := cube_cuberoot (3*V/(4*Real.pi)) (by positivity)
  have hpc := cube_cuberoot (36*Real.pi) (by positivity)
  have hvc := cube_two_thirds V hV
  dsimp only
  calc
    (4*Real.pi*((3*V/(4*Real.pi))^(1/3 : ℝ))^2)^3 =
        (4*Real.pi)^3 * (((3*V/(4*Real.pi))^(1/3 : ℝ))^3)^2 := by ring
    _ = 36*Real.pi*V^2 := by rw [hc]; field_simp; ring
    _ = _ := by rw [mul_pow, hpc, hvc]

lemma volume_canonicalBall {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    torusVolume (canonicalBall V) = ENNReal.ofReal V := by
  obtain ⟨hr0, hr1, heq⟩ := canonicalBall_radius_properties hV
  change torusVolume (Metric.ball (0 : Torus) _) = _
  rw [volume_centeredBall hr0.le hr1, heq]

lemma perimeter_canonicalBall_le {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalBall V) ≤
      ENNReal.ofReal ((36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ)) := by
  obtain ⟨hr0, hr1, _⟩ := canonicalBall_radius_properties hV
  exact (perimeter_centeredBall_le hr0 hr1).trans_eq
    (congrArg ENNReal.ofReal (ballArea_formula hV.1.le))

lemma finitePerimeter_canonicalBall {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    FinitePerimeter (canonicalBall V) :=
  ⟨Metric.isOpen_ball.measurableSet.nullMeasurableSet,
    (perimeter_canonicalBall_le hV).trans_lt ENNReal.ofReal_lt_top⟩

lemma canonicalTube_radius_properties {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    0 < Real.sqrt (V/Real.pi) ∧ Real.sqrt (V/Real.pi) ≤ 1/2 ∧
    Real.pi * (Real.sqrt (V/Real.pi))^2 = V := by
  have hp := Real.pi_pos
  have hVpos := hV.1
  refine ⟨Real.sqrt_pos.2 (div_pos hV.1 hp), ?_, ?_⟩
  · apply Real.sqrt_le_iff.2
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hp).2
    nlinarith [Real.pi_gt_three, hV.2]
  · rw [Real.sq_sqrt (by positivity)]
    field_simp

lemma tubeArea_formula {V : ℝ} (hV : 0 ≤ V) :
    2*Real.pi*Real.sqrt (V/Real.pi) = 2*Real.sqrt (Real.pi*V) := by
  have hp := Real.pi_pos
  have heq : Real.pi*Real.sqrt (V/Real.pi) = Real.sqrt (Real.pi*V) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
  calc
    _ = 2*(Real.pi*Real.sqrt (V/Real.pi)) := by ring
    _ = _ := by rw [heq]

lemma volume_canonicalTube {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    torusVolume (canonicalTube V) = ENNReal.ofReal V := by
  obtain ⟨hr0, hr1, heq⟩ := canonicalTube_radius_properties hV
  change torusVolume (centeredTube _) = _
  rw [volume_centeredTube hr0.le hr1, heq]

lemma perimeter_canonicalTube_le {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalTube V) ≤ ENNReal.ofReal (2*Real.sqrt (Real.pi*V)) := by
  obtain ⟨hr0, hr1, _⟩ := canonicalTube_radius_properties hV
  exact (perimeter_centeredTube_le hr0 hr1).trans_eq
    (congrArg ENNReal.ofReal (tubeArea_formula hV.1.le))

lemma finitePerimeter_canonicalTube {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    FinitePerimeter (canonicalTube V) :=
  ⟨(measurableSet_centeredTube _).nullMeasurableSet,
    (perimeter_canonicalTube_le hV).trans_lt ENNReal.ofReal_lt_top⟩

theorem isMinimizerAt_perimeter_le_envelope {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ))
    {E : Set Torus} (hE : IsMinimizerAt V E) :
    perimeter E ≤ ENNReal.ofReal
      (min ((36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ))
        (min (2*Real.sqrt (Real.pi*V)) 2)) := by
  rw [ENNReal.ofReal_min, ENNReal.ofReal_min]
  refine le_min ?_ (le_min ?_ ?_)
  · exact (hE.2.2 _ (finitePerimeter_canonicalBall hV) (volume_canonicalBall hV)).trans
      (perimeter_canonicalBall_le hV)
  · exact (hE.2.2 _ (finitePerimeter_canonicalTube hV) (volume_canonicalTube hV)).trans
      (perimeter_canonicalTube_le hV)
  · have hVI : V ∈ Icc (0 : ℝ) 1 := ⟨hV.1.le, by linarith [hV.2]⟩
    simpa only [ENNReal.ofReal_ofNat] using
      (hE.2.2 _ (finitePerimeter_stripe hVI) (volume_stripe hVI)).trans (perimeter_stripe_le hVI)

theorem isMinimizerAt_perimeter_le_candidateProfile {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : IsMinimizerAt V E) :
    perimeter E ≤ ENNReal.ofReal (candidateProfile V) := by
  by_cases hhalf : V ≤ 1/2
  · simpa only [candidateProfile, min_eq_left (by linarith : V ≤ 1-V)] using
      isMinimizerAt_perimeter_le_envelope ⟨hV.1, hhalf⟩ hE
  · have hvol : 1-V ∈ Ioc (0 : ℝ) (1/2) := ⟨by linarith [hV.2], by linarith⟩
    have hcompl := (isMinimizerAt_compl ⟨hV.1.le, hV.2.le⟩).2 hE
    have hh := isMinimizerAt_perimeter_le_envelope hvol hcompl
    simpa only [perimeter_compl hE.1.1, candidateProfile,
      min_eq_right (by linarith : 1-V ≤ V)] using hh

end CubicTorus.UpperComparison

namespace CubicTorus

theorem isMinimizerAt_perimeter_le_candidateProfile {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : IsMinimizerAt V E) :
    perimeter E ≤ ENNReal.ofReal (candidateProfile V) :=
  UpperComparison.isMinimizerAt_perimeter_le_candidateProfile hV hE

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

lemma chainCorrection_zero (l : List Variation) (b : Variation)
    {E : Set Torus} (hE : MeasurableSet E) : chainCorrection l b E 0=0 := by
  simp [chainCorrection,simultaneousMass_zero l hE]

lemma chainCorrection_eventually_exact (l : List Variation) (b : Variation)
    {E : Set Torus} (hE : MeasurableSet E) (hB : directionalFlux E b.coordinate b.function≠0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (simultaneousChain l t++[(b,chainCorrection l b E t)]) ∧
      torusVolume (chainRegion (simultaneousChain l t++[(b,chainCorrection l b E t)]) E)=torusVolume E := by
  have hden : chainTransportedFlux (simultaneousChain l 0) b E≠0 := by simpa
  have hc : ContinuousAt (chainCorrection l b E) 0 :=
    (continuousAt_const.sub (simultaneousMass_smooth l E).continuous.continuousAt).div
      (simultaneousFlux_smooth l b E).continuous.continuousAt hden
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),|chainCorrection l b E t| *(b.bound : ℝ)<1 :=
    (hc.abs.mul_const _).eventually (eventually_lt_nhds (by simp [chainCorrection_zero l b hE]))
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ),chainTransportedFlux (simultaneousChain l t) b E≠0 :=
    (simultaneousFlux_smooth l b E).continuous.continuousAt.eventually_ne hden
  filter_upwards [simultaneousChain_eventually_valid l,hsmall,hne] with t ht hbt hnt
  have hv : ChainValid (simultaneousChain l t++[(b,chainCorrection l b E t)]) :=
    ht.append (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact hbt)
  refine ⟨hv,?_⟩
  apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _) |>.mp
  rw [show (torusVolume (chainRegion _ E)).toReal=torusVolume.real (chainRegion _ E) from rfl,
    volume_chainRegion hv hE,chainMass_append]
  unfold chainCorrection
  rw [div_mul_cancel₀ _ hnt]
  dsimp only [Measure.real]
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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma second_derivative_nonneg_of_local_min {f : ℝ → ℝ} {t : ℝ}
    (hmin : IsLocalMin f t) (hc : ContinuousAt f t) : 0≤deriv (deriv f) t := by
  by_contra hn
  have hn' : deriv (deriv f) t<0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn' hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 t] (fun _ ↦ f t) := by
    filter_upwards [hmin,hmax] with s hs hs'
    exact le_antisymm hs' hs
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  linarith

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

theorem isMinimizerAt_chain_stability {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (l : List Variation) (b : Variation)
    (hB : directionalFlux E b.coordinate b.function≠0) :
    ∃ γ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) γ ∧ γ 0=0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
        torusVolume (chainRegion (correctedChain l b γ t) E)=torusVolume E) ∧
      IsLocalMin (correctedChainArea l b γ μ) 0 ∧
      0≤deriv (deriv (correctedChainArea l b γ μ)) 0 := by
  obtain ⟨γ,hγ,heq⟩ := smooth_quotient_extension
    (contDiff_const.sub (simultaneousMass_smooth l E)) (simultaneousFlux_smooth l b E)
    (by simpa using hB)
  have heq' : γ =ᶠ[𝓝 0] chainCorrection l b E := heq
  have hγ0 : γ 0=0 := heq'.eq_of_nhds.trans (chainCorrection_zero l b hE)
  have hvol : ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
      torusVolume (chainRegion (correctedChain l b γ t) E)=torusVolume E := by
    filter_upwards [heq',chainCorrection_eventually_exact l b hE hB] with t ht hv
    simpa only [correctedChain,ht] using hv
  have hlocal : IsLocalMin (correctedChainArea l b γ μ) 0 := by
    filter_upwards [hvol] with t ht
    rw [correctedChainArea_zero l b hγ0,hμ.1]
    have hfin := chainRegion_finite ht.1 hE hmin.1.2
    have hleast := hmin.2.2 _ hfin (ht.2.trans hmin.2.1)
    have harea := perimeter_chainRegion_le_normalArea ht.1 hE hμ
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hleast.trans harea)
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _),correctedChainArea] using hh
  exact ⟨γ,hγ,hγ0,hvol,hlocal,second_derivative_nonneg_of_local_min hlocal
    (correctedChainArea_smoothAt l b hγ hγ0 μ).continuousAt⟩

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

end CubicTorus

end
end

section

noncomputable section
open Filter
open scoped Topology
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma deriv_smooth_add {f g : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : deriv (fun t ↦ f t+g t)=fun t ↦ deriv f t+deriv g t := by
  funext t
  exact ((hf.differentiable (by simp) t).hasDerivAt.add
    (hg.differentiable (by simp) t).hasDerivAt).deriv

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
namespace Periodic

lemma simultaneousMass_single (a : Variation) {E : Set Torus} (hE : MeasurableSet E) (t : ℝ) :
    chainMass (simultaneousChain [a] t) E=torusVolume.real E+t*directionalFlux E a.coordinate a.function := by
  have h := chainMass_append [] a t E
  simpa only [simultaneousChain,List.map_cons,List.map_nil,List.nil_append,chainMass,chainJacobian,chainTransportedFlux,chainMove,mul_one,one_mul,directionalFlux,
    setIntegral_one_eq_measureReal,← realVolume_lift hE] using h

lemma correctedSingleCofactor_deriv (a b : Variation) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0) (x n : Cover) :
    deriv (fun t ↦ chainCofactor (correctedChain [a] b γ t) x n) 0=
      coordinateNormalVelocity a.coordinate a.function x n+
        deriv γ 0 • coordinateNormalVelocity b.coordinate b.function x n := by
  let P : ℝ → Cover := fun t ↦ coordinateNormalVelocity b.coordinate b.function
    (coordinateMove a.coordinate a.function t x) (coordinateCofactor a.coordinate a.function t x n)
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateMove a.coordinate a.function t x) :=
    contDiff_const.add ((contDiff_id.mul contDiff_const).smul contDiff_const)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateCofactor a.coordinate a.function t x n) := by
    simp only [coordinateCofactor_eq]
    exact contDiff_const.add (contDiff_id.fun_smul contDiff_const)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (wallVelocity_contDiff b).comp (hm.prodMk hc)
  have he : (fun t ↦ chainCofactor (correctedChain [a] b γ t) x n)=
      (fun t ↦ n+t • coordinateNormalVelocity a.coordinate a.function x n+γ t • P t) := by
    funext t
    simp only [correctedChain,simultaneousChain,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      chainCofactor,coordinateCofactor_eq,P]
  rw [he]
  have hd := ((hasDerivAt_const (0 : ℝ) n).fun_add
    ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateNormalVelocity a.coordinate a.function x n))).fun_add
      ((hγ.differentiable (by simp) 0).hasDerivAt.fun_smul (hP.differentiable (by simp) 0).hasDerivAt)
  simpa [hγ0,P,coordinateMove,coordinateCofactor_eq] using hd.deriv

lemma correctedSingleArea_deriv (a b : Variation) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0) (μ : FiniteMeasure NormalBundle) :
    deriv (correctedChainArea [a] b γ μ) 0=normalFirstVariation μ a+
      deriv γ 0*normalFirstVariation μ b := by
  have h := normalArea_first_derivative (correctedChainCofactor_smooth [a] b hγ)
      (by intro p _; simp [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0]) μ
  change deriv (correctedChainArea [a] b γ μ) 0 = _ at h
  rw [h]
  simp only [normalEmbedding,correctedSingleCofactor_deriv a b hγ hγ0,inner_add_right,real_inner_smul_right]
  rw [integral_add,integral_const_mul]
  · rfl
  · exact (continuous_normalUnit.inner (𝕜 := ℝ)
      (continuous_coordinateNormalVelocity a.coordinate a.smooth)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((continuous_normalUnit.inner (𝕜 := ℝ)
      (continuous_coordinateNormalVelocity b.coordinate b.smooth)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _

theorem isMinimizerAt_mixed_stationary {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a b : Variation) (hB : directionalFlux E b.coordinate b.function≠0) :
    normalFirstVariation μ a*directionalFlux E b.coordinate b.function=
      normalFirstVariation μ b*directionalFlux E a.coordinate a.function := by
  obtain ⟨γ,hγ,hγ0,hvol,hlocal,_⟩ := isMinimizerAt_chain_stability hmin hE hμ [a] b hB
  have hex : (fun t ↦ chainMass (simultaneousChain [a] t) E+
      γ t*chainTransportedFlux (simultaneousChain [a] t) b E) =ᶠ[𝓝 0]
      (fun _ ↦ torusVolume.real E) := by
    filter_upwards [hvol] with t ht
    rw [← chainMass_append]
    change chainMass (correctedChain [a] b γ t) E=torusVolume.real E
    rw [← volume_chainRegion ht.1 hE]
    exact congrArg ENNReal.toReal ht.2
  have hd := hex.deriv_eq
  have hm : (fun t ↦ chainMass (simultaneousChain [a] t) E)=
      (fun t ↦ torusVolume.real E+t*directionalFlux E a.coordinate a.function) :=
    funext (simultaneousMass_single a hE)
  have hm' : deriv (fun t ↦ chainMass (simultaneousChain [a] t) E) 0=
      directionalFlux E a.coordinate a.function := by rw [hm]; simp
  rw [deriv_smooth_add (simultaneousMass_smooth [a] E)
    (hγ.mul (simultaneousFlux_smooth [a] b E))] at hd
  dsimp only at hd
  rw [hm',(show deriv (fun t ↦ γ t*chainTransportedFlux (simultaneousChain [a] t) b E) 0=
      deriv γ 0*directionalFlux E b.coordinate b.function from by
        simpa [hγ0] using ((hγ.differentiable (by simp) 0).hasDerivAt.fun_mul
          ((simultaneousFlux_smooth [a] b E).differentiable (by simp) 0).hasDerivAt).deriv),deriv_const] at hd
  have ha := hlocal.deriv_eq_zero
  rw [correctedSingleArea_deriv a b hγ hγ0 μ] at ha
  nlinarith [congrArg (fun z ↦ z*directionalFlux E b.coordinate b.function) ha,
    congrArg (fun z ↦ z*normalFirstVariation μ b) hd]

 theorem isMinimizerAt_exists_coordinate_multiplier {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (b : Variation) (hB : directionalFlux E b.coordinate b.function≠0) :
    ∃ H : ℝ,∀ a : Variation,normalFirstVariation μ a=H*directionalFlux E a.coordinate a.function := by
  refine ⟨normalFirstVariation μ b/directionalFlux E b.coordinate b.function,fun a ↦ ?_⟩
  apply mul_right_cancel₀ hB
  rw [isMinimizerAt_mixed_stationary hmin hE hμ a b hB]
  field_simp

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

theorem tangent_firstVariation_of_coordinate {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Variation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  rw [integral_tangentialDivergence_eq_sum hF, flux_sum_components E hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hpc : ∀ m x, (fun y ↦ F y i) (x + latticeVector m) = F x i := by
    intro m x; change (F (x + latticeVector m)) i = (F x) i; rw [hp]
  obtain ⟨D, hi, hf⟩ := exists_variation_of_function i hc hpc
  simpa only [normalFirstVariation, hi, hf] using hH D

theorem weakCMC_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Variation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle) := by
  rw [tangent_firstVariation_of_coordinate hH hF hp]
  obtain ⟨C, hC, hbound⟩ := periodic_bounded hF.continuous hp
  exact congrArg (fun r : ℝ ↦ H*r) (normalMeasure_flux hμ hF hp
    (by linarith : 0<C+1) (fun x ↦ (hbound x).trans (by linarith : C≤C+1))).symm

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

lemma candidateProfile_nonnegative {V : ℝ} (hV : V∈Icc 0 1) : 0 ≤ candidateProfile V := by
  have hv : 0 ≤ min V (1-V) := le_min hV.1 (sub_nonneg.mpr hV.2)
  unfold candidateProfile
  dsimp only
  positivity

lemma candidateProfile_at_zero : candidateProfile 0=0 := by
  norm_num [candidateProfile]

lemma candidateProfile_at_one : candidateProfile 1=0 := by
  norm_num [candidateProfile]

theorem isoperimetricProfile_le_candidate {V : ℝ} (hV : V∈Icc 0 1) :
    isoperimetricProfile V ≤ candidateProfile V/2 := by
  rcases eq_or_lt_of_le hV.1 with h0|h0
  · rw [← h0,isoperimetricProfile_zero,candidateProfile_at_zero]; norm_num
  rcases eq_or_lt_of_le hV.2 with h1|h1
  · rw [h1,isoperimetricProfile_one,candidateProfile_at_one]; norm_num
  obtain ⟨E,hE⟩ := exists_isMinimizerAt ⟨h0,h1⟩
  rw [isoperimetricProfile_eq_of_isMinimizerAt hE]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (isMinimizerAt_perimeter_le_candidateProfile ⟨h0,h1⟩ hE)
  rwa [ENNReal.toReal_ofReal (candidateProfile_nonnegative hV)] at hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ChamberPositionProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_coordinate_multiplier {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ H : ℝ,∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function := by
  obtain ⟨i,f,hf,hp,hflux⟩ := exists_positive_directionalFlux
    (perimeter_pos_of_volume hV hm.1.1 hm.2.1)
  obtain ⟨D,hi,hfD⟩ := Periodic.exists_variation_of_function i hf hp
  have hD : directionalFlux E D.coordinate D.function≠0 := by
    rw [hi,hfD]; exact hflux.ne'
  exact Periodic.isMinimizerAt_exists_coordinate_multiplier hm hE hμ D hD

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_MinimizerFirstTransitionTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma firstTransition_mem_Ioo_half : 4*Real.pi/81∈Ioo (0 : ℝ) (1/2) := by
  constructor
  · positivity
  · linarith [Real.pi_lt_four]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingBaseline
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

lemma isMinimizerAt_perimeter_half_le_one {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) : (perimeter E).toReal/2 ≤ 1 := by
  have hupper : perimeter E ≤ 2 :=
    (hmin.2.2 (stripe V) (finitePerimeter_stripe ⟨hV.1.le,hV.2.le⟩)
      (volume_stripe ⟨hV.1.le,hV.2.le⟩)).trans (perimeter_stripe_le ⟨hV.1.le,hV.2.le⟩)
  have hup : (perimeter E).toReal ≤ 2 := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞)≠⊤) hupper
  linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Rigidity_TwoVolumeNodal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CubicTorus.TwoVolume
noncomputable section
open Set Filter
open scoped Topology
open Reduction

lemma transitions : 0 < V₁ ∧ V₁ < V₂ ∧ V₂ < 1 / 2 := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hp4 : Real.pi < 4 := Real.pi_lt_four
  dsimp [V₁, V₂]
  constructor
  · positivity
  constructor
  · apply (lt_div_iff₀ hp).2
    nlinarith [sq_nonneg (4 - Real.pi)]
  · apply (div_lt_iff₀ hp).2
    linarith

lemma sphereArea_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ sphereArea v := by
  unfold sphereArea
  positivity

lemma sphereArea_cube {v : ℝ} (hv : 0 ≤ v) :
    sphereArea v ^ 3 = (9 * Real.pi / 2) * v ^ 2 := by
  have ha : ((9 * Real.pi / 2) ^ (1 / 3 : ℝ)) ^ 3 = 9 * Real.pi / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hb : (v ^ (2 / 3 : ℝ)) ^ 3 = v ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv]
    norm_num
  simp only [sphereArea, mul_pow, ha, hb]

lemma tubeArea_sq {v : ℝ} (hv : 0 ≤ v) : tubeArea v ^ 2 = Real.pi * v := by
  exact Real.sq_sqrt (mul_nonneg Real.pi_pos.le hv)

lemma sphereArea_le_tubeArea_iff {v : ℝ} (hv : 0 < v) :
    sphereArea v ≤ tubeArea v ↔ v ≤ V₁ := by
  have hs := sphereArea_cube hv.le
  have ht := tubeArea_sq hv.le
  have h0 : 0 < Real.pi ^ 2 * v ^ 3 := by positivity
  have h₆ : sphereArea v ^ 6 - tubeArea v ^ 6 =
      (81 / 4 * v - Real.pi) * (Real.pi ^ 2 * v ^ 3) := by
    calc
      _ = (sphereArea v ^ 3) ^ 2 - (tubeArea v ^ 2) ^ 3 := by ring
      _ = _ := by rw [hs, ht]; ring
  have ht0 : 0 ≤ tubeArea v := Real.sqrt_nonneg _
  rw [← pow_le_pow_iff_left₀ (sphereArea_nonneg hv.le) ht0 (by decide : 6 ≠ 0)]
  rw [← sub_nonpos, h₆]
  dsimp [V₁]
  constructor
  · intro h
    by_contra! hn
    have hpos : 0 < 81 / 4 * v - Real.pi := by linarith
    exact (not_lt_of_ge h) (mul_pos hpos h0)
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) h0.le

lemma tubeArea_le_one_iff {v : ℝ} (_ : 0 ≤ v) : tubeArea v ≤ 1 ↔ v ≤ V₂ := by
  rw [tubeArea, Real.sqrt_le_iff]
  norm_num
  simpa [V₂, mul_comm] using (le_div_iff₀ Real.pi_pos : v ≤ 1 / Real.pi ↔ v * Real.pi ≤ 1).symm

lemma tubeArea_nonneg (v : ℝ) : 0 ≤ tubeArea v := Real.sqrt_nonneg _

lemma sphereArea_eq_tubeArea_V₁ : sphereArea V₁ = tubeArea V₁ := by
  have hs := sphereArea_cube transitions.1.le
  have ht := tubeArea_sq transitions.1.le
  have hp : sphereArea V₁ ^ 6 = tubeArea V₁ ^ 6 := by
    calc
      _ = (sphereArea V₁ ^ 3) ^ 2 := by ring
      _ = (tubeArea V₁ ^ 2) ^ 3 := by rw [hs, ht]; dsimp [V₁]; ring
      _ = _ := by ring
  exact (pow_left_inj₀ (sphereArea_nonneg transitions.1.le) (tubeArea_nonneg _)
    (by decide : (6 : ℕ) ≠ 0)).mp hp

lemma envelope_tube {v : ℝ} (hv : v ∈ Icc V₁ V₂) : envelope v = tubeArea v := by
  have hv0 : 0 < v := transitions.1.trans_le hv.1
  have hvhalf : v ≤ 1 / 2 := hv.2.trans transitions.2.2.le
  have hmin : min v (1-v) = v := min_eq_left (by linarith)
  have hts : tubeArea v ≤ sphereArea v := by
    by_cases heq : v = V₁
    · subst v; exact sphereArea_eq_tubeArea_V₁.ge
    · exact le_of_lt (not_le.1 (fun h => heq (le_antisymm
        ((sphereArea_le_tubeArea_iff hv0).1 h) hv.1)))
  have ht1 := (tubeArea_le_one_iff hv0.le).2 hv.2
  simp only [envelope, hmin, min_eq_left ht1, min_eq_right hts]

lemma candidateProfile_eq_two_envelope (v : ℝ) : candidateProfile v = 2 * envelope v := by
  have hc : (36 * Real.pi) ^ (1/3 : ℝ) = 2 * (9 * Real.pi / 2) ^ (1/3 : ℝ) := by
    have hcube (a : ℝ) (ha : 0 ≤ a) : (a ^ (1/3 : ℝ)) ^ 3 = a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
      norm_num
    apply (pow_left_inj₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
    rw [hcube _ (by positivity), mul_pow, hcube _ (by positivity)]
    ring
  simp only [candidateProfile, envelope, sphereArea, tubeArea, hc,
    mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  ring_nf

end
end CubicTorus.TwoVolume

end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma candidateProfile_tube {V : ℝ} (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂) :
    candidateProfile V=2*Real.sqrt (Real.pi*V) := by
  rw [TwoVolume.candidateProfile_eq_two_envelope,TwoVolume.envelope_tube hV]
  rfl

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FourStarScalarGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma secondTransition_mem_Ioo_half : 1/Real.pi∈Ioo (0 : ℝ) (1/2) := by
  exact ⟨by positivity,(div_lt_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cylinder_contact_support_deriv {V : ℝ} (hV : 0<V)
    (hc : IsLocalMin cylinderRatio V) {C : ℝ → ℝ}
    (hs : Reduction.UpperSupport isoperimetricProfile C V) :
    deriv C V=isoperimetricProfile V/(2*V) := by
  have hloc : IsLocalMin (fun W => C W/Real.sqrt W) V := by
    filter_upwards [hc,hs.above,Ioi_mem_nhds hV] with W hW hab hpos
    change C V/Real.sqrt V≤C W/Real.sqrt W
    rw [hs.contact]
    exact hW.trans (div_le_div_of_nonneg_right hab (Real.sqrt_nonneg _))
  have hd := (hs.smooth.differentiableAt (by norm_num)).hasDerivAt.div
    (Real.hasDerivAt_sqrt hV.ne') (Real.sqrt_ne_zero'.mpr hV)
  have hz := hloc.hasDerivAt_eq_zero hd
  rw [hs.contact] at hz
  have hq : (Real.sqrt V)^2=V := Real.sq_sqrt hV.le
  have hn : Real.sqrt V≠0 := Real.sqrt_ne_zero'.mpr hV
  field_simp [hn] at hz
  apply (eq_div_iff (by positivity : 2*V≠0)).mpr
  rw [hq] at hz
  nlinarith only [hz]

theorem isMinimizerAt_cylinder_contact_multiplier {V : ℝ} (hV : V∈Ioo 0 1)
    (hc : IsLocalMin cylinderRatio V) {E : Set Torus}
    (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) :
    (H/2)*V=((perimeter E).toReal/2)/2 := by
  obtain ⟨N,C,hN,hp,ha,hs,hd,_⟩ := Periodic.profile_hessian_of_CMC hV hE hm hμ
    (fun _ hF hpF => Periodic.weakCMC_identity hμ hH hF hpF)
  have hh := cylinder_contact_support_deriv hV.1 hc hs
  rw [hd,isoperimetricProfile_eq_of_isMinimizerAt hm] at hh
  have he := (eq_div_iff (ne_of_gt (mul_pos (by norm_num : (0 : ℝ)<2) hV.1))).mp hh
  nlinarith only [he]

theorem isMinimizerAt_cylinder_contact_bounds {V : ℝ} (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂)
    (hc : IsLocalMin cylinderRatio V) {E : Set Torus}
    (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) :
    let A := (perimeter E).toReal/2
    let h := H/2
    0<A ∧ A≤1 ∧ h*V=A/2 ∧ Real.pi/2≤h ∧ h*A≤Real.pi/2 := by
  have hv1 := firstTransition_mem_Ioo_half
  have hv2 := secondTransition_mem_Ioo_half
  have hv : V∈Ioo (0 : ℝ) 1 := ⟨hv1.1.trans_le hV.1,lt_of_le_of_lt hV.2 (by change 1/Real.pi<1; linarith [hv2.2])⟩
  let A := (perimeter E).toReal/2
  let h := H/2
  have hpos : 0<A := by dsimp only [A]; rw [←isoperimetricProfile_eq_of_isMinimizerAt hm]; exact isoperimetricProfile_pos hv
  have hA1 : A≤1 := isMinimizerAt_perimeter_half_le_one hv hm
  have he : h*V=A/2 := isMinimizerAt_cylinder_contact_multiplier hv hc hE hm hμ hH
  have hlow := profile_ge_second_chord (show V∈Icc (0 : ℝ) (1/Real.pi) from ⟨hv.1.le,hV.2⟩)
  rw [isoperimetricProfile_eq_of_isMinimizerAt hm] at hlow
  change Real.pi*V≤A at hlow
  have hh : Real.pi/2≤h := by
    apply (mul_le_mul_iff_left₀ hv.1).mp
    change Real.pi/2*V≤h*V
    rw [he]
    linarith only [hlow]
  have hupper := isoperimetricProfile_le_candidate ⟨hv.1.le,hv.2.le⟩
  rw [candidateProfile_tube hV,isoperimetricProfile_eq_of_isMinimizerAt hm] at hupper
  change A≤2*Real.sqrt (Real.pi*V)/2 at hupper
  have hsq := Real.sq_sqrt (show 0≤Real.pi*V from mul_nonneg Real.pi_pos.le hv.1.le)
  have hA2 : A^2≤Real.pi*V := by nlinarith [Real.sqrt_nonneg (Real.pi*V)]
  have hcap : h*A≤Real.pi/2 := by
    apply (mul_le_mul_iff_left₀ hv.1).mp
    nlinarith only [hA2,congrArg (fun x : ℝ => x*A) he]
  exact ⟨hpos,hA1,he,hh,hcap⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_cylinder_contact_corner_excluded_oai
    {V : ℝ} (hVrange : V∈Icc TwoVolume.V₁ TwoVolume.V₂)
    (hcontact : IsLocalMin cylinderRatio V)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    (hw0 : 2/3 ≤ axialFluxWeight μ 0) (hw1 : axialFluxWeight μ 0<1)
    (ht1 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (ht2 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E)
    (hb1 : quotientMap (chamberVertex c (fun j => decide (j=1)))∈openRepresentative E)
    (hb2 : quotientMap (chamberVertex c (fun j => decide (j=2)))∈openRepresentative E) : False := by
  have hv1 := firstTransition_mem_Ioo_half
  have hv2 := secondTransition_mem_Ioo_half
  have hvh : V∈Ioo (0 : ℝ) (1/2) := ⟨hv1.1.trans_le hVrange.1,hVrange.2.trans_lt hv2.2⟩
  have hV : V∈Ioo (0 : ℝ) 1 := ⟨hvh.1,by linarith [hvh.2]⟩
  obtain ⟨H,hH⟩ := isMinimizerAt_coordinate_multiplier hV hE hm hμ
  obtain ⟨hA,hAc,hA1,hh,hr,hrV,_,hs1,hb,_,htop,hbottom,hdrop⟩ :=
    isMinimizerAt_four_corner_necessary_data hvh hE hm hμ hN hp ha hs hsg hH ht1 ht2 hb1 hb2
  have hpos : 0<Real.sqrt (Real.pi*V) := Real.sqrt_pos.mpr (mul_pos Real.pi_pos hvh.1)
  have hle : Real.sqrt (Real.pi*V) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    simpa only [mul_comm] using (le_div_iff₀ Real.pi_pos).mp hVrange.2
  have hv : V=(Real.sqrt (Real.pi*V))^2/Real.pi := by
    rw [Real.sq_sqrt (mul_nonneg Real.pi_pos.le hvh.1.le)]
    field_simp
  have hcap := (isMinimizerAt_cylinder_contact_bounds hVrange hcontact hE hm hμ hH).2.2.2.2
  rw [← hμ.1] at hcap
  exact fourCorner_normalized_contradiction hA hpos hle hAc hv hh hb hw1 hr hrV hs1 htop hbottom hdrop hw0
    (hcap.trans (by linarith [Real.pi_lt_d2]))

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_cylinder_contact_corner_excluded_oai := @OAI.CubicTorus.isMinimizerAt_cylinder_contact_corner_excluded_oai
