-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:21:34.4329+00:00
-- url     : https://prove2.me/submissions/c91c76d6-8a59-4929-97f8-9af1ca8b1dd6

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_connected_or_zero_curvature
import Theorems.Thm_OAI_CubicTorus_actual_centered_graph_phase_patch
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normal_linear_chart
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_oriented_CMC_charts
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_smooth_CMC
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_zero_curvature_local_normal

section
-- module Solutions.OAIQ079_CT.Compat
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

lemma perimeter_empty : perimeter ∅ = 0 := by
  simp [perimeter]

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

lemma product_to_torus_measurePreserving :
    MeasurePreserving (WithLp.toLp 2 : ProductTorus → Torus) volume torusVolume :=
  ⟨(PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable,
    torusVolume_eq_product.symm⟩

lemma torus_to_product_measurePreserving :
    MeasurePreserving (WithLp.ofLp : Torus → ProductTorus) torusVolume volume := by
  exact product_to_torus_measurePreserving.symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.toMeasurableEquiv

lemma torus_coordinate_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Torus => x i) torusVolume volume := by
  exact (measurePreserving_eval (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ)))) i).comp
    torus_to_product_measurePreserving

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

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

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
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
open scoped RealInnerProductSpace

lemma normalTest_le_one {F : Cover → Cover} (hF : AdmissibleField F) (z : NormalBundle) :
    normalTest F hF.1.continuous z ≤ 1 := by
  calc
    _ ≤ ‖(z.2 : Cover)‖ * ‖F z.1‖ := real_inner_le_norm _ _
    _ ≤ 1 := by simpa only [z.2.property, one_mul] using hF.2.2 z.1

theorem normalMeasure_weighted_saturation {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (w : C(NormalBundle, ℝ))
    {A : ℝ} (hA : ∀ (F : Cover → Cover) (hF : AdmissibleField F),
      (∫ z, w z * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ A) :
    (∫ z, w z ∂(μ : Measure NormalBundle)) ≤ A := by
  let C : ℝ := ‖w‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hwC (z : NormalBundle) : w z ≤ C := by
    exact (le_abs_self _).trans ((w.norm_coe_le_norm z).trans (by dsimp [C]; linarith))
  let P : ℝ := (perimeter E).toReal
  let I : ℝ := ∫ z, w z ∂(μ : Measure NormalBundle)
  let B : ℝ := P + (A - I) / C
  have hiw : Integrable w (μ : Measure NormalBundle) := w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (F : Cover → Cover) (hF : AdmissibleField F) :
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) ≤ B := by
    let T := normalTest F hF.1.continuous
    have hiT : Integrable T (μ : Measure NormalBundle) := T.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hiwT : Integrable (fun z ↦ w z * T z) (μ : Measure NormalBundle) :=
      (w.continuous.mul T.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hdef (z : NormalBundle) :
        w z - w z * T z ≤ C * (1 - T z) := by
      have hT : 0 ≤ 1 - T z := sub_nonneg.mpr (normalTest_le_one hF z)
      nlinarith [mul_le_mul_of_nonneg_right (hwC z) hT]
    have hh := integral_mono (hiw.sub hiwT)
      (((integrable_const (1 : ℝ)).sub hiT).const_mul C) hdef
    simp only [Pi.sub_apply] at hh
    rw [integral_sub hiw hiwT, integral_const_mul,
      integral_sub (integrable_const (1 : ℝ)) hiT] at hh
    have hmass : (∫ _ : NormalBundle, (1 : ℝ) ∂(μ : Measure NormalBundle)) = P := by
      simpa only [integral_const, smul_eq_mul, mul_one, P,
        FiniteMeasure.mass, FiniteMeasure.coeFn_def, Measure.real, ENNReal.toReal] using hμ.1
    rw [hmass] at hh
    have hcap : (∫ z, w z * T z ∂(μ : Measure NormalBundle)) ≤ A := hA F hF
    have hflux : (∫ z, T z ∂(μ : Measure NormalBundle)) =
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := hμ.2 F hF
    rw [← hflux]
    dsimp only [B]
    apply (mul_le_mul_iff_left₀ hC).mp
    rw [add_mul, div_mul_cancel₀ _ hC.ne']
    dsimp only [I] at *
    nlinarith
  have hB : 0 ≤ B := by
    simpa only [divergence_zero, integral_zero] using hbound (fun _ ↦ 0) admissible_zero
  have hP : perimeter E ≤ ENNReal.ofReal B := by
    unfold perimeter
    exact iSup_le fun F ↦ iSup_le fun hF ↦ ENNReal.ofReal_le_ofReal (hbound F hF)
  have hPB : P ≤ B := by
    simpa only [P, ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
  have hneg : (A - I) / C ≥ 0 := by dsimp only [B] at hPB; linarith
  have hh := mul_nonneg hneg hC.le
  rw [div_mul_cancel₀ _ hC.ne'] at hh
  exact sub_nonneg.mp hh

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalMeasure_weighted_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ z, w z.1 * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        divergence (fun y ↦ w y • F y) x := by
  obtain ⟨M, hM, hb⟩ := periodic_bounded hw.continuous hp
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ w x • F x) := hw.smul hF.1
  have hGp : ∀ n x, w (x + latticeVector n) • F (x + latticeVector n) = w x • F x := by
    intro n x
    rw [hp, hF.2.1]
  have hGb (x : Cover) : ‖w x • F x‖ ≤ M + 1 := by
    rw [norm_smul]
    calc
      _ ≤ ‖w x‖ * 1 := mul_le_mul_of_nonneg_left (hF.2.2 x) (norm_nonneg _)
      _ ≤ M + 1 := by simpa only [mul_one] using (hb x).trans (by linarith)
  simpa only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right] using
    normalMeasure_flux hμ hG hGp (by linarith : 0 < M + 1) hGb

theorem normalMeasure_weightedPerimeter {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hn : ∀ x, 0 ≤ w x) :
    weightedPerimeter E w = ENNReal.ofReal
      (∫ z, w z.1 ∂(μ : Measure NormalBundle)) := by
  let W : C(NormalBundle, ℝ) := ⟨fun z ↦ w z.1,
    hw.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  have hiW : Integrable W (μ : Measure NormalBundle) :=
    W.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle : weightedPerimeter E w ≤ ENNReal.ofReal (∫ z, W z ∂(μ : Measure NormalBundle)) := by
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    rw [← normalMeasure_weighted_flux hμ hw hp hF]
    apply integral_mono ((W.continuous.mul (normalTest F hF.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hiW
    intro z
    exact (mul_le_mul_of_nonneg_left (normalTest_le_one hF z) (hn z.1)).trans_eq (mul_one _)
  have htop : weightedPerimeter E w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  apply le_antisymm hle
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  apply normalMeasure_weighted_saturation hμ W
  intro F hF
  change (∫ z, w z.1 * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ _
  rw [normalMeasure_weighted_flux hμ hw hp hF]
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
  exact le_iSup_of_le F (le_iSup_of_le hF le_rfl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

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

lemma measurableSet_sublevelRegion {q : Cover → ℝ} (hq : Measurable q) (t : ℝ) :
    MeasurableSet (sublevelRegion q t) :=
  measurableSet_lt (hq.comp measurable_representative) measurable_const

lemma mem_sublevelRegion_quotient {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x) (t : ℝ) (x : Cover) :
    quotientMap x ∈ sublevelRegion q t ↔ q x < t := by
  simp only [sublevelRegion, mem_ofPred_eq, periodic_representative hp]

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

lemma integral_spatialNormalMeasure_periodic (μ : FiniteMeasure NormalBundle)
    {w : Cover → ℝ} (hw : Continuous w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) :
    (∫ x, w (representative x) ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z, w z.1 ∂(μ : Measure NormalBundle) := by
  rw [integral_spatialNormalMeasure μ (f := fun x ↦ w (representative x))
    (hw.measurable.comp measurable_representative)]
  congr 1
  ext z
  exact periodic_representative hp z.1

lemma spatialNormalMeasure_weightedPerimeter {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hn : ∀ x, 0 ≤ w x) :
    weightedPerimeter E w = ENNReal.ofReal
      (∫ x, w (representative x) ∂(spatialNormalMeasure μ : Measure Torus)) := by
  rw [integral_spatialNormalMeasure_periodic μ hw.continuous hp]
  exact normalMeasure_weightedPerimeter hμ hw hp hn

lemma sublevelCutoff_eq_zero {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : t ≤ q x) : sublevelCutoff q t ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

lemma sublevelCutoff_eq_one {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : q x ≤ t - ε) : sublevelCutoff q t ε x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hε).2 (by linarith)

lemma divergence_cutoff_zero {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    {t ε : ℝ} (hε : 0 < ε) {x : Cover} (hx : t ≤ q x) :
    divergence (fun y ↦ sublevelCutoff q t ε y • F y) x = 0 := by
  rw [divergence_smul_function ((sublevelCutoff_contDiff hq t ε).differentiable (by simp) x)
    (hF.differentiable (by simp) x), sublevelCutoff_eq_zero hε hx,
    sublevelCutoff_gradient_zero (hq.differentiable (by simp)) hε t x (Or.inr hx)]
  simp

lemma admissible_sublevelCutoff {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {F : Cover → Cover}
    (hF : AdmissibleField F) (t ε : ℝ) :
    AdmissibleField (fun x ↦ sublevelCutoff q t ε x • F x) := by
  have hh := admissible_convex_cutoff (sublevelCutoff_contDiff hq t ε)
    (sublevelCutoff_periodic hp t ε) (sublevelCutoff_mem_Icc q t ε) hF admissible_zero
  simpa only [smul_zero, add_zero] using hh

lemma weightedPerimeter_sublevelCutoff_le {E : Set Torus} (hE : MeasurableSet E)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {t ε : ℝ} (hε : 0 < ε) :
    weightedPerimeter E (sublevelCutoff q t ε) ≤ perimeter (E ∩ sublevelRegion q t) := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have he : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      divergence (fun y ↦ sublevelCutoff q t ε y • F y) x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ sublevelRegion q t),
      divergence (fun y ↦ sublevelCutoff q t ε y • F y) x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))
      (inter_subset_inter_right _ (preimage_mono inter_subset_left))
    intro x hx
    apply divergence_cutoff_zero hq hF.1 hε
    by_contra hn
    apply hx.2
    refine ⟨hx.1.1, hx.1.2, ?_⟩
    exact (mem_sublevelRegion_quotient hp t x).2 (lt_of_not_ge hn)
  rw [he]
  exact le_iSup₂_of_le (fun x ↦ sublevelCutoff q t ε x • F x)
    (admissible_sublevelCutoff hq hp hF t ε) le_rfl

lemma spatialNormalMeasure_sublevel_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {s t : ℝ} (hst : s < t)
    (hP : perimeter (E ∩ sublevelRegion q t) ≠ ⊤) :
    (spatialNormalMeasure μ : Measure Torus).real (sublevelRegion q s) ≤
      (perimeter (E ∩ sublevelRegion q t)).toReal := by
  let σ : Measure Torus := spatialNormalMeasure μ
  let w := sublevelCutoff q t (t - s)
  let B := sublevelRegion q s
  have hB : MeasurableSet B := measurableSet_sublevelRegion hq.continuous.measurable s
  have hwb (x : Cover) : w x ∈ Icc (0 : ℝ) 1 := sublevelCutoff_mem_Icc q t (t - s) x
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := sublevelCutoff_contDiff hq t (t - s)
  have hwp : ∀ n x, w (x + latticeVector n) = w x := sublevelCutoff_periodic hp t (t - s)
  have hi : Integrable (fun x ↦ w (representative x)) σ :=
    Integrable.of_bound (hw.continuous.measurable.comp measurable_representative).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hwb _).1]
        exact (hwb _).2)
  have hminor (x : Torus) : B.indicator (fun _ ↦ (1 : ℝ)) x ≤ w (representative x) := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact le_of_eq (sublevelCutoff_eq_one (sub_pos.mpr hst) (by
        have hh : q (representative x) < s := hx
        linarith)).symm
    · rw [indicator_of_notMem hx]
      exact (hwb _).1
  have hm : σ.real B ≤ ∫ x, w (representative x) ∂σ := by
    have hh := integral_mono ((integrable_const (1 : ℝ)).indicator hB) hi hminor
    simpa only [integral_indicator hB, integral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply_univ] using hh
  have hpbound := weightedPerimeter_sublevelCutoff_le hE hq hp (t := t) (sub_pos.mpr hst)
  rw [spatialNormalMeasure_weightedPerimeter hμ hw hwp (fun x ↦ (hwb x).1)] at hpbound
  have hnonneg : 0 ≤ ∫ x, w (representative x) ∂σ := integral_nonneg fun x ↦ (hwb _).1
  have hh := ENNReal.toReal_mono hP hpbound
  rw [ENNReal.toReal_ofReal hnonneg] at hh
  exact hm.trans hh

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

lemma perimeter_eq_zero_of_volume_eq_zero {E : Set Torus} (hE : torusVolume E = 0) :
    perimeter E = 0 := by
  rw [perimeter_congr_ae (ae_eq_empty.mpr hE), perimeter_empty]

lemma spatialNormalMeasure_support_subset_volumeSupport {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus).support ⊆ volumeSupport E := by
  intro a ha
  rw [mem_volumeSupport_iff]
  intro r hr
  by_contra! hv
  have hz : torusVolume (E ∩ Metric.ball a r) = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hv ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  let s := min r (1 / 4 : ℝ)
  have hs : 0 < s := lt_min hr (by norm_num)
  have hs4 : s ≤ 1 / 4 := min_le_right _ _
  have hsr : s ≤ r := min_le_left _ _
  have hcut : perimeter (E ∩ sublevelRegion (localRadialSquared a) (s ^ 2)) = 0 := by
    rw [sublevelRegion_localRadialSquared a hs.le hs4]
    apply perimeter_eq_zero_of_volume_eq_zero
    apply measure_mono_null (inter_subset_inter_right E (Metric.ball_subset_ball hsr)) hz
  have hbound := spatialNormalMeasure_sublevel_le hE hμ (localRadialSquared_contDiff a)
    (localRadialSquared_periodic a) (s := (s / 2) ^ 2) (t := s ^ 2)
    (by nlinarith [sq_pos_of_pos hs]) (by rw [hcut]; exact ENNReal.zero_ne_top)
  rw [hcut, ENNReal.toReal_zero,
    sublevelRegion_localRadialSquared a (by positivity : 0 ≤ s / 2) (by linarith)] at hbound
  have hzero : (spatialNormalMeasure μ : Measure Torus) (Metric.ball a (s / 2)) = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hbound ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  have hp := (Metric.nhds_basis_ball.mem_measureSupport.mp ha) (s / 2) (by positivity)
  exact hp.ne' hzero

lemma spatialNormalMeasure_support_subset_boundary {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus).support ⊆ volumeSupport E ∩ volumeSupport Eᶜ := by
  intro a ha
  refine ⟨spatialNormalMeasure_support_subset_volumeSupport hE hμ ha, ?_⟩
  have hh := spatialNormalMeasure_support_subset_volumeSupport hE.compl (isNormalMeasure_compl hE hμ)
  rw [spatialNormalMeasure_reverse] at hh
  exact hh ha

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

lemma image_quotientMap_eq_preimage_representative {S : Set Cover}
    (hS : S ⊆ fundamentalCube) : quotientMap '' S = representative ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change representative (quotientMap v) ∈ S
    rwa [representative_quotientMap_of_mem (hS hv)]
  · intro hx
    exact ⟨representative x, hx, quotientMap_representative x⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma hyperplane_volume_zero {n : Cover} (hn : ‖n‖ = 1) :
    volume {x : Cover | ⟪n, x⟫ = 0} = 0 := by
  apply Measure.addHaar_submodule volume (LinearMap.ker (innerSL ℝ n).toLinearMap)
  intro htop
  have hm : n ∈ LinearMap.ker (innerSL ℝ n).toLinearMap := by rw [htop]; trivial
  change ⟪n, n⟫ = 0 at hm
  rw [real_inner_self_eq_norm_sq, hn] at hm
  norm_num at hm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
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

lemma IsNormalMeasure.congr_ae {E F : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (hEF : E =ᵐ[torusVolume] F) : IsNormalMeasure F μ := by
  refine ⟨?_, ?_⟩
  · rw [← perimeter_congr_ae hEF]
    exact hμ.1
  · intro G hG
    rw [hμ.2 G hG]
    apply setIntegral_congr_set
    exact liftSet_congr_ae hEF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProductChart_measurePreserving (n : Cover) :
    MeasurePreserving (normalProductChart n) := by
  exact (((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm _).trans
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm).trans
    (normalRotation n).measurePreserving

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVLipschitzGraph
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

lemma normalMeasure_frontier_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∀ᵐ z ∂(μ : Measure NormalBundle), quotientMap z.1 ∈ frontier E := by
  have hh : ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus), c ∈ frontier E := by
    filter_upwards [Measure.support_mem_ae (μ := (spatialNormalMeasure μ : Measure Torus))] with c hc
    have hc' := spatialNormalMeasure_support_subset_boundary hE hμ hc
    rw [frontier_eq_closure_inter_closure]
    exact ⟨Measure.support_restrict_subset.trans inter_subset_left hc'.1,
      Measure.support_restrict_subset.trans inter_subset_left hc'.2⟩
  change ∀ᵐ c ∂Measure.map normalProjection (μ : Measure NormalBundle), c ∈ frontier E at hh
  exact (ae_map_iff normalProjection_continuous.measurable.aemeasurable
    (show MeasurableSet {c : Torus | c ∈ frontier E} from isClosed_frontier.measurableSet)).mp hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_inner {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ⟪n, normalGraph n g y⟫ = g y := by
  simp [normalGraph, inner_add_right, normalPlaneEmbedding_inner hn,
    inner_smul_right, hn]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma fderiv_fderiv_apply {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : X) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp) |>.differentiableAt) (differentiableAt_const v)]
  simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphEnergy
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_graph {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : normalPlaneCoordinates n (normalGraph n g y) = y := by
  simp [normalGraph, map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVColumnHeight
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma normalColumnChart_apply (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Plane) :
    normalColumnChart a n (t, y) = a + (normalPlaneEmbedding n y + t • n) := by
  change a + normalProductChart n (t, WithLp.ofLp y) = _
  rw [normalProductChart_decompose hn]
  congr 1
  exact add_comm _ _

lemma normalColumnChart_measurePreserving (a n : Cover) :
    MeasurePreserving (normalColumnChart a n) := by
  apply MeasurePreserving.trans _ (measurePreserving_add_left volume a)
  apply MeasurePreserving.trans _ (normalProductChart_measurePreserving n)
  change MeasurePreserving
    (Prod.map id (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) volume volume
  simpa only [Measure.volume_eq_prod] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

lemma normalColumnChart_projection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) :
    normalPlaneCoordinates n (normalColumnChart a n (t, y) - a) = y := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, map_add, map_smul,
    normalPlaneCoordinates_embedding, normalPlaneCoordinates_normal hn, smul_zero, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphShear_columnChart (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (t : ℝ) (y : Plane) :
    graphShear a n g (normalColumnChart a n (t,y)) = normalColumnChart a n (t+g y,y) := by
  change normalColumnChart a n (t,y) +
    g (normalPlaneCoordinates n (normalColumnChart a n (t,y)-a)) • n = _
  rw [normalColumnChart_projection a hn, normalColumnChart_apply a hn,
    normalColumnChart_apply a hn, add_smul]
  abel

lemma columnShear_measurePreserving {g : Plane → ℝ} (hg : Measurable g) :
    MeasurePreserving (fun p : ℝ × Plane ↦ (p.1+g p.2, p.2)) := by
  have hs : MeasurePreserving (fun p : Plane × ℝ ↦ (p.1, p.2+g p.1))
      ((volume : Measure Plane).prod volume) ((volume : Measure Plane).prod volume) :=
    (MeasurePreserving.id (volume : Measure Plane)).skew_product
      (measurable_snd.add (hg.comp measurable_fst))
      (Eventually.of_forall fun y ↦ (measurePreserving_add_right volume (g y)).map_eq)
  have hh := (Measure.measurePreserving_swap (μ := (volume : Measure Plane))
    (ν := (volume : Measure ℝ))).comp (hs.comp (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure Plane))))
  simpa only [Function.comp_def, Prod.swap, Measure.volume_eq_prod] using hh

lemma graphShear_measurePreserving (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Measurable g) : MeasurePreserving (graphShear a n g) := by
  have hi : MeasurePreserving (normalColumnChart a n).symm :=
    MeasurePreserving.symm (normalColumnChart a n) (normalColumnChart_measurePreserving a n)
  have hh := (normalColumnChart_measurePreserving a n).comp
    ((columnShear_measurePreserving hg).comp hi)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  obtain ⟨⟨t,y⟩,rfl⟩ := (normalColumnChart a n).surjective x
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply]
  exact graphShear_columnChart a hn g t y

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVFlatBlowupRegular
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

lemma preconnected_crosses_frontier {X : Type*} [TopologicalSpace X]
    {S U : Set X} (hS : IsPreconnected S) (hU : IsOpen U)
    (h₁ : (S ∩ U).Nonempty) (h₂ : (S ∩ Uᶜ).Nonempty) :
    (S ∩ frontier U).Nonempty := by
  classical
  by_contra h
  have hd : Disjoint (frontier U) S := by
    rw [Set.disjoint_left]
    intro x hx hxs
    exact h ⟨x,hxs,hx⟩
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hc := isClopen_preimage_val hU hd
  obtain ⟨x,hxS,hxU⟩ := h₁
  have he : (Subtype.val ⁻¹' U : Set S) = univ := hc.eq_univ ⟨⟨x,hxS⟩,hxU⟩
  obtain ⟨y,hyS,hyU⟩ := h₂
  have hy : (⟨y,hyS⟩ : S) ∈ Subtype.val ⁻¹' U := by rw [he]; trivial
  exact hyU hy

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_GraphMollifier
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

lemma graph_trace_volume_zero (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) :
    volume {x : Cover | ⟪n,x-a⟫ = graphHeightExtension a n g x} = 0 := by
  have hz : volume {x : Cover | ⟪n,x-a⟫ = 0} = 0 := by
    simpa only [Set.preimage_ofPred_eq,sub_eq_add_neg] using
      (measurePreserving_add_right volume (-a)).quasiMeasurePreserving.preimage_null
        (hyperplane_volume_zero hn)
  have hh := (graphShear_measurePreserving a hn hg.neg.measurable).quasiMeasurePreserving.preimage_null hz
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_preimage,graphShear,normalMove,graphHeightExtension,
    add_sub_right_comm,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hn,
    one_pow,mul_one,Pi.neg_apply]
  constructor <;> intro h <;> linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TorusC1Boundary
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

lemma volumeSupport_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    volumeSupport ((fun z ↦ z+b) ⁻¹' E) = (fun z ↦ z+b) ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : ((fun z ↦ z+b) ⁻¹' E) ∩ Metric.ball a r =
      (fun z ↦ z+b) ⁻¹' (E ∩ Metric.ball (a+b) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,dist_add_right]
  rw [he,Measure.real_def,Measure.real_def,
    volume_translation (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    openRepresentative ((fun z ↦ z+b) ⁻¹' E) =
      (fun z ↦ z+b) ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_translation hE.compl]
  rfl

lemma frontier_openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    frontier (openRepresentative ((fun z ↦ z+b) ⁻¹' E)) =
      (fun z ↦ z+b) ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_translation hE b]
  exact (Homeomorph.addRight b).preimage_frontier _ |>.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcWeight_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcWeight := by
  apply (contDiff_const.add (contDiff_id.norm_sq ℝ)).sqrt
  intro p
  positivity

lemma cmcFlux_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcFlux :=
  (cmcWeight_contDiff.inv (fun p ↦ (cmcWeight_pos p).ne')).smul contDiff_id

lemma cmcWeight_hasFDerivAt (p : Plane) :
    HasFDerivAt cmcWeight ((cmcWeight p)⁻¹ • innerSL ℝ p) p := by
  have h := ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_add 1).sqrt
    (by positivity : (1 : ℝ)+‖p‖^2≠0)
  change HasFDerivAt cmcWeight ((1/(2*cmcWeight p)) • (2 • innerSL ℝ p)) p at h
  have he : (1/(2*cmcWeight p)) • (2 • innerSL ℝ p) =
      (cmcWeight p)⁻¹ • innerSL ℝ p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,two_smul,add_apply]
    field_simp
    ring
  exact he ▸ h

lemma cmcFlux_hasFDerivAt (p : Plane) : HasFDerivAt cmcFlux (cmcJacobian p) p := by
  have h := ((hasDerivAt_inv (cmcWeight_pos p).ne').comp_hasFDerivAt p (cmcWeight_hasFDerivAt p)).smul (hasFDerivAt_id p)
  have he : (cmcWeight p)⁻¹ • ContinuousLinearMap.id ℝ Plane +
      ((-((cmcWeight p)^2)⁻¹) • ((cmcWeight p)⁻¹ • innerSL ℝ p)).smulRight p =
      cmcJacobian p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [cmcJacobian,add_apply,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_eq_mul,smul_smul]
    have hc : -((cmcWeight p)^2)⁻¹*(cmcWeight p)⁻¹*⟪p,v⟫ =
        -(((cmcWeight p)^3)⁻¹*⟪p,v⟫) := by field_simp
    rw [hc,neg_smul,sub_eq_add_neg]
  exact he ▸ h

lemma cmcJacobian_apply (p v : Plane) :
    cmcJacobian p v=(cmcWeight p)⁻¹ • v -
      (((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p := by
  simp only [cmcJacobian,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcJacobian_self (p v : Plane) :
    ⟪v,cmcJacobian p v⟫=
      ((cmcWeight p)^2*‖v‖^2-⟪p,v⟫^2)/(cmcWeight p)^3 := by
  rw [cmcJacobian_apply,inner_sub_right,inner_smul_right,inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm v p]
  field_simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquation
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

lemma cmcJacobian_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcJacobian := by
  have he : cmcJacobian=fderiv ℝ cmcFlux := funext (fun p ↦ (cmcFlux_hasFDerivAt p).fderiv.symm)
  rw [he]
  exact cmcFlux_contDiff.fderiv_right (by simp)

lemma cmcJacobian_symmetric (p v w : Plane) :
    ⟪v,cmcJacobian p w⟫=⟪cmcJacobian p v,w⟫ := by
  simp only [cmcJacobian_apply,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    RCLike.conj_to_real]
  rw [real_inner_comm v p]
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneWeakGradient
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

lemma continuous_local_scalar_product {f η : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hf : ContinuousOn f S) (hη : Continuous η)
    (hs : tsupport η⊆S) : Continuous (fun y ↦ f y*η y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact ((hf y (hs hy)).continuousAt (hS.mem_nhds (hs hy))).mul hη.continuousAt
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma C1_local_integration_by_parts {g ψ : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hg : Continuous g) (hgc : ContDiffOn ℝ 1 g S)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S) (v : Plane) :
    (∫ y, fderiv ℝ g y v*ψ y)= -(∫ y,g y*fderiv ℝ ψ y v) := by
  have hdf : ContinuousOn (fun y ↦ fderiv ℝ g y v) S :=
    (hgc.continuousOn_fderiv_of_isOpen hS (by simp)).clm_apply continuousOn_const
  have hi₁ : Integrable (fun y ↦ fderiv ℝ g y v*ψ y) :=
    (continuous_local_scalar_product hS hdf hψ.continuous hs).integrable_of_hasCompactSupport hc.mul_left
  have hi₂ : Integrable (fun y ↦ g y*fderiv ℝ ψ y v) :=
    (hg.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ g y*ψ y) :=
    (hg.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun y hy ↦ ((hgc y (hs hy)).contDiffAt (hS.mem_nhds (hs hy))).differentiableAt (by simp))
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [neg_neg] using congrArg Neg.neg hh.symm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_HolderNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.mono {g : Plane → ℝ} {p B : Plane → Plane} {U W : Set Plane}
    (hw : LinearCMCEquation g p B U) (hW : W⊆U) : LinearCMCEquation g p B W :=
  fun ψ hψ hc hs ↦ hw ψ hψ hc (hs.trans hW)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_decompose (v : Plane) : v=v 0 • EuclideanSpace.single 0 (1 : ℝ)+
    v 1 • EuclideanSpace.single 1 (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquationNear
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

lemma planeDivergence_continuous {F : Plane → Plane} (hF : ContDiff ℝ 1 F) :
    Continuous (planeDivergence F) := by
  have hd := hF.continuous_fderiv (by simp)
  exact ((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const))

lemma plane_component_fderiv {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) (y v : Plane) :
    fderiv ℝ (fun z ↦ F z i) y v=(fderiv ℝ F y v) i := by
  have hh := (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).hasFDerivAt.comp y
    ((hF.differentiable (by simp) y).hasFDerivAt)
  have he := hh.fderiv
  change fderiv ℝ (fun z ↦ F z i) y=_ at he
  rw [he]
  rfl

lemma plane_divergence_integration_by_parts {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ y,planeDivergence F y*ψ y)= -(∫ y,fderiv ℝ ψ y (F y)) := by
  have hcomp (i : Fin 2) : ContDiff ℝ 1 (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hi (i : Fin 2) : Integrable (fun y ↦ (fderiv ℝ F y (EuclideanSpace.single i 1)) i*ψ y) :=
    (((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).continuous.comp
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hj (i : Fin 2) : Integrable (fun y ↦ F y i*fderiv ℝ ψ y (EuclideanSpace.single i 1)) :=
    ((hcomp i).continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ _).mul_left
  have hpart (i : Fin 2) := C1_local_integration_by_parts isOpen_univ (hcomp i).continuous
    (hcomp i).contDiffOn hψ hc (subset_univ _) (EuclideanSpace.single i 1)
  simp_rw [plane_component_fderiv hF] at hpart
  have he (y : Plane) : fderiv ℝ ψ y (F y)=
      F y 0*fderiv ℝ ψ y (EuclideanSpace.single 0 1)+
      F y 1*fderiv ℝ ψ y (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [plane_decompose (F y)]
    simp
  simp_rw [planeDivergence,add_mul,he]
  rw [integral_add (hi 0) (hi 1),hpart 0,hpart 1,integral_add (hj 0) (hj 1)]
  ring

lemma classical_divergence_of_weak {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {S : Set Plane} (hS : IsOpen S) {H : ℝ}
    (hw : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ⊆S →
      (∫ y,fderiv ℝ ψ y (F y))=H*(∫ y,ψ y)) :
    ∀ y∈S,planeDivergence F y= -H := by
  have hd := (planeDivergence_continuous hF).add (continuous_const (y := H))
  have hae := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hd.locallyIntegrable.locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · have hae' : (fun y ↦ planeDivergence F y+H)=ᵐ[volume.restrict S] (fun _ ↦ (0:ℝ)) := by
      change ∀ᵐ y ∂volume.restrict S,planeDivergence F y+H=0
      rw [ae_restrict_iff' hS.measurableSet]
      exact hae
    have he := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hS hd.continuousOn continuousOn_const
    intro y hy
    exact eq_neg_of_add_eq_zero_left (he hy)
  · have hi : Integrable (fun y ↦ planeDivergence F y*ψ y) volume := ((planeDivergence_continuous hF).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
    have hj : Integrable (fun y ↦ H*ψ y) volume := (hψ.continuous.integrable_of_hasCompactSupport hc).const_mul H
    simp only [smul_eq_mul,Pi.add_apply,mul_add]
    simp_rw [mul_comm (ψ _) (planeDivergence F _),mul_comm (ψ _) H]
    rw [integral_add hi hj,plane_divergence_integration_by_parts hF (hψ.of_le (by simp)) hc,
      hw ψ hψ hc hs,integral_const_mul]
    ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_TorusC2CMCAt
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

lemma plane_gradient_mul {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y ↦ f y*g y) x=f x • gradient g x+g x • gradient f x := by
  apply ext_inner_left ℝ
  intro v
  simp only [inner_gradient_right,inner_add_right,real_inner_smul_right,
    fderiv_fun_mul hf hg,add_apply,smul_apply,smul_eq_mul,starRingEnd_apply,star_trivial]

lemma plane_gradient_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient f) :=
  (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (by simp))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_components (u v : Plane) : ⟪u,v⟫=u 0*v 0+u 1*v 1 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,star_trivial]
  ring

lemma plane_gradient_component (f : Plane → ℝ) (y : Plane) (i : Fin 2) :
    gradient f y i=fderiv ℝ f y (EuclideanSpace.single i 1) := by
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

lemma planeDivergence_add {F G : Plane → Plane} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    planeDivergence (fun z ↦ F z+G z) y=planeDivergence F y+planeDivergence G y := by
  simp only [planeDivergence,fderiv_fun_add hF hG,add_apply,PiLp.add_apply]
  ring

lemma planeDivergence_smul {a : Plane → ℝ} {F : Plane → Plane} {y : Plane}
    (ha : DifferentiableAt ℝ a y) (hF : DifferentiableAt ℝ F y) :
    planeDivergence (fun z ↦ a z • F z) y=
      a y*planeDivergence F y+⟪gradient a y,F y⟫ := by
  rw [plane_inner_components]
  simp only [plane_gradient_component,planeDivergence,fderiv_fun_smul ha hF,
    add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_hessian_direction {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v : Plane) : fderiv ℝ (gradient g) y v=
      gradient (fun z ↦ fderiv ℝ g z v) y := by
  ext i
  rw [← plane_component_fderiv ((plane_gradient_contDiff hg).of_le (by simp))]
  simp_rw [plane_gradient_component]
  rw [fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) v _

lemma plane_hessian_symmetric {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v w : Plane) : ⟪fderiv ℝ (gradient g) y v,w⟫=⟪v,fderiv ℝ (gradient g) y w⟫ := by
  rw [plane_hessian_direction hg,plane_hessian_direction hg]
  conv_rhs => rw [real_inner_comm]
  rw [inner_gradient_left,inner_gradient_left,fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) w v

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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_GraphInverseMetric
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

lemma LinearCMCEquation.classical_zero {g f : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hU : IsOpen U)
    (hw : LinearCMCEquation f (gradient g) (fun _ ↦ 0) U) :
    ∀ y∈U,planeDivergence (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) y=0 := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) :=
    (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)).clm_apply (plane_gradient_contDiff hf)
  have ht := classical_divergence_of_weak (H := 0) (hF.of_le (by simp)) hU
    (fun ψ hψ hc hs ↦ by simpa only [sub_zero,zero_mul] using hw ψ hψ hc hs)
  simpa only [neg_zero] using ht

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GraphNormalExtensionDivergence
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

lemma localRadialSquared_lt_iff (a : Torus) (x : Cover) {r : ℝ}
    (hr : 0 ≤ r) (hs : r≤1/4) :
    localRadialSquared a x < r^2 ↔ quotientMap x∈Metric.ball a r := by
  have he := periodic_representative (localRadialSquared_periodic a) x
  rw [← he]
  change quotientMap x∈sublevelRegion (localRadialSquared a) (r^2) ↔ _
  rw [sublevelRegion_localRadialSquared a hr hs]

theorem exists_periodic_local_cutoff (a : Torus) {U : Set Torus}
    (hU : IsOpen U) (ha : a∈U) :
    ∃ φ : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ m x,φ (x+latticeVector m)=φ x) ∧ (∀ x,φ x∈Icc 0 1) ∧
      (∃ W : Set Torus,IsOpen W ∧ a∈W ∧
        ∀ x,quotientMap x∈W → ∀ᶠ y in 𝓝 x,φ y=1) ∧
      ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0 := by
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU a ha
  let r := min (ε/4) (1/8 : ℝ)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrsmall : 2*r≤1/4 := by dsimp [r]; linarith [min_le_right (ε/4) (1/8 : ℝ)]
  have hrε : 2*r<ε := by dsimp [r]; linarith [min_le_left (ε/4) (1/8 : ℝ)]
  let q := localRadialSquared a
  let φ : Cover → ℝ := fun x ↦ Real.smoothTransition ((r^2-q x)/(r^2/2))
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := localRadialSquared_contDiff a
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const _)
  have hden : 0 < r^2/2 := by positivity
  refine ⟨φ,hφ,?_,?_,?_,?_⟩
  · intro m x
    simp only [φ,q,localRadialSquared_periodic]
  · intro x
    exact ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  · refine ⟨Metric.ball a (r/2),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),?_⟩
    intro x hx
    have hxq : q x<(r/2)^2 := (localRadialSquared_lt_iff a x (by positivity) (by linarith)).mpr hx
    have hn : ∀ᶠ y in 𝓝 x,q y < r^2/2 := hq.continuous.continuousAt.eventually_lt_const (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ hden).mpr (by nlinarith)
  · intro x hx
    have hnot : quotientMap x∉Metric.ball a (2*r) := fun hh ↦ hx (hεU (Metric.ball_subset_ball hrε.le hh))
    have hxq : (2*r)^2≤q x := le_of_not_gt (fun hh ↦ hnot ((localRadialSquared_lt_iff a x (by positivity) hrsmall).mp hh))
    have hn : ∀ᶠ y in 𝓝 x,r^2<q y := hq.continuous.continuousAt.eventually_const_lt (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_normal_base {F : Cover → ℝ} (hF : Continuous F)
    (μ : FiniteMeasure NormalBundle) :
    Integrable (fun z : NormalBundle ↦ F z.1) (μ : Measure NormalBundle) :=
  (hF.comp normalEmbedding_continuous.fst).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TorusCoordinatePermute
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

lemma openRepresentative_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    openRepresentative E=openRepresentative F := by
  unfold openRepresentative
  apply congrArg (fun A : Set Torus ↦ Aᶜ)
  apply volumeSupport_congr_ae
  filter_upwards [h] with z hz
  exact congrArg Not hz

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateReflection
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma coordinateReflection_continuous (i : Fin 3) : Continuous (coordinateReflection i) :=
  (coordinateReflection_isometry i).continuous

lemma coordinateReflection_measurePreserving (i : Fin 3) :
    MeasurePreserving (coordinateReflection i) torusVolume torusVolume := by
  have h (j : Fin 3) : MeasurePreserving
      (fun a : AddCircle (1 : ℝ) => if j=i then -a else a) volume volume := by
    by_cases hj : j=i
    · simpa only [ite_eq_left hj] using (Measure.measurePreserving_neg (volume : Measure (AddCircle (1 : ℝ))))
    · simp only [ite_eq_right hj]
      constructor
      · exact measurable_id
      · exact Measure.map_id
  exact product_to_torus_measurePreserving.comp ((volume_preserving_pi h).comp torus_to_product_measurePreserving)

lemma quotientMap_coordinateReflection (i : Fin 3) (x : Cover) :
    quotientMap (coverCoordinateReflection i x)=coordinateReflection i (quotientMap x) := by
  ext j
  by_cases h : j=i <;> simp [quotientMap,h]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma reflectionCompetitor_measurable (i : Fin 3) {E B : Set Torus}
    (hE : MeasurableSet E) (hB : MeasurableSet B) : MeasurableSet (reflectionCompetitor i E B) :=
  (hE.inter hB).union ((coordinateReflection_continuous i).measurable (hE.inter hB))

lemma reflectionCompetitor_disjoint_parts (i : Fin 3) (E : Set Torus) {B : Set Torus}
    (hb : Disjoint B (coordinateReflection i ⁻¹' B)) :
    Disjoint (E∩B) (coordinateReflection i ⁻¹' (E∩B)) :=
  hb.mono inter_subset_right (preimage_mono inter_subset_right)

lemma reflectionCompetitor_volume (i : Fin 3) {E B : Set Torus}
    (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hb : Disjoint B (coordinateReflection i ⁻¹' B)) :
    torusVolume (reflectionCompetitor i E B)=2*torusVolume (E∩B) := by
  rw [reflectionCompetitor,measure_union (reflectionCompetitor_disjoint_parts i E hb)
    ((coordinateReflection_continuous i).measurable (hE.inter hB)),
    (coordinateReflection_measurePreserving i).measure_preimage (hE.inter hB).nullMeasurableSet,two_mul]

lemma reflectionCompetitor_realVolume (i : Fin 3) {E B : Set Torus}
    (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hb : Disjoint B (coordinateReflection i ⁻¹' B)) :
    torusVolume.real (reflectionCompetitor i E B)=2*torusVolume.real (E∩B) := by
  simp only [Measure.real_def,reflectionCompetitor_volume i hE hB hb,ENNReal.toReal_mul,ENNReal.toReal_ofNat]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateSine_contDiff (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (coordinateSine i) :=
  (contDiff_const.mul (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).sin

lemma coordinateSine_periodic (i : Fin 3) :
    ∀ n x,coordinateSine i (x+latticeVector n)=coordinateSine i x := by
  intro n x
  unfold coordinateSine
  simp only [PiLp.add_apply,latticeVector]
  rw [show 2*Real.pi*(x i+(n i : ℝ))=2*Real.pi*x i+(n i : ℝ)*(2*Real.pi) by ring,
    Real.sin_add_int_mul_two_pi]

lemma coordinateSine_reflection (i : Fin 3) (x : Cover) :
    coordinateSine i (coverCoordinateReflection i x)= -coordinateSine i x := by
  simp [coordinateSine]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma reflection_sublevel_disjoint {i : Fin 3} {q : Cover → ℝ}
    (hp : ∀ n x,q (x+latticeVector n)=q x)
    (hr : ∀ x,q (coverCoordinateReflection i x)= -q x) :
    Disjoint (sublevelRegion q 0) (coordinateReflection i ⁻¹' sublevelRegion q 0) := by
  rw [disjoint_left]
  intro z hz hz'
  let x := representative z
  have hx : quotientMap x=z := quotientMap_representative z
  have h1 := (mem_sublevelRegion_quotient hp 0 x).1 (hx ▸ hz)
  have h2 := (mem_sublevelRegion_quotient hp 0 (coverCoordinateReflection i x)).1 (by
    simpa only [quotientMap_coordinateReflection,hx,mem_preimage] using hz')
  rw [hr] at h2
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateHalf_measurable (i : Fin 3) (a : ℝ) : MeasurableSet (coordinateHalf i a) := by
  apply measurableSet_lt _ measurable_const
  exact (((EuclideanSpace.proj i).continuous.measurable.comp measurable_representative).sub_const a).const_mul _ |>.sin

lemma coordinateHalf_seam_zero (i : Fin 3) (a : ℝ) :
    torusVolume {z | Real.sin (2*Real.pi*((representative z) i-a))=0}=0 := by
  have hz (k : ℤ) : torusVolume {z : Torus | z i=((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ))}=0 := by
    have hh := (torus_coordinate_measurePreserving i).measure_preimage
      (measurableSet_singleton (((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ)))).nullMeasurableSet
    change torusVolume {z : Torus | z i=((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ))}=volume {((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ))} at hh
    rw [hh,← Metric.closedBall_zero,AddCircle.volume_closedBall]; norm_num
  apply measure_mono_null (t := ⋃ k : ℤ,{z : Torus | z i=((a+(k : ℝ)/2 : ℝ) : AddCircle (1 : ℝ))}) _
    (measure_iUnion_null hz)
  intro z hz'
  obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp hz'
  apply mem_iUnion.mpr
  refine ⟨k,?_⟩
  have hc : (representative z) i=a+(k : ℝ)/2 := by nlinarith [Real.pi_pos]
  have he := congrArg (fun w : Torus => w i) (quotientMap_representative z)
  change (((representative z) i : ℝ) : AddCircle (1 : ℝ))=z i at he
  change z i=_
  rw [← he,hc]

lemma coordinateHalf_halfturn (i : Fin 3) (a : ℝ) (z : Torus) :
    z∈coordinateHalf i (a+1/2) ↔ 0<Real.sin (2*Real.pi*((representative z) i-a)) := by
  change Real.sin (2*Real.pi*((representative z) i-(a+1/2)))<0 ↔ _
  rw [show 2*Real.pi*((representative z) i-(a+1/2))=
    2*Real.pi*((representative z) i-a)-Real.pi by ring,Real.sin_sub_pi]
  simp

lemma coordinateHalf_complement_ae (i : Fin 3) (a : ℝ) :
    coordinateHalf i (a+1/2) =ᵐ[torusVolume] (coordinateHalf i a)ᶜ := by
  have hh : ∀ᵐ z ∂torusVolume,Real.sin (2*Real.pi*((representative z) i-a))≠0 := by
    simpa only [ae_iff,not_not] using coordinateHalf_seam_zero i a
  filter_upwards [hh] with z hz
  apply propext
  refine (coordinateHalf_halfturn i a z).trans ?_
  change (0 : ℝ)<Real.sin (2*Real.pi*((representative z) i-a)) ↔
    ¬Real.sin (2*Real.pi*((representative z) i-a))<0
  constructor
  · exact fun h => not_lt.mpr h.le
  · exact fun h => lt_of_le_of_ne (le_of_not_gt h) hz.symm

lemma coordinateHalf_volume_sum (i : Fin 3) (a : ℝ) {E : Set Torus}
    (hE : MeasurableSet E) :
    torusVolume.real (E∩coordinateHalf i a)+torusVolume.real (E∩coordinateHalf i (a+1/2))=
      torusVolume.real E := by
  have he : (E∩coordinateHalf i (a+1/2) : Set Torus) =ᵐ[torusVolume] (E∩(coordinateHalf i a)ᶜ : Set Torus) :=
    by
      filter_upwards [coordinateHalf_complement_ae i a] with z hz
      exact congrArg (fun halfMembership : Prop => z∈E ∧ halfMembership) hz
  simp_rw [Measure.real_def]
  rw [measure_congr he]
  change torusVolume.real (E∩coordinateHalf i a)+torusVolume.real (E∩(coordinateHalf i a)ᶜ)=torusVolume.real E
  rw [← measureReal_union (Disjoint.mono inter_subset_right inter_subset_right disjoint_compl_right)
    (hE.inter (coordinateHalf_measurable i a).compl)]
  congr 1
  ext z; simp only [mem_union,mem_inter_iff,mem_compl_iff]; tauto

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceGraphBundleMeasure
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma mem_coordinateHalf_quotient (i : Fin 3) (a : ℝ) (x : Cover) :
    quotientMap x∈coordinateHalf i a ↔ Real.sin (2*Real.pi*(x i-a))<0 := by
  let q : Cover → ℝ := fun y => coordinateSine i (y-a • EuclideanSpace.single i 1)
  have hp : ∀ n y,q (y+latticeVector n)=q y := by
    intro n y
    dsimp [q]
    rw [show y+latticeVector n-a • EuclideanSpace.single i 1=
      (y-a • EuclideanSpace.single i 1)+latticeVector n by abel,coordinateSine_periodic]
  have he := periodic_representative hp x
  simp only [q,coordinateSine,PiLp.sub_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,
    smul_eq_mul,mul_one] at he
  change Real.sin (2*Real.pi*((representative (quotientMap x)) i-a))<0 ↔ _
  rw [he]

lemma coordinateHalf_zero (i : Fin 3) : coordinateHalf i 0=sublevelRegion (coordinateSine i) 0 := by
  ext z
  simp only [coordinateHalf,sublevelRegion,coordinateSine,sub_zero,mem_ofPred_eq]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateHalf_open (i : Fin 3) : IsOpen (coordinateHalf i 0) := by
  rw [coordinateHalf_zero]
  change IsOpen {z : Torus | coordinateSine i (representative z)<0}
  exact isOpen_lt (continuous_periodic_descent (coordinateSine_contDiff i).continuous
    (coordinateSine_periodic i)) continuous_const

lemma coordinateHalf_eq_slab_image (i : Fin 3) : coordinateHalf i 0=
    quotientMap '' {x : Cover | (1/2 : ℝ)<x i ∧ x i<1} := by
  ext z
  constructor
  · intro hz
    refine ⟨representative z,?_,quotientMap_representative z⟩
    have hr := (representative_mem_fundamentalCube z) i
    change 0 ≤ representative z i ∧ representative z i<1 at hr
    refine ⟨?_,hr.2⟩
    by_contra hn
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (mul_nonneg (by positivity : 0≤2*Real.pi) hr.1)
      (show 2*Real.pi*representative z i≤Real.pi by nlinarith [Real.pi_pos,le_of_not_gt hn])
    change Real.sin (2*Real.pi*(representative z i-0))<0 at hz
    simp only [sub_zero] at hz
    exact not_lt_of_ge hs hz
  · rintro ⟨x,hx,rfl⟩
    rw [mem_coordinateHalf_quotient,sub_zero]
    have hs := Real.sin_neg_of_neg_of_neg_pi_lt
      (show 2*Real.pi*x i-2*Real.pi<0 by nlinarith [Real.pi_pos,hx.2])
      (show -Real.pi<2*Real.pi*x i-2*Real.pi by nlinarith [Real.pi_pos,hx.1])
    simpa only [Real.sin_sub_two_pi] using hs

lemma coordinateHalf_preconnected (i : Fin 3) : IsPreconnected (coordinateHalf i 0) := by
  rw [coordinateHalf_eq_slab_image]
  have hc : Convex ℝ {x : Cover | (1/2 : ℝ)<x i ∧ x i<1} := by
    exact (convex_Ioo (1/2 : ℝ) 1).linear_preimage (EuclideanSpace.proj i).toLinearMap
  exact hc.isPreconnected.image _ continuous_quotientMap.continuousOn

lemma coordinateReflection_preimage_half (i : Fin 3) :
    coordinateReflection i ⁻¹' coordinateHalf i 0=coordinateHalf i (1/2) := by
  ext z
  obtain ⟨x,rfl⟩ := quotientMap_surjective z
  simp only [mem_preimage]
  rw [← quotientMap_coordinateReflection,mem_coordinateHalf_quotient,mem_coordinateHalf_quotient]
  simp only [sub_zero,coverCoordinateReflection_apply,ite_true,mul_neg,Real.sin_neg]
  rw [show 2*Real.pi*(x i-1/2)=2*Real.pi*x i-Real.pi by ring,Real.sin_sub_pi]

lemma coordinateHalf_realVolume (i : Fin 3) : torusVolume.real (coordinateHalf i 0)=1/2 := by
  have hh := coordinateHalf_volume_sum i 0 MeasurableSet.univ
  simp only [univ_inter,zero_add] at hh
  have he : torusVolume (coordinateHalf i (1/2))=torusVolume (coordinateHalf i 0) := by
    rw [← coordinateReflection_preimage_half]
    exact (coordinateReflection_measurePreserving i).measure_preimage (coordinateHalf_measurable i 0).nullMeasurableSet
  have her : torusVolume.real (coordinateHalf i (1/2))=torusVolume.real (coordinateHalf i 0) :=
    congrArg ENNReal.toReal he
  rw [her] at hh
  have hu : torusVolume.real univ=1 := by simp [Measure.real_def]
  rw [hu] at hh
  linarith

lemma reflectionCompetitor_retained (i : Fin 3) (E : Set Torus) {B : Set Torus}
    (hd : Disjoint B (coordinateReflection i ⁻¹' B)) :
    E∩B=reflectionCompetitor i E B∩B := by
  ext z
  constructor
  · exact fun hz => ⟨Or.inl hz,hz.2⟩
  · rintro ⟨hz,hzB⟩
    rcases hz with hh|hh
    · exact hh
    · exact False.elim (disjoint_left.mp hd hzB hh.2)

lemma reflectionCompetitor_invariant (i : Fin 3) (E B : Set Torus) :
    coordinateReflection i ⁻¹' reflectionCompetitor i E B=reflectionCompetitor i E B := by
  ext z
  simp only [reflectionCompetitor,mem_preimage,mem_union,mem_inter_iff,coordinateReflection_involutive]
  tauto

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceH1Translation
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

lemma planeDivergence_sub {F G : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Plane) :
    planeDivergence (fun y => F y-G y) x=planeDivergence F x-planeDivergence G x := by
  simp only [planeDivergence,fderiv_fun_sub (hF.differentiable (by simp) x)
    (hG.differentiable (by simp) x),sub_apply,PiLp.sub_apply]
  ring

lemma planeDivergence_contDiff {F : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : PlaneSmooth (planeDivergence F) := by
  unfold planeDivergence
  exact ((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const))

lemma planeElliptic_contDiff {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f) : PlaneSmooth (planeElliptic A f) :=
  planeDivergence_contDiff (hA.clm_apply (plane_gradient_contDiff hf))

lemma planeDrift_contDiff {b : Plane → Plane} {f : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : PlaneSmooth f) : PlaneSmooth (planeDrift b f) :=
  (hf.fderiv_right (by simp)).clm_apply hb

lemma planeDrift_compact {b : Plane → Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (planeDrift b f) := by
  apply (hc.fderiv ℝ).mono
  intro x hx hz
  exact hx (by simp [planeDrift,hz])

lemma planeDivergence_compact {F : Plane → Plane} (hc : HasCompactSupport F) :
    HasCompactSupport (planeDivergence F) := by
  apply (hc.fderiv ℝ).mono
  intro x hx hz
  exact hx (by simp [planeDivergence,hz])

lemma planeElliptic_compact {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (planeElliptic A f) := by
  apply planeDivergence_compact
  apply (plane_gradient_compact hc).mono
  intro x hx hz
  exact hx (by simp [hz])

lemma planeDivergence_integral_zero {F : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    (∫ x,planeDivergence F x)=0 := by
  have hcomp (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hcc (i : Fin 2) : HasCompactSupport (fun y => F y i) := by
    apply hc.mono
    intro x hx hz
    exact hx (by simp [hz])
  have hi (i : Fin 2) : Integrable (fun y => fderiv ℝ (fun z => F z i) y
      (EuclideanSpace.single i 1)) :=
    (((hcomp i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hcc i).fderiv_apply ℝ _)
  have hp (i : Fin 2) := C1_local_integration_by_parts (g := fun _ : Plane => (1:ℝ)) isOpen_univ continuous_const
    contDiffOn_const ((hcomp i).of_le (by simp)) (hcc i)
    (subset_univ _) (EuclideanSpace.single i 1)
  simp only [fderiv_fun_const,one_mul] at hp
  simp only [plane_component_fderiv (hF.of_le (by simp))] at hi hp
  have hz (i : Fin 2) : (∫ y, ((fderiv ℝ F y) (EuclideanSpace.single i 1)) i)=0 := by
    simpa using (hp i).symm
  simp only [planeDivergence]
  rw [integral_add (hi 0) (hi 1),hz 0,hz 1,add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeEnergy_contDiff {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hu : PlaneSmooth u) : PlaneSmooth (planeEnergy A u) :=
  (plane_gradient_contDiff hu).inner ℝ (hA.clm_apply (plane_gradient_contDiff hu))

lemma planeEnergy_compact {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hc : HasCompactSupport u) : HasCompactSupport (planeEnergy A u) := by
  apply (plane_gradient_compact hc).mono
  intro x hx hz
  exact hx (by simp [planeEnergy,hz])

lemma planeEnergy_fderiv {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hu : PlaneSmooth u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (x v : Plane) :
    fderiv ℝ (planeEnergy A u) x v=
      2*⟪fderiv ℝ (gradient u) x v,A x (gradient u x)⟫+
      ⟪gradient u x,(fderiv ℝ A x v) (gradient u x)⟫ := by
  have hg := (plane_gradient_contDiff hu).differentiable (by simp) x
  have ha := hA.differentiable (by simp) x
  unfold planeEnergy
  rw [fderiv_inner_apply ℝ hg (ha.clm_apply hg),fderiv_clm_apply ha hg]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,inner_add_right]
  rw [hAs x (gradient u x) (fderiv ℝ (gradient u) x v)]
  ring

lemma planeDrift_fderiv {b : Plane → Plane} {u : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : PlaneSmooth u) (x v : Plane) :
    fderiv ℝ (planeDrift b u) x v=
      ⟪fderiv ℝ (gradient u) x (b x),v⟫+⟪gradient u x,fderiv ℝ b x v⟫ := by
  have he : planeDrift b u=fun y => ⟪gradient u y,b y⟫ := by
    funext y
    exact inner_gradient_left.symm
  rw [he,fderiv_inner_apply ℝ ((plane_gradient_contDiff hu).differentiable (by simp) x)
    (hb.differentiable (by simp) x),plane_hessian_symmetric hu]
  rw [real_inner_comm v]
  ring

lemma planeRellichFlux_contDiff {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : PlaneSmooth u) :
    ContDiff ℝ (⊤ : ℕ∞) (planeRellichFlux A b u) :=
  ((((contDiff_const.mul (planeDrift_contDiff hb hu)).add
    ((planeDivergence_contDiff hb).mul hu)).smul
      (hA.clm_apply (plane_gradient_contDiff hu))).sub
    ((planeEnergy_contDiff hA hu).smul hb)).sub
    ((contDiff_const.mul (hu.pow 2)).smul
      (hA.clm_apply (plane_gradient_contDiff (planeDivergence_contDiff hb))))

lemma planeRellichFlux_compact {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {u : Plane → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (planeRellichFlux A b u) := by
  apply (((planeDrift_compact (b := b) hc).mul_left.add hc.mul_left).smul_right.sub
    (planeEnergy_compact hc).smul_right).sub
  have hpow : HasCompactSupport (fun x => u x^2) := hc.mono (by
    intro x hx hz
    exact hx (by simp [hz]))
  exact hpow.mul_left.smul_right

theorem planeRellichFlux_divergence {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : PlaneSmooth u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (x : Plane) :
    planeDivergence (planeRellichFlux A b u) x=
      planeElliptic A u x*(2*planeDrift b u x+planeDivergence b x*u x)+
      2*⟪gradient u x,fderiv ℝ b x (A x (gradient u x))⟫-
      ⟪gradient u x,(fderiv ℝ A x (b x)) (gradient u x)⟫-
      (1/2:ℝ)*planeElliptic A (planeDivergence b) x*u x^2 := by
  have hd := planeDivergence_contDiff hb
  have hG := hA.clm_apply (plane_gradient_contDiff hu)
  have hD := hA.clm_apply (plane_gradient_contDiff hd)
  have hK : PlaneSmooth (fun y => 2*planeDrift b u y+planeDivergence b y*u y) :=
    (contDiff_const.mul (planeDrift_contDiff hb hu)).add (hd.mul hu)
  have hE := planeEnergy_contDiff hA hu
  have hW : PlaneSmooth (fun y => (1/2:ℝ)*u y^2) := contDiff_const.mul (hu.pow 2)
  unfold planeRellichFlux
  erw [planeDivergence_sub ((hK.smul hG).sub (hE.smul hb)) (hW.smul hD),
    planeDivergence_sub (hK.smul hG) (hE.smul hb),
    planeDivergence_smul (hK.differentiable (by simp) x) (hG.differentiable (by simp) x),
    planeDivergence_smul (hE.differentiable (by simp) x) (hb.differentiable (by simp) x),
    planeDivergence_smul (hW.differentiable (by simp) x) (hD.differentiable (by simp) x)]
  simp only [inner_gradient_left]
  rw [fderiv_fun_add ((contDiff_const.mul (planeDrift_contDiff hb hu)).differentiable (by simp) x)
      ((hd.mul hu).differentiable (by simp) x),
    fderiv_const_mul ((planeDrift_contDiff hb hu).differentiable (by simp) x),
    fderiv_fun_mul (hd.differentiable (by simp) x) (hu.differentiable (by simp) x),
    fderiv_const_mul ((hu.pow 2).differentiable (by simp) x),
    fderiv_fun_pow 2 (hu.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [planeDrift_fderiv hb hu,planeEnergy_fderiv hA hu hAs]
  simp only [← inner_gradient_left,planeElliptic,planeEnergy]
  rw [hAs x (gradient u x) (gradient (planeDivergence b) x)]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeCarlemanFlux_contDiff {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeCarlemanFlux A b q τ u) :=
  by
  unfold planeCarlemanFlux
  exact ((planeRellichFlux_contDiff hA hb hu).const_smul (2*τ)).add
    ((((contDiff_const (c := 2*τ^3)).mul hq).mul (hu.pow 2)).smul hb)

lemma planeCarlemanFlux_compact {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hc : HasCompactSupport u) (τ : ℝ) :
    HasCompactSupport (planeCarlemanFlux A b q τ u) := by
  unfold planeCarlemanFlux
  apply HasCompactSupport.add
  · apply (planeRellichFlux_compact (A := A) (b := b) hc).mono
    intro x hx hz
    exact hx (by simp only [hz,smul_zero])
  · have hpow : HasCompactSupport (fun x => u x^2) := hc.mono (by
      intro x hx hz
      exact hx (by simp [hz]))
    exact hpow.mul_left.smul_right

lemma planeCarlemanP_contDiff {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u) (τ : ℝ) :
    PlaneSmooth (planeCarlemanP A b q τ u) :=
  by
  unfold planeCarlemanP planeCarlemanS planeCarlemanT
  exact ((planeElliptic_contDiff hA hu).add ((contDiff_const.mul hq).mul hu)).add
    (contDiff_const.mul ((contDiff_const.mul (planeDrift_contDiff hb hu)).add
      ((planeDivergence_contDiff hb).mul hu)))

lemma planeCarlemanP_compact {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hc : HasCompactSupport u) (τ : ℝ) :
    HasCompactSupport (planeCarlemanP A b q τ u) :=
  by
  unfold planeCarlemanP planeCarlemanS planeCarlemanT
  exact ((planeElliptic_compact hc).add hc.mul_left).add
    (((planeDrift_compact hc).mul_left.add hc.mul_left).mul_left)

theorem planeCarleman_pointwise {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) (x : Plane) :
    (planeCarlemanP A b q τ u x)^2+planeDivergence (planeCarlemanFlux A b q τ u) x=
      (planeCarlemanS A q τ u x)^2+(planeCarlemanT b τ u x)^2+
      τ*planeCarlemanR A b x (gradient u x)+
      (2*τ^3*planeDrift b q x-τ*planeElliptic A (planeDivergence b) x)*u x^2 := by
  have hf := planeRellichFlux_contDiff hA hb hu
  have hk : PlaneSmooth (fun y => 2*τ^3*q y*u y^2) :=
    (contDiff_const.mul hq).mul (hu.pow 2)
  unfold planeCarlemanFlux
  erw [planeDivergence_add ((hf.const_smul (2*τ)).differentiable (by simp) x)
      ((hk.smul hb).differentiable (by simp) x),
    planeDivergence_smul (differentiableAt_const (2*τ)) (hf.differentiable (by simp) x),
    planeDivergence_smul (hk.differentiable (by simp) x) (hb.differentiable (by simp) x)]
  simp only [add_zero,inner_gradient_left,fderiv_fun_const,Pi.zero_apply,zero_apply]
  rw [planeRellichFlux_divergence hA hb hu hAs,
    fderiv_fun_mul ((contDiff_const.mul hq).differentiable (by simp) x)
      ((hu.pow 2).differentiable (by simp) x),
    fderiv_const_mul (hq.differentiable (by simp) x),
    fderiv_fun_pow 2 (hu.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  simp only [planeCarlemanP,planeCarlemanS,planeCarlemanT,planeCarlemanR,planeDrift]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma carleman_scalar_coercivity {C D Q c τ E R S T z q d l : ℝ}
    (hC : 0≤C) (hD : 0≤D) (hτ : 1≤τ) (hbudget : D+(C+1)^2≤τ)
    (hpseudo : 2≤2*c-(C+1)*Q) (hR : -C*E≤R) (hq : q≤Q)
    (hd : c≤d) (hl : l≤D) :
    τ*E+τ^3*z^2≤S^2+T^2+τ*R+(2*τ^3*d-τ*l)*z^2+
      (C+1)*τ*(z*(S-τ^2*q*z)+E) := by
  have ht : 0≤τ := by linarith
  have ha : 0≤C+1 := by linarith
  have ht2 : τ≤τ^2 := by nlinarith
  have hb : 0≤τ^3-D*τ-(C+1)^2*τ^2 := by
    have h₁ := mul_le_mul_of_nonneg_left ht2 hD
    have h₂ := mul_le_mul_of_nonneg_right hbudget (sq_nonneg τ)
    nlinarith
  have hs : 0≤S^2+(C+1)*τ*S*z+(C+1)^2*τ^2*z^2 := by
    nlinarith only [sq_nonneg (S+(C+1)*τ*z),sq_nonneg S,
      sq_nonneg ((C+1)*τ*z)]
  have h₁ : 0≤τ*(R+C*E) := mul_nonneg ht (by linarith)
  have h₂ : 0≤(2*τ^3*(d-c))*z^2 :=
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hd)) (sq_nonneg z)
  have h₃ : 0≤((C+1)*τ^3*(Q-q))*z^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg ha (pow_nonneg ht _)) (sub_nonneg.mpr hq)) (sq_nonneg z)
  have h₄ : 0≤(τ*(D-l))*z^2 :=
    mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hl)) (sq_nonneg z)
  have h₅ : 0≤(τ^3*(2*c-(C+1)*Q-2))*z^2 :=
    mul_nonneg (mul_nonneg (pow_nonneg ht _) (by linarith)) (sq_nonneg z)
  have h₆ := mul_nonneg hb (sq_nonneg z)
  have he : S^2+T^2+τ*R+(2*τ^3*d-τ*l)*z^2+
      (C+1)*τ*(z*(S-τ^2*q*z)+E)-(τ*E+τ^3*z^2)=
      T^2+(S^2+(C+1)*τ*S*z+(C+1)^2*τ^2*z^2)+τ*(R+C*E)+
      (2*τ^3*(d-c))*z^2+((C+1)*τ^3*(Q-q))*z^2+
      (τ*(D-l))*z^2+(τ^3*(2*c-(C+1)*Q-2))*z^2+
      (τ^3-D*τ-(C+1)^2*τ^2)*z^2 := by ring
  have hh := add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (add_nonneg (sq_nonneg T) hs) h₁) h₂) h₃) h₄) h₅) h₆
  rw [← he] at hh
  exact sub_nonneg.mp hh

lemma plane_energy_flux_divergence {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hu : PlaneSmooth u) (x : Plane) :
    planeDivergence (fun y => u y • A y (gradient u y)) x=
      u x*planeElliptic A u x+planeEnergy A u x := by
  exact planeDivergence_smul (hu.differentiable (by simp) x)
    ((hA.clm_apply (plane_gradient_contDiff hu)).differentiable (by simp) x)

theorem planeCarleman_coercive {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u)
    (hc : HasCompactSupport u) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} {C D Q c τ : ℝ} (hs : tsupport u⊆U)
    (hdata : PlaneCarlemanData A b q U C D Q c)
    (hτ : 1≤τ) (hbudget : D+(C+1)^2≤τ) :
    (∫ x,τ*planeEnergy A u x+τ^3*u x^2)≤
      ∫ x,(planeCarlemanP A b q τ u x)^2 := by
  let F : Plane → Plane := fun x => planeCarlemanFlux A b q τ u x+
    ((C+1)*τ) • (u x • A x (gradient u x))
  have hG := hA.clm_apply (plane_gradient_contDiff hu)
  have hf : ContDiff ℝ (⊤ : ℕ∞) F :=
    (planeCarlemanFlux_contDiff hA hb hq hu τ).add ((hu.smul hG).const_smul ((C+1)*τ))
  have hgc : HasCompactSupport (fun x => ((C+1)*τ) • (u x • A x (gradient u x))) := by
    apply hc.mono
    intro x hx hz
    exact hx (by simp [hz])
  have hfc : HasCompactSupport F :=
    (planeCarlemanFlux_compact (A := A) (b := b) (q := q) hc τ).add hgc
  have hdiv (x : Plane) : planeDivergence F x=
      planeDivergence (planeCarlemanFlux A b q τ u) x+
        (C+1)*τ*(u x*planeElliptic A u x+planeEnergy A u x) := by
    dsimp only [F]
    erw [planeDivergence_add ((planeCarlemanFlux_contDiff hA hb hq hu τ).differentiable (by simp) x)
        (((hu.smul hG).const_smul ((C+1)*τ)).differentiable (by simp) x),
      planeDivergence_smul (differentiableAt_const ((C+1)*τ)) ((hu.smul hG).differentiable (by simp) x)]
    simp only [inner_gradient_left,fderiv_fun_const,Pi.zero_apply,zero_apply,add_zero]
    erw [plane_energy_flux_divergence hA hu]
  have hpoint (x : Plane) : τ*planeEnergy A u x+τ^3*u x^2≤
      (planeCarlemanP A b q τ u x)^2+planeDivergence F x := by
    rw [hdiv,← add_assoc,planeCarleman_pointwise hA hb hq hu hAs τ]
    by_cases hx : x∈tsupport u
    · have hh := carleman_scalar_coercivity hdata.C_nonneg hdata.D_nonneg hτ hbudget
        hdata.pseudoconvex (hdata.principal x (hs hx) (gradient u x))
        (hdata.weight_bound x (hs hx)) (hdata.transport_bound x (hs hx))
        (hdata.remainder_bound x (hs hx))
        (S := planeCarlemanS A q τ u x) (T := planeCarlemanT b τ u x) (z := u x)
      simpa only [planeEnergy,planeCarlemanS,add_sub_cancel_right] using hh
    · have hz : u x=0 := image_eq_zero_of_notMem_tsupport hx
      have hg : gradient u x=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
      simp only [planeEnergy,hg,inner_zero_left,mul_zero,hz,zero_pow (by decide : (2:ℕ)≠0),
        planeCarlemanR,map_zero,sub_self,add_zero,zero_mul]
      positivity
  have huc : HasCompactSupport (fun x => u x^2) := hc.mono (by
    intro x hx hz
    exact hx (by simp [hz]))
  have hi : Integrable (fun x => τ*planeEnergy A u x+τ^3*u x^2) :=
    (((planeEnergy_contDiff hA hu).continuous.integrable_of_hasCompactSupport
      (planeEnergy_compact hc)).const_mul τ).add
      (((hu.continuous.pow 2).integrable_of_hasCompactSupport huc).const_mul (τ^3))
  have hp := planeCarlemanP_contDiff hA hb hq hu τ
  have hpc := planeCarlemanP_compact (A := A) (b := b) (q := q) hc τ
  have hj : Integrable (fun x => (planeCarlemanP A b q τ u x)^2) :=
    (hp.continuous.pow 2).integrable_of_hasCompactSupport (hpc.mono (by
      intro x hx hz
      exact hx (by simp [hz])))
  have hk : Integrable (planeDivergence F) :=
    (planeDivergence_contDiff hf).continuous.integrable_of_hasCompactSupport
    (planeDivergence_compact hfc)
  have hm := integral_mono hi (hj.add hk) hpoint
  simp only [Pi.add_apply] at hm
  rw [integral_add hj hk,planeDivergence_integral_zero hf hfc,add_zero] at hm
  exact hm

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneQuadraticWeight
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

lemma planeQuadraticWeight_smooth (a n : Plane) (κ ε : ℝ) :
    PlaneSmooth (planeQuadraticWeight a n κ ε) :=
  ((contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)).add
    (contDiff_const.mul ((contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)).pow 2))).sub
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma planeQuadraticWeight_fderiv (a n : Plane) (κ ε : ℝ) (x : Plane) :
    fderiv ℝ (planeQuadraticWeight a n κ ε) x=
      innerSL ℝ n+(κ*⟪n,x-a⟫) • innerSL ℝ n-ε • innerSL ℝ (x-a) := by
  have hl := (innerSL ℝ n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  have hd := (hl.add ((hl.pow 2).const_mul (κ/2))).sub
    (((hasFDerivAt_id x).sub_const a).norm_sq.const_mul (ε/2))
  change HasFDerivAt (planeQuadraticWeight a n κ ε) _ x at hd
  rw [hd.fderiv]
  ext v
  simp only [add_apply,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul,
    nsmul_eq_mul,Nat.cast_ofNat,Function.comp_apply,id_eq]
  ring

lemma planeQuadraticWeight_gradient (a n : Plane) (κ ε : ℝ) (x : Plane) :
    gradient (planeQuadraticWeight a n κ ε) x=
      n+(κ*⟪n,x-a⟫) • n-ε • (x-a) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,planeQuadraticWeight_fderiv]
  simp only [add_apply,sub_apply,smul_apply,innerSL_apply_apply,
    inner_sub_left,inner_add_left,real_inner_smul_left,smul_eq_mul]

lemma planeQuadraticWeight_hessian (a n : Plane) (κ ε : ℝ) (x v : Plane) :
    fderiv ℝ (gradient (planeQuadraticWeight a n κ ε)) x v=
      (κ*⟪n,v⟫) • n-ε • v := by
  have he : gradient (planeQuadraticWeight a n κ ε)=
      fun y => n+(κ*⟪n,y-a⟫) • n-ε • (y-a) :=
    funext (planeQuadraticWeight_gradient a n κ ε)
  rw [he]
  have hl := (innerSL ℝ n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  have hd := (((hl.const_mul κ).smul_const n).const_add n).sub
    (((hasFDerivAt_id x).sub_const a).const_smul ε)
  change HasFDerivAt (fun y => n+(κ*⟪n,y-a⟫) • n-ε • (y-a)) _ x at hd
  rw [hd.fderiv]
  simp only [sub_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul]

lemma planeQuadraticWeight_gradient_center (a n : Plane) (κ ε : ℝ) :
    gradient (planeQuadraticWeight a n κ ε) a=n := by
  simp [planeQuadraticWeight_gradient]

lemma quadratic_weight_R {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a n : Plane) (κ ε : ℝ) (x w : Plane) :
    planeCarlemanR A (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y)) x w=
      4*κ*⟪n,A x w⟫^2-4*ε*‖A x w‖^2+
      4*⟪w,(fderiv ℝ A x (A x w)) (gradient (planeQuadraticWeight a n κ ε) x)⟫-
      2*⟪w,(fderiv ℝ A x (A x (gradient (planeQuadraticWeight a n κ ε) x))) w⟫ := by
  have hg := plane_gradient_contDiff (planeQuadraticWeight_smooth a n κ ε)
  rw [planeCarlemanR,fderiv_clm_apply (hA.differentiable (by simp) x)
    (hg.differentiable (by simp) x)]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    planeQuadraticWeight_hessian,map_sub,map_smul,inner_add_right,inner_sub_right,real_inner_smul_right]
  rw [hAs x w n,hAs x w (A x w),real_inner_self_eq_norm_sq]
  ring

lemma quadratic_weight_transport_center {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a n : Plane) (κ ε : ℝ) :
    planeDrift (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y))
      (planeEnergy A (planeQuadraticWeight a n κ ε)) a=
      2*κ*⟪n,A a n⟫^2-2*ε*‖A a n‖^2+⟪n,(fderiv ℝ A a (A a n)) n⟫ := by
  rw [planeDrift,planeEnergy_fderiv hA (planeQuadraticWeight_smooth a n κ ε) hAs,
    planeQuadraticWeight_gradient_center,planeQuadraticWeight_hessian]
  simp only [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_clm_bound (A : Plane →L[ℝ] Plane) (v w : Plane) :
    |⟪v,A w⟫|≤‖v‖*‖A‖*‖w‖ := by
  calc
    |⟪v,A w⟫|≤‖v‖*‖A w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖*(‖A‖*‖w‖) := mul_le_mul_of_nonneg_left (A.le_opNorm w) (norm_nonneg _)
    _ = _ := by ring

lemma plane_inner_double_clm_bound (B : Plane →L[ℝ] (Plane →L[ℝ] Plane)) (v w z : Plane) :
    |⟪v,B w z⟫|≤‖v‖*‖B‖*‖w‖*‖z‖ := by
  calc
    |⟪v,B w z⟫|≤‖v‖*‖B w‖*‖z‖ := plane_inner_clm_bound _ _ _
    _ ≤ ‖v‖*(‖B‖*‖w‖)*‖z‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (B.le_opNorm w) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

lemma quadratic_weight_R_lower {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a n : Plane) {κ ε M K P : ℝ} (hκ : 0≤κ) (hε : 0≤ε)
    {x : Plane} (hM : ‖A x‖≤M) (hK : ‖fderiv ℝ A x‖≤K)
    (hP : ‖gradient (planeQuadraticWeight a n κ ε) x‖≤P) (w : Plane) :
    -(4*ε*M^2+6*K*M*P)*‖w‖^2≤
    planeCarlemanR A (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y)) x w := by
  let p := gradient (planeQuadraticWeight a n κ ε) x
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hK0 : 0≤K := (norm_nonneg (fderiv ℝ A x)).trans hK
  have hP0 : 0≤P := (norm_nonneg _).trans hP
  have haw : ‖A x w‖≤M*‖w‖ := (A x).le_opNorm w |>.trans
    (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have hap : ‖A x p‖≤M*P := ((A x).le_opNorm p).trans
    (mul_le_mul hM hP (norm_nonneg _) hM0)
  have h₁ : |⟪w,(fderiv ℝ A x (A x w)) p⟫|≤K*M*P*‖w‖^2 := by
    calc
      _ ≤ ‖w‖*‖fderiv ℝ A x‖*‖A x w‖*‖p‖ := plane_inner_double_clm_bound _ _ _ _
      _ ≤ ‖w‖*K*(M*‖w‖)*P := by gcongr
      _ = _ := by ring
  have h₂ : |⟪w,(fderiv ℝ A x (A x p)) w⟫|≤K*M*P*‖w‖^2 := by
    calc
      _ ≤ ‖w‖*‖fderiv ℝ A x‖*‖A x p‖*‖w‖ := plane_inner_double_clm_bound _ _ _ _
      _ ≤ ‖w‖*K*(M*P)*‖w‖ := by gcongr
      _ = _ := by ring
  have hs : ‖A x w‖^2≤M^2*‖w‖^2 := by
    calc
      _ ≤ (M*‖w‖)^2 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _)) |>.mpr haw
      _ = _ := by ring
  have hsq : 0≤4*κ*⟪n,A x w⟫^2 := by positivity
  have hneg := mul_le_mul_of_nonneg_left hs (show 0≤4*ε by positivity)
  rw [quadratic_weight_R hA hAs]
  have hleft := (abs_le.mp h₁).1
  have hright := (abs_le.mp h₂).2
  dsimp only [p] at hleft hright
  nlinarith only [hleft,hright,hneg,hsq]

lemma quadratic_weight_transport_lower {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a : Plane) {n : Plane} (hn : ‖n‖=1) {κ ε M K ℓ : ℝ}
    (hκ : 0≤κ) (hε : 0≤ε) (hℓ : 0≤ℓ)
    (hell : ℓ≤⟪n,A a n⟫) (hM : ‖A a‖≤M) (hK : ‖fderiv ℝ A a‖≤K) :
    2*κ*ℓ^2-2*ε*M^2-K*M≤
    planeDrift (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y))
      (planeEnergy A (planeQuadraticWeight a n κ ε)) a := by
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hK0 : 0≤K := (norm_nonneg (fderiv ℝ A a)).trans hK
  have han : ‖A a n‖≤M := by
    simpa only [hn,mul_one] using ((A a).le_opNorm n).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg n))
  have he : |⟪n,(fderiv ℝ A a (A a n)) n⟫|≤K*M := by
    calc
      _ ≤ ‖n‖*‖fderiv ℝ A a‖*‖A a n‖*‖n‖ := plane_inner_double_clm_bound _ _ _ _
      _ = ‖fderiv ℝ A a‖*‖A a n‖ := by rw [hn]; ring
      _ ≤ K*M := mul_le_mul hK han (norm_nonneg _) hK0
  have hs₁ := mul_le_mul_of_nonneg_left
    (sq_le_sq₀ hℓ (hℓ.trans hell) |>.mpr hell) (show 0≤2*κ by positivity)
  have hs₂ := mul_le_mul_of_nonneg_left
    (sq_le_sq₀ (norm_nonneg _) hM0 |>.mpr han) (show 0≤2*ε by positivity)
  rw [quadratic_weight_transport_center hA hAs]
  linarith [(abs_le.mp he).1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_ellipticity_perturb {A B : Plane →L[ℝ] Plane} {ℓ δ : ℝ}
    (hA : ∀ v,ℓ*‖v‖^2≤⟪v,A v⟫) (hAB : ‖B-A‖≤δ) (v : Plane) :
    (ℓ-δ)*‖v‖^2≤⟪v,B v⟫ := by
  have hh := plane_inner_clm_bound (B-A) v v
  have hd : |⟪v,(B-A) v⟫|≤δ*‖v‖^2 := by
    calc
      _ ≤ ‖v‖*‖B-A‖*‖v‖ := hh
      _ ≤ ‖v‖*δ*‖v‖ := by gcongr
      _ = _ := by ring
  simp only [sub_apply,inner_sub_right] at hd
  linarith [(abs_le.mp hd).1,hA v]

theorem planeCarleman_weight_exists {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a : Plane) {n : Plane} (hn : ‖n‖=1) {ℓ ε : ℝ} (hℓ : 0<ℓ) (hε : 0<ε)
    (hell : ∀ v,ℓ*‖v‖^2≤⟪v,A a v⟫) :
    ∃ κ>0,∃ r>0,∃ C D Q c : ℝ,
      PlaneCarlemanData A (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y))
        (planeEnergy A (planeQuadraticWeight a n κ ε)) (Metric.ball a r) C D Q c ∧
      ∀ x∈Metric.ball a r,∀ v,(ℓ/2)*‖v‖^2≤⟪v,A x v⟫ := by
  let M := ‖A a‖+1
  let K := ‖fderiv ℝ A a‖+1
  let B := 4*ε*M^2+12*K*M
  let C := B/(ℓ/2)
  let Q := 4*M
  let c := ((C+1)*Q+2)/2
  have hM : 0<M := by dsimp [M]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hC : 0≤C := div_nonneg hB (by positivity)
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  let κ := max 1 ((c+2*ε*M^2+K*M+1)/(2*ℓ^2))
  have hκ : 0<κ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlarge : c+2*ε*M^2+K*M+1≤2*κ*ℓ^2 := by
    have hh := (div_le_iff₀ (show 0<2*ℓ^2 by positivity)).mp
      (le_max_right 1 ((c+2*ε*M^2+K*M+1)/(2*ℓ^2)))
    dsimp only [κ]
    nlinarith only [hh]
  let φ := planeQuadraticWeight a n κ ε
  let b : Plane → Plane := fun y => A y (gradient φ y)
  let q := planeEnergy A φ
  have hφ : PlaneSmooth φ := planeQuadraticWeight_smooth _ _ _ _
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := hA.clm_apply (plane_gradient_contDiff hφ)
  have hq : PlaneSmooth q := planeEnergy_contDiff hA hφ
  have htrans : c<planeDrift b q a := by
    have hh := quadratic_weight_transport_lower hA hAs a hn hκ.le hε.le hℓ.le
      (by simpa only [hn,one_pow,mul_one] using hell n)
      (show ‖A a‖≤M by dsimp [M]; linarith)
      (show ‖fderiv ℝ A a‖≤K by dsimp [K]; linarith)
    change 2*κ*ℓ^2-2*ε*M^2-K*M≤planeDrift b q a at hh
    linarith
  let D := |planeElliptic A (planeDivergence b) a|+1
  have hD : 0≤D := by dsimp [D]; positivity
  have hDA := hA.continuous_fderiv (by simp)
  have hevM : ∀ᶠ x in 𝓝 a,‖A x‖<M :=
    (hA.continuous.norm.tendsto a).eventually (eventually_lt_nhds (lt_add_one _))
  have hevK : ∀ᶠ x in 𝓝 a,‖fderiv ℝ A x‖<K :=
    (hDA.norm.tendsto a).eventually (eventually_lt_nhds (lt_add_one _))
  have hevp : ∀ᶠ x in 𝓝 a,‖gradient φ x‖<2 :=
    ((plane_gradient_contDiff hφ).continuous.norm.tendsto a).eventually
      (eventually_lt_nhds (by simp only [φ,planeQuadraticWeight_gradient_center,hn]; norm_num))
  have hevell : ∀ᶠ x in 𝓝 a,‖A x-A a‖<ℓ/2 :=
    ((hA.continuous.sub continuous_const).norm.tendsto a).eventually
      (eventually_lt_nhds (by change ‖A a-A a‖<ℓ/2; simp only [sub_self,norm_zero]; positivity))
  have hevt : ∀ᶠ x in 𝓝 a,c<planeDrift b q x :=
    ((planeDrift_contDiff hb hq).continuous.tendsto a).eventually (eventually_gt_nhds htrans)
  have hevd : ∀ᶠ x in 𝓝 a,planeElliptic A (planeDivergence b) x<D :=
    ((planeElliptic_contDiff hA (planeDivergence_contDiff hb)).continuous.tendsto a).eventually
      (eventually_lt_nhds (by dsimp [D]; linarith [le_abs_self (planeElliptic A (planeDivergence b) a)]))
  have hev := hevM.and (hevK.and (hevp.and (hevell.and (hevt.and hevd))))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hell' (x : Plane) (hx : x∈Metric.ball a r) (v : Plane) :
      (ℓ/2)*‖v‖^2≤⟪v,A x v⟫ := by
    have hh := plane_ellipticity_perturb hell (hball hx).2.2.2.1.le v
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  refine ⟨κ,hκ,r,hr,C,D,Q,c,?_,hell'⟩
  refine ⟨hC,hD,?_,?_,?_,?_,?_⟩
  · dsimp [c]
    linarith
  · intro x hx v
    obtain ⟨hMx,hKx,hpx,_,_,_⟩ := hball hx
    have hh := quadratic_weight_R_lower hA hAs a n hκ.le hε.le hMx.le hKx.le hpx.le v
    have hmul := mul_le_mul_of_nonneg_left (hell' x hx v) hC
    have hCB : C*(ℓ/2)=B := by dsimp [C]; exact div_mul_cancel₀ _ (by positivity)
    change -C*⟪v,A x v⟫≤planeCarlemanR A b x v
    have he : (4*ε*M^2+6*K*M*2)=B := by dsimp [B]; ring
    rw [he] at hh
    dsimp only [φ,b]
    nlinarith only [hh,hmul,hCB]
  · intro x hx
    obtain ⟨hMx,_,hpx,_,_,_⟩ := hball hx
    have hh := plane_inner_clm_bound (A x) (gradient φ x) (gradient φ x)
    change ⟪gradient φ x,A x (gradient φ x)⟫≤Q
    calc
      _ ≤ |⟪gradient φ x,A x (gradient φ x)⟫| := le_abs_self _
      _ ≤ ‖gradient φ x‖*‖A x‖*‖gradient φ x‖ := hh
      _ ≤ 2*M*2 := by gcongr
      _ = Q := by dsimp [Q]; ring
  · intro x hx
    exact (hball hx).2.2.2.2.1.le
  · intro x hx
    exact (hball hx).2.2.2.2.2.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quadratic_weight_scalar_outside {s t κ ε R : ℝ} (hR : 0<R) (ht : 0≤t)
    (hκ : 0≤κ) (hsmall : κ*t≤1) (hst : |s|≤t)
    (hout : 2*R*s≤t^2) (hε : 4/R≤ε) :
    s+(κ/2)*s^2-(ε/2)*t^2≤ -(1/R)*t^2 := by
  have hlin : s+(κ/2)*s^2≤t^2/R := by
    by_cases hs : s≤0
    · have hst' : -s≤t := by simpa only [abs_of_nonpos hs] using hst
      have hsκ : κ*(-s)≤1 :=
        (mul_le_mul_of_nonneg_left hst' hκ).trans hsmall
      have hh := mul_le_mul_of_nonneg_right hsκ (neg_nonneg.mpr hs)
      have hn : 0≤t^2/R := div_nonneg (pow_nonneg ht 2) hR.le
      nlinarith only [hh,hn,hs]
    · have hs0 : 0≤ s := le_of_not_ge hs
      have hst' : s≤t := (le_abs_self _).trans hst
      have hsκ : κ*s≤1 := (mul_le_mul_of_nonneg_left hst' hκ).trans hsmall
      have hh := mul_le_mul_of_nonneg_right hsκ hs0
      have hhout : 2*s≤t^2/R := (le_div_iff₀ hR).mpr (by nlinarith only [hout])
      nlinarith only [hh,hhout,hs0]
  have he := mul_le_mul_of_nonneg_right hε (sq_nonneg t)
  have heq₁ : (4/R)*t^2=4*(t^2/R) := by ring
  have heq₂ : -(1/R)*t^2= -(t^2/R) := by ring
  rw [heq₁] at he
  rw [heq₂]
  nlinarith only [he,hlin]

lemma planeQuadraticWeight_outside {a n x : Plane} {κ ε R : ℝ}
    (hn : ‖n‖=1) (hR : 0<R) (hκ : 0≤κ) (hsmall : κ*‖x-a‖≤1)
    (hout : R≤‖x-(a+R • n)‖) (hε : 4/R≤ε) :
    planeQuadraticWeight a n κ ε x≤ -(1/R)*‖x-a‖^2 := by
  have hst : |⟪n,x-a⟫|≤‖x-a‖ := by
    simpa only [hn,one_mul] using abs_real_inner_le_norm n (x-a)
  have he : ‖x-(a+R • n)‖^2=‖x-a‖^2+R^2-2*R*⟪n,x-a⟫ := by
    rw [show x-(a+R • n)=(x-a)-R • n by abel,norm_sub_sq_real]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hn,mul_one,real_inner_smul_right,
      real_inner_comm (x-a) n]
    ring
  have hout' : 2*R*⟪n,x-a⟫≤‖x-a‖^2 := by
    have hh := sq_le_sq₀ hR.le (norm_nonneg _) |>.mpr hout
    rw [he] at hh
    linarith
  exact quadratic_weight_scalar_outside hR (norm_nonneg _) hκ hsmall hst hout' hε

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_exp {f : Plane → ℝ} (hf : PlaneSmooth f) (τ : ℝ) (x : Plane) :
    gradient (fun y => Real.exp (τ*f y)) x=(τ*Real.exp (τ*f x)) • gradient f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  rw [(((hf.differentiable (by simp) x).hasFDerivAt.const_mul τ).exp).fderiv]
  simp only [smul_apply,smul_eq_mul]
  ring

lemma planeElliptic_mul {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f) (hg : PlaneSmooth g)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (x : Plane) :
    planeElliptic A (fun y => f y*g y) x=
      f x*planeElliptic A g x+g x*planeElliptic A f x+2*⟪gradient f x,A x (gradient g x)⟫ := by
  have hF := hA.clm_apply (plane_gradient_contDiff hf)
  have hG := hA.clm_apply (plane_gradient_contDiff hg)
  have he : (fun y => A y (gradient (fun z => f z*g z) y))=
      fun y => f y • A y (gradient g y)+g y • A y (gradient f y) := by
    funext y
    rw [plane_gradient_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
    simp only [map_add,map_smul]
  unfold planeElliptic
  rw [he]
  erw [planeDivergence_add ((hf.smul hG).differentiable (by simp) x)
      ((hg.smul hF).differentiable (by simp) x),
    planeDivergence_smul (hf.differentiable (by simp) x) (hG.differentiable (by simp) x),
    planeDivergence_smul (hg.differentiable (by simp) x) (hF.differentiable (by simp) x)]
  rw [hAs x (gradient g x) (gradient f x)]
  ring

lemma planeElliptic_exp {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f) (τ : ℝ) (x : Plane) :
    planeElliptic A (fun y => Real.exp (τ*f y)) x=
      Real.exp (τ*f x)*(τ*planeElliptic A f x+τ^2*planeEnergy A f x) := by
  have he : (fun y => A y (gradient (fun z => Real.exp (τ*f z)) y))=
      fun y => (τ*Real.exp (τ*f y)) • A y (gradient f y) := by
    funext y
    rw [plane_gradient_exp hf,map_smul]
  have hF := hA.clm_apply (plane_gradient_contDiff hf)
  have hk : PlaneSmooth (fun y => τ*Real.exp (τ*f y)) :=
    contDiff_const.mul ((contDiff_const.mul hf).exp)
  unfold planeElliptic
  rw [he]
  erw [planeDivergence_smul (hk.differentiable (by simp) x) (hF.differentiable (by simp) x)]
  rw [inner_gradient_left,fderiv_const_mul (((contDiff_const.mul hf).exp).differentiable (by simp) x)]
  rw [(((hf.differentiable (by simp) x).hasFDerivAt.const_mul τ).exp).fderiv]
  simp only [smul_apply,smul_eq_mul,← inner_gradient_left,planeEnergy]
  ring

theorem planeCarleman_conjugation {A : Plane → Plane →L[ℝ] Plane} {φ v : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : PlaneSmooth φ) (hv : PlaneSmooth v)
    (hAs : ∀ x w z,⟪w,A x z⟫=⟪z,A x w⟫) (τ : ℝ) (x : Plane) :
    planeCarlemanP A (fun y => A y (gradient φ y)) (planeEnergy A φ) τ
      (fun y => Real.exp (τ*φ y)*v y) x=Real.exp (τ*φ x)*planeElliptic A v x := by
  have he : PlaneSmooth (fun y => Real.exp (τ*φ y)) := (contDiff_const.mul hφ).exp
  unfold planeCarlemanP planeCarlemanS planeCarlemanT planeDrift
  rw [planeElliptic_mul hA he hv hAs,planeElliptic_exp hA hφ,plane_gradient_exp hφ,
    fderiv_fun_mul (he.differentiable (by simp) x) (hv.differentiable (by simp) x)]
  rw [(((hφ.differentiable (by simp) x).hasFDerivAt.const_mul τ).exp).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,← inner_gradient_left,real_inner_smul_left,
    planeEnergy,planeElliptic]
  rw [hAs x (gradient v x) (gradient φ x)]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_square_compact {u : Plane → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (fun x => u x^2) := hc.mono (by
  intro x hx hz
  exact hx (by simp [hz]))

theorem planeCarleman_weighted {A : Plane → Plane →L[ℝ] Plane} {φ v : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : PlaneSmooth φ) (hv : PlaneSmooth v)
    (hc : HasCompactSupport v) (hAs : ∀ x w z,⟪w,A x z⟫=⟪z,A x w⟫)
    {U : Set Plane} {C D Q c τ : ℝ} (hs : tsupport v⊆U)
    (hell : ∀ x∈U,∀ w,0≤⟪w,A x w⟫)
    (hdata : PlaneCarlemanData A (fun y => A y (gradient φ y)) (planeEnergy A φ) U C D Q c)
    (hτ : 1≤τ) (hbudget : D+(C+1)^2≤τ) :
    τ^3*(∫ x,(Real.exp (τ*φ x))^2*v x^2)≤
      ∫ x,(Real.exp (τ*φ x))^2*(planeElliptic A v x)^2 := by
  let u : Plane → ℝ := fun x => Real.exp (τ*φ x)*v x
  have hu : PlaneSmooth u := ((contDiff_const.mul hφ).exp).mul hv
  have huc : HasCompactSupport u := hc.mul_left
  have hus : tsupport u⊆tsupport v := tsupport_mul_subset_right
  have hb := hA.clm_apply (plane_gradient_contDiff hφ)
  have hq := planeEnergy_contDiff hA hφ
  have he := planeCarleman_coercive hA hb hq hu huc hAs (hus.trans hs) hdata hτ hbudget
  have hn (x : Plane) : 0≤planeEnergy A u x := by
    by_cases hx : x∈tsupport u
    · exact hell x (hs (hus hx)) (gradient u x)
    · have hg : gradient u x=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
      simp [planeEnergy,hg]
  have hi : Integrable (fun x => τ^3*u x^2) :=
    (((hu.continuous.pow 2).integrable_of_hasCompactSupport (plane_square_compact huc)).const_mul _)
  have hj : Integrable (fun x => τ*planeEnergy A u x+τ^3*u x^2) :=
    (((planeEnergy_contDiff hA hu).continuous.integrable_of_hasCompactSupport
      (planeEnergy_compact huc)).const_mul τ).add hi
  have hm := integral_mono hi hj (fun x => le_add_of_nonneg_left (mul_nonneg (by linarith) (hn x)))
  have ht := hm.trans he
  simp only [u,planeCarleman_conjugation hA hφ hv hAs,mul_pow] at ht
  rwa [integral_const_mul] at ht

theorem planeCarleman_vanish_above {A : Plane → Plane →L[ℝ] Plane} {φ v : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : PlaneSmooth φ) (hv : PlaneSmooth v)
    (hc : HasCompactSupport v) (hAs : ∀ x w z,⟪w,A x z⟫=⟪z,A x w⟫)
    {U : Set Plane} {C D Q c d : ℝ} (hs : tsupport v⊆U)
    (hell : ∀ x∈U,∀ w,0≤⟪w,A x w⟫)
    (hdata : PlaneCarlemanData A (fun y => A y (gradient φ y)) (planeEnergy A φ) U C D Q c)
    (hres : ∀ x,planeElliptic A v x≠0 → φ x≤d) :
    ∀ x,d<φ x → v x=0 := by
  let S : Set Plane := {x | d<φ x}
  have hSo : IsOpen S := isOpen_lt continuous_const hφ.continuous
  have hSm : MeasurableSet S := hSo.measurableSet
  have hvI : Integrable (fun x => v x^2) :=
    (hv.continuous.pow 2).integrable_of_hasCompactSupport (plane_square_compact hc)
  have hL := planeElliptic_contDiff hA hv
  have hLc := planeElliptic_compact (A := A) hc
  have hLI : Integrable (fun x => planeElliptic A v x^2) :=
    (hL.continuous.pow 2).integrable_of_hasCompactSupport (plane_square_compact hLc)
  let I : ℝ := ∫ x in S,v x^2
  let N : ℝ := ∫ x,planeElliptic A v x^2
  have hI : 0≤I := integral_nonneg (fun _ => sq_nonneg _)
  have hN : 0≤N := integral_nonneg (fun _ => sq_nonneg _)
  have hbound (τ : ℝ) (ht : 1≤τ) (hb : D+(C+1)^2≤τ) : τ^3*I≤N := by
    have ht0 : 0≤τ := by linarith
    let w : Plane → ℝ := fun x => (Real.exp (τ*φ x))^2
    let W : ℝ := (Real.exp (τ*d))^2
    have hW : 0<W := sq_pos_of_pos (Real.exp_pos _)
    have hw : Continuous w := (Real.continuous_exp.comp (continuous_const.mul hφ.continuous)).pow 2
    have hi : Integrable (fun x => w x*v x^2) :=
      (hw.mul (hv.continuous.pow 2)).integrable_of_hasCompactSupport
        (plane_square_compact hc).mul_left
    have hj : Integrable (fun x => w x*planeElliptic A v x^2) :=
      (hw.mul (hL.continuous.pow 2)).integrable_of_hasCompactSupport
        (plane_square_compact hLc).mul_left
    have hlo : W*I≤∫ x,w x*v x^2 := by
      rw [← integral_const_mul,← integral_indicator hSm]
      apply integral_mono ((hvI.const_mul W).indicator hSm) hi
      intro x
      by_cases hx : x∈S
      · rw [indicator_of_mem hx]
        apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (le_of_lt hx) ht0)) 2
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hhi : (∫ x,w x*planeElliptic A v x^2)≤W*N := by
      rw [← integral_const_mul]
      apply integral_mono hj (hLI.const_mul W)
      intro x
      by_cases hx : planeElliptic A v x=0
      · simp [hx]
      · apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hres x hx) ht0)) 2
    have hh := planeCarleman_weighted hA hφ hv hc hAs hs hell hdata ht hb
    have hmul := mul_le_mul_of_nonneg_left hlo (pow_nonneg ht0 3)
    have hf : W*(τ^3*I)≤W*N := by nlinarith only [hmul,hh,hhi]
    nlinarith only [hf,hW]
  have hIz : I=0 := by
    by_contra hz
    have hip : 0<I := lt_of_le_of_ne hI (Ne.symm hz)
    let τ := max 1 (max (D+(C+1)^2) (N/I+1))
    have ht : 1≤τ := le_max_left _ _
    have hb : D+(C+1)^2≤τ := (le_max_left _ _).trans (le_max_right _ _)
    have hlarge : N/I+1≤τ := (le_max_right _ _).trans (le_max_right _ _)
    have hτI : N<τ*I := by
      have hx := (div_lt_iff₀ hip).mp (show N/I<τ by linarith)
      linarith
    have hpow : τ≤τ^3 := by nlinarith [sq_nonneg (τ-1)]
    have hp := mul_le_mul_of_nonneg_right hpow hI
    linarith [hbound τ ht hb]
  have hae : (fun x => v x^2)=ᵐ[volume.restrict S] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun x => sq_nonneg (v x)))
      hvI.integrableOn).mp hIz
  have heq := Measure.eqOn_open_of_ae_eq hae hSo (hv.continuous.pow 2).continuousOn continuousOn_const
  intro x hx
  have hz := heq hx
  exact sq_eq_zero_iff.mp hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_eventuallyEq {f g : Plane → ℝ} {x : Plane}
    (h : f=ᶠ[𝓝 x] g) : gradient f=ᶠ[𝓝 x] gradient g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp only [gradient,hy]

lemma planeElliptic_congr_nhds {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    {x : Plane} (h : f=ᶠ[𝓝 x] g) : planeElliptic A f x=planeElliptic A g x := by
  have hg : (fun y => A y (gradient f y))=ᶠ[𝓝 x] (fun y => A y (gradient g y)) := by
    filter_upwards [plane_gradient_eventuallyEq h] with y hy
    rw [hy]
  simp only [planeElliptic,planeDivergence,hg.fderiv_eq]

lemma planeElliptic_zero_of_notMem_tsupport {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    {x : Plane} (hx : x∉tsupport f) : planeElliptic A f x=0 := by
  have he : f=ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [planeElliptic_congr_nhds he,planeElliptic_zero]

lemma planeElliptic_zero_on_open {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    {U : Set Plane} (hU : IsOpen U) (hz : ∀ x∈U,f x=0) {x : Plane} (hx : x∈U) :
    planeElliptic A f x=0 := by
  have he : f=ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hz y hy
  rw [planeElliptic_congr_nhds he,planeElliptic_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planeElliptic_continue_tangent_ball {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} (hU : IsOpen U) {a n : Plane} (ha : a∈U) (hn : ‖n‖=1)
    {ℓ R : ℝ} (hℓ : 0<ℓ) (hR : 0<R)
    (hell : ∀ v,ℓ*‖v‖^2≤⟪v,A a v⟫)
    (heq : ∀ x∈U,planeElliptic A f x=0)
    (hz : ∀ x∈Metric.ball (a+R • n) R,f x=0) :
    a∈interior {x | f x=0} := by
  obtain ⟨κ,hκ,r₀,hr₀,C,D,Q,c,hdata,hell'⟩ :=
    planeCarleman_weight_exists hA hAs a hn hℓ (show 0<4/R by positivity) hell
  obtain ⟨rU,hrU,hballU⟩ := Metric.isOpen_iff.mp hU a ha
  let r := min r₀ (min rU (1/(κ+1)))
  have hr : 0 < r := lt_min hr₀ (lt_min hrU (by positivity))
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrrU : r ≤ rU := (min_le_left _ _).trans' (min_le_right _ _)
  have hrrκ : r≤1/(κ+1) := (min_le_right _ _).trans (min_le_right _ _)
  let χ : ContDiffBump a := ⟨r/4,r/2,by positivity,by linarith⟩
  let v : Plane → ℝ := fun x => χ x*f x
  let φ := planeQuadraticWeight a n κ (4/R)
  let d := -(1/R)*(r/4)^2
  have hv : PlaneSmooth v := χ.contDiff.mul hf
  have hvc : HasCompactSupport v := χ.hasCompactSupport.mul_right
  have hvs : tsupport v⊆Metric.closedBall a (r/2) := by
    calc tsupport v ⊆ tsupport (χ : Plane → ℝ) := tsupport_mul_subset_left
         _ = _ := χ.tsupport_eq
  have hs₀ : tsupport v⊆Metric.ball a r₀ := by
    intro x hx
    have hh : dist x a ≤ r/2 := hvs hx
    change dist x a < r₀
    linarith
  have hsU : tsupport v⊆U := by
    intro x hx
    apply hballU
    have hh : dist x a ≤ r/2 := hvs hx
    change dist x a < rU
    linarith
  have hveq {x : Plane} (hx : x∈Metric.ball a (r/4)) : v=ᶠ[𝓝 x] f := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hx] with y hy
    change χ y*f y=f y
    simp only [hy,Pi.one_apply,one_mul]
  have hres (x : Plane) (hx : planeElliptic A v x≠0) : φ x≤d := by
    have hxs : x∈tsupport v := by
      by_contra h
      exact hx (planeElliptic_zero_of_notMem_tsupport h)
    have hsmall : κ*‖x-a‖≤1 := by
      have hdist : ‖x-a‖ ≤ r/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hvs hxs
      have hk : κ*r≤1 := by
        have hb := (le_div_iff₀ (show 0<κ+1 by positivity)).mp hrrκ
        nlinarith
      nlinarith
    have hout : R≤‖x-(a+R • n)‖ := by
      by_contra h
      have hxin : x∈Metric.ball (a+R • n) R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using (lt_of_not_ge h)
      apply hx
      apply planeElliptic_zero_on_open Metric.isOpen_ball (x := x) (hx := hxin)
      intro y hy
      dsimp [v]
      rw [hz y hy,mul_zero]
    have hfar : r/4≤‖x-a‖ := by
      by_contra h
      have hxin : x∈Metric.ball a (r/4) := by
        simpa only [Metric.mem_ball,dist_eq_norm] using (lt_of_not_ge h)
      exact hx ((planeElliptic_congr_nhds (hveq hxin)).trans (heq x (hsU hxs)))
    have hh := planeQuadraticWeight_outside hn hR hκ.le hsmall hout (le_refl (4/R))
    change φ x≤d
    apply hh.trans
    dsimp [d]
    have hsq : (r/4)^2≤‖x-a‖^2 := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hfar
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0≤1/R by positivity)]
  have hvan := planeCarleman_vanish_above hA (planeQuadraticWeight_smooth _ _ _ _)
    hv hvc hAs hs₀ (fun x hx w => (by positivity : 0≤(ℓ/2)*‖w‖^2).trans (hell' x hx w))
    hdata hres
  have hd : d<φ a := by
    dsimp [φ,planeQuadraticWeight,d]
    simp only [sub_self,inner_zero_right,zero_pow (by decide : 2≠0),mul_zero,norm_zero,
      zero_add]
    have hp : 0<(1/R)*(r/4)^2 := by positivity
    linarith
  have ho : IsOpen {x : Plane | d<φ x} :=
    isOpen_lt continuous_const (planeQuadraticWeight_smooth _ _ _ _).continuous
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (inter_mem (ho.mem_nhds hd)
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (show 0 < r/4 by positivity))))
  intro x hx
  have hvz := hvan x hx.1
  have he := Filter.EventuallyEq.eq_of_nhds (hveq hx.2)
  exact he.symm.trans hvz

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CMCFrameOperator
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

theorem plane_interior_ball_at_frontier {D : Set Plane} (hD : IsOpen D)
    {a : Plane} (ha : a∈frontier D) {ε : ℝ} (hε : 0<ε) :
    ∃ (c y : Plane) (R : ℝ),0<R ∧
      Metric.ball c R⊆D ∧ ‖y-c‖=R ∧ y∈frontier D ∧
      Metric.closedBall c R⊆Metric.ball a ε := by
  have hac : a∈closure D := frontier_subset_closure ha
  have had : a∉D := by
    rw [frontier, hD.interior_eq] at ha
    exact ha.2
  obtain ⟨c,hcD,hca⟩ := Metric.mem_closure_iff.mp hac (ε/4) (by positivity)
  have hcomp : Dᶜ.Nonempty := ⟨a,had⟩
  let R := Metric.infDist c Dᶜ
  have hR : 0<R := (hD.isClosed_compl.notMem_iff_infDist_pos hcomp).mp (by simpa using hcD)
  have hRa : R≤dist c a := Metric.infDist_le_dist_of_mem had
  obtain ⟨y,hyc,hRy⟩ := hD.isClosed_compl.exists_infDist_eq_dist hcomp c
  have hball : Metric.ball c R⊆D := Metric.ball_infDist_compl_subset
  have hyR : ‖y-c‖=R := by
    rw [← dist_eq_norm,dist_comm]
    exact hRy.symm
  have hycl : y∈closure D := by
    apply closure_mono hball
    rw [closure_ball c hR.ne']
    simpa only [Metric.mem_closedBall,dist_eq_norm,hyR] using (le_refl R)
  refine ⟨c,y,R,hR,hball,hyR,?_,?_⟩
  · rw [frontier,hD.interior_eq]
    exact ⟨hycl,hyc⟩
  · intro z hz
    have hzR : dist z c≤R := hz
    have hca' : dist c a<ε/4 := by simpa only [dist_comm] using hca
    have hza := dist_triangle z c a
    change dist z a<ε
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeElliptic_continue_ball {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} (hU : IsOpen U) {a c : Plane} (ha : a∈U)
    {ℓ R : ℝ} (hℓ : 0<ℓ) (hR : 0<R) (hd : ‖a-c‖=R)
    (hell : ∀ v,ℓ*‖v‖^2≤⟪v,A a v⟫)
    (heq : ∀ x∈U,planeElliptic A f x=0)
    (hz : ∀ x∈Metric.ball c R,f x=0) :
    a∈interior {x | f x=0} := by
  let n : Plane := (1/R) • (c-a)
  have hn : ‖n‖=1 := by
    dsimp [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (show 0<1/R by positivity),norm_sub_rev,hd]
    exact one_div_mul_cancel hR.ne'
  have hc : a+R • n=c := by
    dsimp [n]
    rw [smul_smul,mul_one_div_cancel hR.ne',one_smul]
    abel
  exact planeElliptic_continue_tangent_ball hA hf hAs hU ha hn hℓ hR hell heq (by simpa [hc] using hz)

theorem planeElliptic_unique_continuation {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hell : ∀ x∈U,∃ ℓ>0,∀ v,ℓ*‖v‖^2≤⟪v,A x v⟫)
    (heq : ∀ x∈U,planeElliptic A f x=0)
    (hpatch : (U∩interior {x | f x=0}).Nonempty) :
    ∀ x∈U,f x=0 := by
  let D := interior {x | f x=0}
  have hD : IsOpen D := isOpen_interior
  have hno : Disjoint (frontier D) U := by
    rw [Set.disjoint_left]
    intro a ha haU
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU a haU
    obtain ⟨c,y,R,hR,hball,hyR,hyD,hsub⟩ := plane_interior_ball_at_frontier hD ha hε
    have hyU : y∈U := hεU (hsub (by
      simpa only [Metric.mem_closedBall,dist_eq_norm,hyR] using (le_refl R)))
    obtain ⟨ℓ,hℓ,hell⟩ := hell y hyU
    have hyz := planeElliptic_continue_ball hA hf hAs hU hyU hℓ hR hyR hell heq
      (fun x hx => show x∈{y | f y=0} from interior_subset (hball hx))
    have hyn : y∉D := by
      rw [frontier,hD.interior_eq] at hyD
      exact hyD.2
    exact hyn hyz
  have hsub : U⊆D := hUc.subset_of_closure_inter_subset hD hpatch (by
    intro x hx
    by_contra hn
    apply Set.disjoint_left.mp hno ?_ hx.2
    rw [frontier,hD.interior_eq]
    exact ⟨hx.1,hn⟩)
  exact fun x hx => show x∈{y | f y=0} from interior_subset (hsub hx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcJacobian_strict_coercive (p v : Plane) :
    (1/(cmcWeight p)^3)*‖v‖^2≤⟪v,cmcJacobian p v⟫ := by
  rw [cmcJacobian_self]
  have hp := cmcWeight_pos p
  have hw := cmcWeight_sq p
  have hcs := real_inner_mul_inner_self_le p v
  simp only [real_inner_self_eq_norm_sq] at hcs
  rw [one_div_mul_eq_div,div_le_div_iff_of_pos_right (by positivity : 0<(cmcWeight p)^3)]
  nlinarith

theorem LinearCMCEquation.unique_continuation {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hw : LinearCMCEquation u (gradient g) (fun _ => 0) U)
    (hpatch : (U∩interior {x | u x=0}).Nonempty) : ∀ x∈U,u x=0 := by
  exact planeElliptic_unique_continuation (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)) hu
    (fun x v w => (cmcJacobian_symmetric _ _ _).trans (real_inner_comm _ _)) hU hUc
    (fun x _ => ⟨1/(cmcWeight (gradient g x))^3,by have hh := cmcWeight_pos (gradient g x); positivity,cmcJacobian_strict_coercive _⟩)
    (hw.classical_zero hg hu hU) hpatch

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.affine_zero {u v : Plane → ℝ} {p : Plane → Plane}
    {U : Set Plane} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hp : Continuous p)
    (hue : LinearCMCEquation u p (fun _ => 0) U)
    (hve : LinearCMCEquation v p (fun _ => 0) U) (c a b : ℝ) :
    LinearCMCEquation (fun y => c+a*u y+b*v y) p (fun _ => 0) U := by
  have hg (y : Plane) : gradient (fun z => c+a*u z+b*v z) y=
      a • gradient u y+b • gradient v y := by
    have hd := ((hasFDerivAt_const c y).add
      ((hu.differentiable (by simp) y).hasFDerivAt.const_mul a)).add
        ((hv.differentiable (by simp) y).hasFDerivAt.const_mul b)
    have he : fderiv ℝ (fun z => c+a*u z+b*v z) y=
        0+a • fderiv ℝ u y+b • fderiv ℝ v y := hd.fderiv
    simp only [gradient,he,zero_add,map_add,map_smul]
  intro ψ hψ hc hs
  have hi (w : Plane → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
      Integrable (fun y => fderiv ℝ ψ y (cmcJacobian (p y) (gradient w y))) := by
    apply ((hψ.continuous_fderiv (by simp)).clm_apply
      ((cmcJacobian_contDiff.continuous.comp hp).clm_apply
        (plane_gradient_contDiff hw).continuous)).integrable_of_hasCompactSupport
    apply (hc.fderiv ℝ).mono
    intro y hy hz
    exact hy (by simp only [hz,zero_apply])
  simp_rw [hg,sub_zero,map_add,map_smul,smul_eq_mul]
  rw [integral_add ((hi u hu).const_mul a) ((hi v hv).const_mul b),
    integral_const_mul,integral_const_mul]
  have hu0 := hue ψ hψ hc hs
  have hv0 := hve ψ hψ hc hs
  simp only [sub_zero] at hu0 hv0
  rw [hu0,hv0,mul_zero,mul_zero,add_zero]

lemma normalTranslationNumerator_contDiff (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Cover) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalTranslationNumerator n g v σ) :=
  contDiff_const.mul (contDiff_const.sub (contDiff_const.inner ℝ (plane_gradient_contDiff hg)))

lemma normalTranslationNumerator_eq (n : Cover) (g : Plane → ℝ) (v : Cover) (σ : ℝ)
    (y : Plane) : normalTranslationNumerator n g v σ y=
      σ*⟪v,n⟫+(-σ*(normalPlaneCoordinates n v) 0)*
        fderiv ℝ g y (EuclideanSpace.single 0 1)+
      (-σ*(normalPlaneCoordinates n v) 1)*fderiv ℝ g y (EuclideanSpace.single 1 1) := by
  simp only [normalTranslationNumerator,plane_inner_components,plane_gradient_component]
  ring

lemma normalTranslationNumerator_linear (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Cover) (σ : ℝ) {U : Set Plane}
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ => 0) U) :
    LinearCMCEquation (normalTranslationNumerator n g v σ) (gradient g) (fun _ => 0) U := by
  simp_rw [show normalTranslationNumerator n g v σ = fun y =>
    σ*⟪v,n⟫+(-σ*(normalPlaneCoordinates n v) 0)*
      fderiv ℝ g y (EuclideanSpace.single 0 1)+
    (-σ*(normalPlaneCoordinates n v) 1)*fderiv ℝ g y (EuclideanSpace.single 1 1)
      from funext (normalTranslationNumerator_eq n g v σ)]
  exact (hlin 0).affine_zero
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const)
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const)
    (plane_gradient_contDiff hg).continuous (hlin 1) _ _ _

lemma normalTranslationNumerator_weight {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (v : Cover) (σ : ℝ) (y : Plane) :
    normalTranslationNumerator n g v σ y=
      cmcWeight (gradient g y)*⟪v,σ • graphSlopeNormal n (gradient g y)⟫ := by
  rw [graphSlopeNormal_weight hn]
  simp only [normalTranslationNumerator,inner_smul_right,inner_sub_right]
  have he : ⟪normalPlaneCoordinates n v,gradient g y⟫=
      ⟪v,normalPlaneEmbedding n (gradient g y)⟫ :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  rw [he]
  field_simp [(cmcWeight_pos (gradient g y)).ne']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotient_graph_closure {S D : Set Torus} (hDS : D⊆S)
    {x : Cover} {G : Plane → Cover} {P : Cover →L[ℝ] Plane}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v)
    (hx : quotientMap x∈closure D) :
    (0 : Plane)∈closure ((fun y => quotientMap (x+G y)) ⁻¹' D) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hP : ∀ᶠ v in 𝓝 (0 : Cover),P v∈Metric.ball (0 : Plane) ε := by
    have ht : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
      simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
    exact ht.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hcover.and hP)
  obtain ⟨a,haD,hax⟩ := Metric.mem_closure_iff.mp hx δ hδ
  have ha : a∈Metric.ball (quotientMap x) δ := by
    simpa only [Metric.mem_ball,dist_comm] using hax
  rw [← quotientMap_image_ball x δ] at ha
  obtain ⟨z,hzx,hza⟩ := ha
  have hz : z-x∈Metric.ball (0 : Cover) δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hzx
  obtain ⟨hi,hp⟩ := hsub hz
  have hzs : quotientMap (x+(z-x))∈S := by
    simpa only [add_sub_cancel,hza] using hDS haD
  refine ⟨P (z-x),?_,?_⟩
  · change quotientMap (x+G (P (z-x)))∈D
    rw [hi hzs,add_sub_cancel,hza]
    exact haD
  · simpa only [Metric.mem_ball,dist_comm] using hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma relativeZeroNeighborhood_zero {S : Set Torus} {F : Torus → ℝ} {a : Torus}
    (ha : a∈S) (hz : a∈relativeZeroNeighborhood S F) : F a=0 := by
  have h : a∈Sᶜ∪{a | F a=0} := interior_subset hz
  exact h.resolve_left (fun hn => hn ha)

lemma quotient_graph_zero_germ {S : Set Torus} {F : Torus → ℝ}
    {x : Cover} {G : Plane → Cover} {P : Cover →L[ℝ] Plane}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v)
    (hz : ∀ᶠ y in 𝓝 (0 : Plane),F (quotientMap (x+G y))=0) :
    quotientMap x∈relativeZeroNeighborhood S F := by
  have hP : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
  have hev : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → F (quotientMap (x+v))=0 := by
    filter_upwards [hcover,hP.eventually hz] with v hv hvz hS
    rwa [hv hS] at hvz
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  change quotientMap x∈interior (Sᶜ∪{a | F a=0})
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (quotientMap x) hδ)
  intro a ha
  by_cases haS : a∈S
  · right
    rw [← quotientMap_image_ball x δ] at ha
    obtain ⟨z,hz,hza⟩ := ha
    have hz' : z-x∈Metric.ball (0 : Cover) δ := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hz
    have hh := hball hz'
    change F a=0
    simpa only [add_sub_cancel,hza] using hh (by simpa only [add_sub_cancel,hza] using haS)
  · exact Or.inl haS

lemma preconnected_zero_of_closed_germ {S : Set Torus} {F : Torus → ℝ}
    (hS : IsPreconnected S) (hD : IsClosed (S∩relativeZeroNeighborhood S F))
    (hpatch : (S∩relativeZeroNeighborhood S F).Nonempty) : ∀ a∈S,F a=0 := by
  let Z := relativeZeroNeighborhood S F
  have hZ : IsOpen Z := isOpen_interior
  have hsub : S⊆Z := by
    intro a ha
    by_contra hn
    have hcover : S⊆Z∪(S∩Z)ᶜ := by
      intro b hb
      by_cases hz : b∈Z
      · exact Or.inl hz
      · exact Or.inr (fun hd => hz hd.2)
    obtain ⟨b,hbS,hbZ,hbn⟩ := hS Z (S∩Z)ᶜ hZ hD.isOpen_compl hcover hpatch
      ⟨a,ha,fun hd => hn hd.2⟩
    exact hbn ⟨hbS,hbZ⟩
  exact fun a ha => relativeZeroNeighborhood_zero ha (hsub ha)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_zero_germs_closed {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover) :
    IsClosed (frontier (openRepresentative E)∩relativeZeroNeighborhood
      (frontier (openRepresentative E)) (fun a => ⟪v,N (representative a)⟫)) := by
  let S := frontier (openRepresentative E)
  let F : Torus → ℝ := fun a => ⟪v,N (representative a)⟫
  let Z := relativeZeroNeighborhood S F
  let D := S∩Z
  have hD : D⊆S := inter_subset_left
  apply isClosed_of_closure_subset
  intro a ha
  have haS : a∈S := closure_minimal hD isClosed_frontier ha
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hx : quotientMap x∈S := by rwa [hxa]
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hm,hcover,r,hr,hgrad,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmin hμ hN hp hae x hx
  let G := normalGraph n g
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry n).contDiff.add (hg.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  obtain ⟨ρ,hρ,hρm⟩ := Metric.mem_nhds_iff.mp hm
  let ε := min r ρ
  have hε : 0<ε := lt_min hr hρ
  have hεr : ε ≤ r := min_le_left _ _
  have hερ : ε≤ρ := min_le_right _ _
  have hb (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      N (x+G y)=σ • graphSlopeNormal n (gradient g y) ∧ φ y∈S :=
    hρm (Metric.ball_subset_ball hερ hy)
  let w := normalTranslationNumerator n g v σ
  have hw : PlaneSmooth w := normalTranslationNumerator_contDiff n hg v σ
  have hws (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      w y=cmcWeight (gradient g y)*F (φ y) := by
    change w y=cmcWeight (gradient g y)*⟪v,N (representative (φ y))⟫
    rw [show N (representative (φ y))=N (x+G y) from periodic_representative hp _,(hb y hy).1]
    exact normalTranslationNumerator_weight hn g v σ y
  have hc : (0 : Plane)∈closure (φ ⁻¹' D) := quotient_graph_closure hD
    (hcover.mono fun z hz => hz.mp) (by rwa [hxa])
  obtain ⟨y,hyD,hyd⟩ := Metric.mem_closure_iff.mp hc ε hε
  have hyb : y∈Metric.ball (0 : Plane) ε := by
    simpa only [Metric.mem_ball,dist_comm] using hyd
  have hO : IsOpen (φ ⁻¹' Z∩Metric.ball 0 ε) :=
    (isOpen_interior.preimage hφ).inter Metric.isOpen_ball
  have hyO : y∈φ ⁻¹' Z∩Metric.ball 0 ε := ⟨hyD.2,hyb⟩
  have hzeroO : φ ⁻¹' Z∩Metric.ball 0 ε⊆{z | w z=0} := by
    intro z hz
    change w z=0
    rw [hws z hz.2,relativeZeroNeighborhood_zero (hb z hz.2).2 hz.1,mul_zero]
  have hpatch : (Metric.ball (0 : Plane) ε∩interior {z | w z=0}).Nonempty :=
    ⟨y,hyb,(hO.subset_interior_iff.mpr hzeroO) hyO⟩
  have hvan := (normalTranslationNumerator_linear n hg v σ hlin |>.mono
    (Metric.ball_subset_ball hεr)).unique_continuation hg hw Metric.isOpen_ball
      (convex_ball (0 : Plane) ε).isPreconnected hpatch
  refine ⟨haS,?_⟩
  rw [← hxa]
  apply quotient_graph_zero_germ (hcover.mono fun z hz => hz.mp)
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hε] with y hy
  have hz := hvan y hy
  rw [hws y hy] at hz
  exact (mul_eq_zero.mp hz).resolve_left (cmcWeight_pos _).ne'

theorem isMinimizerAt_normal_unique_continuation {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover)
    {U : Set Torus} (hU : IsOpen U) (hpatch : (frontier (openRepresentative E)∩U).Nonempty)
    (hz : ∀ a∈frontier (openRepresentative E)∩U,⟪v,N (representative a)⟫=0) :
    ∀ a∈frontier (openRepresentative E),⟪v,N (representative a)⟫=0 := by
  apply preconnected_zero_of_closed_germ hS
    (isMinimizerAt_normal_zero_germs_closed hV hE hmin hμ hN hp hae v)
  obtain ⟨a,haS,haU⟩ := hpatch
  refine ⟨a,haS,?_⟩
  apply hU.subset_interior_iff.mpr ?_ haU
  intro b hb
  by_cases hbs : b∈frontier (openRepresentative E)
  · exact Or.inr (hz b ⟨hbs,hb⟩)
  · exact Or.inl hbs

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CMCSecantSymbol
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

theorem isMinimizerAt_no_constant_normal_patch {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {U : Set Torus} (hU : IsOpen U) (hpatch : (frontier (openRepresentative E)∩U).Nonempty)
    (n : Cover) (hconst : ∀ a∈frontier (openRepresentative E)∩U,N (representative a)=n) : False := by
  have hunit (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) : ‖N x‖=1 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hN.continuous.norm continuous_const
      (fun k y => by rw [hp]) (fun _ _ => rfl) _ x hx
    filter_upwards [hae] with z hz
    rw [hz,z.2.property]
  obtain ⟨a,ha,haU⟩ := hpatch
  have hna := hconst a ⟨ha,haU⟩
  have hn : ‖n‖=1 := by
    rw [← hna]
    exact hunit (representative a) (by simpa only [quotientMap_representative] using ha)
  have hpar (b : Torus) (hb : b∈frontier (openRepresentative E)) :
      N (representative b)=n ∨ N (representative b)= -n := by
    let m := N (representative b)
    let d := ⟪n,m⟫
    let v := m-d • n
    have hvn : ⟪v,n⟫=0 := by
      simp only [v,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
      rw [real_inner_comm n m]
      exact sub_self _
    have hvm := isMinimizerAt_normal_unique_continuation hV hE hmin hconn hμ hN hp hae v
      hU ⟨a,ha,haU⟩ (fun c hc => by rw [hconst c hc,hvn]) b hb
    have hm : ‖m‖=1 := hunit (representative b) (by simpa only [quotientMap_representative] using hb)
    have hd : d^2=1 := by
      change ⟪m-d • n,m⟫=0 at hvm
      rw [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hm,one_pow] at hvm
      change 1-d*d=0 at hvm
      nlinarith
    have hdor : d=1 ∨ d= -1 := by
      have he : (d-1)*(d+1)=0 := by nlinarith
      rcases mul_eq_zero.mp he with h|h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hdor with hd1|hd1
    · left
      have hs : ‖m-n‖^2=0 := by
        rw [norm_sub_sq_real,hm,hn,real_inner_comm n m]
        change 1^2-2*d+1^2=0
        rw [hd1]; norm_num
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
    · right
      have hs : ‖m+n‖^2=0 := by
        rw [norm_add_sq_real,hm,hn,real_inner_comm n m]
        change 1^2+2*d+1^2=0
        rw [hd1]; norm_num
      exact eq_neg_iff_add_eq_zero.mpr (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
  have hc (b : Torus) (hb : b∈frontier (openRepresentative E)) : N (representative b)=n := by
    have hm : MapsTo (fun b : Torus => N (representative b)) (frontier (openRepresentative E))
        ({n,-n} : Set Cover) := by
      intro c hc
      simpa only [mem_insert_iff,mem_singleton_iff] using hpar c hc
    exact (hconn.constant_of_mapsTo (Set.toFinite ({n,-n} : Set Cover)).isDiscrete
      (continuous_periodic_descent hN.continuous hp).continuousOn hm hb ha).trans hna
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hac : ∀ᵐ z ∂(μ : Measure NormalBundle),(z.2 : Cover)=n := by
    filter_upwards [hbd,hae] with z hz he
    have hh := hc (quotientMap z.1) hz
    rw [periodic_representative hp] at hh
    exact he.symm.trans hh
  have hmpos : 0<(μ : Measure NormalBundle).real univ := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal,hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne
  have hf : AdmissibleField (fun _ : Cover => n) := ⟨contDiff_const,fun _ _ => rfl,fun _ => hn.le⟩
  have hflux := hμ.2 _ hf
  have hi : (∫ z,normalTest (fun _ : Cover => n) hf.1.continuous z ∂(μ : Measure NormalBundle))=
      (μ : Measure NormalBundle).real univ := by
    calc
      _=(∫ _ : NormalBundle,(1 : ℝ) ∂(μ : Measure NormalBundle)) := by
        apply integral_congr_ae
        filter_upwards [hac] with z hz
        simp only [normalTest,ContinuousMap.coe_mk,hz,real_inner_self_eq_norm_sq,hn,one_pow]
      _=_ := by simp
  have hd : divergence (fun _ : Cover => n)=fun _ => 0 := by funext x; simp [divergence]
  rw [hi,hd,integral_zero] at hflux
  exact hmpos.ne' hflux

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcSecant_apply (p q v : Plane) :
    cmcSecant p q v=((cmcWeight p+cmcWeight q)/(2*cmcWeight p*cmcWeight q)) • v -
      (⟪p+q,v⟫/(2*cmcWeight p*cmcWeight q*(cmcWeight p+cmcWeight q))) • (p+q) := by
  simp only [cmcSecant,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul,one_div_mul_eq_div]

lemma cmcSecant_exact (p q : Plane) : cmcSecant p q (q-p)=cmcFlux q-cmcFlux p := by
  have hp := cmcWeight_pos p
  have hq := cmcWeight_pos q
  have hs : cmcWeight p+cmcWeight q≠0 := ne_of_gt (add_pos hp hq)
  have he : ⟪p+q,q-p⟫=(cmcWeight q)^2-(cmcWeight p)^2 := by
    rw [inner_add_left,inner_sub_right,inner_sub_right,real_inner_comm p q,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,cmcWeight_sq,cmcWeight_sq]
    ring
  rw [cmcSecant_apply,he]
  apply PiLp.ext
  intro i
  simp only [cmcFlux,cmcWeight,PiLp.smul_apply,PiLp.sub_apply,PiLp.add_apply,smul_eq_mul]
  field_simp
  ring

lemma cmcSecant_symmetric (p q v w : Plane) : ⟪v,cmcSecant p q w⟫=⟪w,cmcSecant p q v⟫ := by
  simp only [cmcSecant_apply,inner_sub_right,real_inner_smul_right,real_inner_comm v (p+q),
    real_inner_comm w (p+q),real_inner_comm w v]
  ring

lemma cmcWeight_gt_norm (p : Plane) : ‖p‖ < cmcWeight p := by
  have hp := cmcWeight_pos p
  have he := cmcWeight_sq p
  nlinarith [norm_nonneg p]

lemma cmcSecant_elliptic (p q : Plane) : ∃ ℓ>0,∀ v,ℓ*‖v‖^2≤⟪v,cmcSecant p q v⟫ := by
  let S := cmcWeight p+cmcWeight q
  let D := 2*cmcWeight p*cmcWeight q*S
  have hS : 0<S := add_pos (cmcWeight_pos p) (cmcWeight_pos q)
  have hD : 0<D := by dsimp [D]; have hp := cmcWeight_pos p; have hq := cmcWeight_pos q; positivity
  have hnorm : ‖p+q‖<S := (norm_add_le p q).trans_lt (add_lt_add (cmcWeight_gt_norm p) (cmcWeight_gt_norm q))
  have hn : 0<S^2-‖p+q‖^2 := by nlinarith [norm_nonneg (p+q)]
  refine ⟨(S^2-‖p+q‖^2)/D,div_pos hn hD,?_⟩
  intro v
  have hcs := real_inner_mul_inner_self_le (p+q) v
  simp only [real_inner_self_eq_norm_sq] at hcs
  rw [cmcSecant_apply,inner_sub_right,real_inner_smul_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm v (p+q)]
  have he : (cmcWeight p+cmcWeight q)/(2*cmcWeight p*cmcWeight q)=S^2/D := by
    dsimp [S,D]
    field_simp
  change (S^2-‖p+q‖^2)/D*‖v‖^2≤_
  rw [he]
  rw [real_inner_comm (p+q) v]
  change (S^2-‖p+q‖^2)/D*‖v‖^2≤S^2/D*‖v‖^2-⟪p+q,v⟫/D*⟪p+q,v⟫
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div,div_mul_eq_mul_div,← sub_div,
    div_le_div_iff_of_pos_right hD]
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_sub {f g : Plane → ℝ} (hf : PlaneSmooth f) (hg : PlaneSmooth g) (x : Plane) :
    gradient (fun y => g y-f y) x=gradient g x-gradient f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,inner_sub_left,inner_gradient_left,inner_gradient_left,
    fderiv_fun_sub (hg.differentiable (by simp) x) (hf.differentiable (by simp) x)]
  rfl

lemma cmcSecant_comp_contDiff {p q : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => cmcSecant (p x) (q x)) := by
  have hw₁ : ContDiff ℝ (⊤ : ℕ∞) (fun x => cmcWeight (p x)) := cmcWeight_contDiff.comp hp
  have hw₂ : ContDiff ℝ (⊤ : ℕ∞) (fun x => cmcWeight (q x)) := cmcWeight_contDiff.comp hq
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => 2*cmcWeight (p x)*cmcWeight (q x)) :=
    (contDiff_const.mul hw₁).mul hw₂
  have hn (x : Plane) : 2*cmcWeight (p x)*cmcWeight (q x)≠0 := by
    have hh := cmcWeight_pos (p x); have hk := cmcWeight_pos (q x); positivity
  have hs (x : Plane) : cmcWeight (p x)+cmcWeight (q x)≠0 :=
    ne_of_gt (add_pos (cmcWeight_pos _) (cmcWeight_pos _))
  unfold cmcSecant
  apply ((hw₁.add hw₂).div hd hn).smul contDiff_const |>.sub
  exact (contDiff_const.div (hd.mul (hw₁.add hw₂)) (fun x => mul_ne_zero (hn x) (hs x))).smul
    (((innerSL ℝ : Plane →L[ℝ] Plane →L[ℝ] ℝ).contDiff.comp (hp.add hq)).smulRight (hp.add hq))

lemma cmcSecant_graph_contDiff {f g : Plane → ℝ} (hf : PlaneSmooth f) (hg : PlaneSmooth g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => cmcSecant (gradient f x) (gradient g x)) := by
  exact cmcSecant_comp_contDiff (plane_gradient_contDiff hf) (plane_gradient_contDiff hg)

lemma cmcSecant_graph_flux {f g : Plane → ℝ} (hf : PlaneSmooth f) (hg : PlaneSmooth g) :
    (fun y => cmcSecant (gradient f y) (gradient g y) (gradient (fun z => g z-f z) y))=
      fun y => cmcFlux (gradient g y)-cmcFlux (gradient f y) := by
  funext y
  rw [plane_gradient_sub hf hg]
  exact cmcSecant_exact _ _

lemma cmcSecant_graph_divergence {f g : Plane → ℝ} (hf : PlaneSmooth f) (hg : PlaneSmooth g) (x : Plane) :
    planeElliptic (fun y => cmcSecant (gradient f y) (gradient g y)) (fun y => g y-f y) x=
      planeDivergence (fun y => cmcFlux (gradient g y)) x-
        planeDivergence (fun y => cmcFlux (gradient f y)) x := by
  unfold planeElliptic
  rw [cmcSecant_graph_flux hf hg]
  exact planeDivergence_sub (cmcFlux_contDiff.comp (plane_gradient_contDiff hg))
    (cmcFlux_contDiff.comp (plane_gradient_contDiff hf)) x

theorem cmcGraph_unique_continuation {f g : Plane → ℝ}
    (hf : PlaneSmooth f) (hg : PlaneSmooth g)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsPreconnected U)
    (heq : ∀ x∈U,planeDivergence (fun y => cmcFlux (gradient f y)) x=
      planeDivergence (fun y => cmcFlux (gradient g y)) x)
    (hpatch : (U∩interior {x | f x=g x}).Nonempty) : ∀ x∈U,f x=g x := by
  have hzero : ∀ x∈U,planeElliptic (fun y => cmcSecant (gradient f y) (gradient g y))
      (fun y => g y-f y) x=0 := by
    intro x hx
    rw [cmcSecant_graph_divergence hf hg,heq x hx,sub_self]
  have hzset : {x | f x=g x}={x | g x-f x=0} := by ext x; simp [sub_eq_zero,eq_comm]
  rw [hzset] at hpatch
  have hs : ∀ x v w,⟪v,cmcSecant (gradient f x) (gradient g x) w⟫=
      ⟪w,cmcSecant (gradient f x) (gradient g x) v⟫ := fun x v w => cmcSecant_symmetric _ _ v w
  have hell : ∀ x∈U,∃ ℓ>0,∀ v,ℓ*‖v‖^2≤⟪v,cmcSecant (gradient f x) (gradient g x) v⟫ :=
    fun x _ => cmcSecant_elliptic _ _
  have hh := planeElliptic_unique_continuation (cmcSecant_graph_contDiff hf hg) (hg.sub hf)
    hs hU hUc hell hzero hpatch
  exact fun x hx => (sub_eq_zero.mp (hh x hx)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_zero {n : Cover} {f : Plane → ℝ} (hf0 : f 0=0) :
    normalGraph n f 0=0 := by
  change (normalPlaneLinearIsometry n) 0+f 0 • n=0
  simp [hf0]

lemma normalGraph_tendsto_zero {n : Cover} {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0=0) :
    Tendsto (normalGraph n f) (𝓝 (0 : Plane)) (𝓝 (0 : Cover)) := by
  have hc : Continuous (normalGraph n f) :=
    (normalPlaneLinearIsometry n).continuous.add (hf.continuous.smul continuous_const)
  simpa only [normalGraph_zero hf0] using hc.continuousAt.tendsto (x := 0)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma relativeContainmentNeighborhood_mem {S T : Set Torus} {a : Torus}
    (ha : a∈S) (hz : a∈relativeContainmentNeighborhood S T) : a∈T :=
  (interior_subset hz).resolve_left (fun hn => hn ha)

lemma quotient_graph_containment_germ {S T : Set Torus}
    {x : Cover} {G : Plane → Cover} {P : Cover →L[ℝ] Plane}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v)
    (hz : ∀ᶠ y in 𝓝 (0 : Plane),quotientMap (x+G y)∈T) :
    quotientMap x∈relativeContainmentNeighborhood S T := by
  have hP : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
  have hev : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → quotientMap (x+v)∈T := by
    filter_upwards [hcover,hP.eventually hz] with v hv hvz hS
    rwa [hv hS] at hvz
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (quotientMap x) hδ)
  intro a ha
  by_cases haS : a∈S
  · right
    rw [← quotientMap_image_ball x δ] at ha
    obtain ⟨z,hz,hza⟩ := ha
    have hz' : z-x∈Metric.ball (0 : Cover) δ := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hz
    simpa only [add_sub_cancel,hza] using hball hz' (by simpa only [add_sub_cancel,hza] using haS)
  · exact Or.inl haS

lemma preconnected_subset_of_closed_germ {S T : Set Torus}
    (hS : IsPreconnected S) (hD : IsClosed (S∩relativeContainmentNeighborhood S T))
    (hpatch : (S∩relativeContainmentNeighborhood S T).Nonempty) : S⊆T := by
  let Z := relativeContainmentNeighborhood S T
  have hZ : IsOpen Z := isOpen_interior
  have hsub : S⊆Z := by
    intro a ha
    by_contra hn
    have hcover : S⊆Z∪(S∩Z)ᶜ := by
      intro b hb
      by_cases hz : b∈Z
      · exact Or.inl hz
      · exact Or.inr (fun hd => hz hd.2)
    obtain ⟨b,hbS,hbZ,hbn⟩ := hS Z (S∩Z)ᶜ hZ hD.isOpen_compl hcover hpatch
      ⟨a,ha,fun hd => hn hd.2⟩
    exact hbn ⟨hbS,hbZ⟩
  exact fun a ha => relativeContainmentNeighborhood_mem ha (hsub ha)

lemma normalGraph_eq_height {n : Cover} (hn : ‖n‖=1) {f g : Plane → ℝ} {y : Plane}
    (he : normalGraph n f y=normalGraph n g y) : f y=g y := by
  simpa only [normalGraph_inner hn] using congrArg (fun v : Cover => ⟪n,v⟫) he

lemma normalGraph_boundary_height {n x : Cover} (hn : ‖n‖=1) {f g : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0=0) {S : Set Torus}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S ↔
      normalGraph n g (normalPlaneCoordinates n v)=v) :
    ∀ᶠ y in 𝓝 (0 : Plane),quotientMap (x+normalGraph n f y)∈S ↔ f y=g y := by
  filter_upwards [(normalGraph_tendsto_zero hf hf0).eventually hcover] with y hy
  rw [normalPlaneCoordinates_graph hn] at hy
  refine hy.trans ⟨fun h => (normalGraph_eq_height hn h).symm,?_⟩
  intro he
  simp only [normalGraph,he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem OrientedCMCCharts.containment_germs_closed
    {S T : Set Torus} (hS : IsClosed S) (hT : IsClosed T)
    {H : ℝ} {N M : Cover → Cover}
    (hN : OrientedCMCCharts S H N) (hM : OrientedCMCCharts T H M) :
    IsClosed (S∩relativeContainmentNeighborhood S
      (T∩{a | N (representative a)=M (representative a)})) := by
  let A := T∩{a | N (representative a)=M (representative a)}
  let Z := relativeContainmentNeighborhood S A
  let D := S∩Z
  have hAc : IsClosed A := hT.inter (isClosed_eq
    (continuous_periodic_descent hN.normal_smooth.continuous hN.normal_periodic)
    (continuous_periodic_descent hM.normal_smooth.continuous hM.normal_periodic))
  have hDA : D⊆A := fun a ha => relativeContainmentNeighborhood_mem ha.1 ha.2
  apply isClosed_of_closure_subset
  intro a ha
  have haS : a∈S := closure_minimal inter_subset_left hS ha
  have haA : a∈A := closure_minimal hDA hAc ha
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hxS : quotientMap x∈S := by rwa [hxa]
  have hxT : quotientMap x∈T := by rw [hxa]; exact haA.1
  have hNM : N x=M x := haA.2
  obtain ⟨hn,f,hf,hf0,hfm,hfc⟩ := hN.chart x hxS
  obtain ⟨_,g,hg,hg0,hgm,hgc⟩ := hM.chart x hxT
  rw [← hNM] at hgm hgc
  let G := normalGraph (N x) f
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry (N x)).contDiff.add (hf.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  have hheight := normalGraph_boundary_height hn hf hf0 hgc
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((hfm.and hgm).and hheight)
  have hc : (0 : Plane)∈closure (φ ⁻¹' D) := quotient_graph_closure inter_subset_left
    (hfc.mono fun v hv => hv.mp) (by rwa [hxa])
  obtain ⟨y,hyD,hyd⟩ := Metric.mem_closure_iff.mp hc r hr
  have hyr : y∈Metric.ball (0 : Plane) r := by
    simpa only [Metric.mem_ball,dist_comm] using hyd
  have hO : IsOpen (φ ⁻¹' Z∩Metric.ball 0 r) :=
    (isOpen_interior.preimage hφ).inter Metric.isOpen_ball
  have hOeq : φ ⁻¹' Z∩Metric.ball 0 r⊆{z | f z=g z} := by
    intro z hz
    have hb := hball hz.2
    exact hb.2.mp (relativeContainmentNeighborhood_mem hb.1.1.2.1 hz.1).1
  have hpatch : (Metric.ball (0 : Plane) r∩interior {z | f z=g z}).Nonempty :=
    ⟨y,hyr,(hO.subset_interior_iff.mpr hOeq) ⟨hyD.2,hyr⟩⟩
  have heq := cmcGraph_unique_continuation hf hg Metric.isOpen_ball
    (convex_ball (0 : Plane) r).isPreconnected
    (fun z hz => (hball hz).1.1.2.2.trans (hball hz).1.2.2.2.symm) hpatch
  have he : f =ᶠ[𝓝 (0 : Plane)] g := Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) heq
  have heg : ∀ᶠ y in 𝓝 (0 : Plane),f =ᶠ[𝓝 y] g := eventually_eventually_nhds.mpr he
  refine ⟨haS,?_⟩
  rw [← hxa]
  apply quotient_graph_containment_germ (hfc.mono fun v hv => hv.mp)
  filter_upwards [hfm,hgm,he,heg] with z hz hk hez hezg
  have heG : normalGraph (N x) f z=normalGraph (N x) g z := by
    simp only [normalGraph,hez]
  refine ⟨?_,?_⟩
  · simpa only [heG] using hk.2.1
  · change N (representative (φ z))=M (representative (φ z))
    rw [periodic_representative hN.normal_periodic,periodic_representative hM.normal_periodic]
    change N (x+normalGraph (N x) f z)=M (x+normalGraph (N x) f z)
    rw [hz.1,heG,hk.1,(plane_gradient_eventuallyEq hezg).eq_of_nhds]

theorem OrientedCMCCharts.containment_of_patch
    {S T : Set Torus} (hS : IsClosed S) (hT : IsClosed T) (hSc : IsPreconnected S)
    {H : ℝ} {N M : Cover → Cover}
    (hN : OrientedCMCCharts S H N) (hM : OrientedCMCCharts T H M)
    {U : Set Torus} (hU : IsOpen U) (hpatch : (S∩U).Nonempty)
    (hu : S∩U⊆T∩{a | N (representative a)=M (representative a)}) :
    S⊆T∩{a | N (representative a)=M (representative a)} := by
  apply preconnected_subset_of_closed_germ hSc (hN.containment_germs_closed hS hT hM)
  obtain ⟨a,haS,haU⟩ := hpatch
  refine ⟨a,haS,?_⟩
  apply hU.subset_interior_iff.mpr ?_ haU
  intro b hb
  by_cases hbs : b∈S
  · exact Or.inr (hu ⟨hbs,hb⟩)
  · exact Or.inl hbs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem OrientedCMCCharts.curvature_eq_of_patch
    {S T : Set Torus} {H K : ℝ} {N M : Cover → Cover}
    (hN : OrientedCMCCharts S H N) (hM : OrientedCMCCharts T K M)
    {U : Set Torus} (hU : IsOpen U) (hpatch : (S∩U).Nonempty)
    (hu : S∩U⊆T∩{a | N (representative a)=M (representative a)}) : H=K := by
  obtain ⟨a,haS,haU⟩ := hpatch
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hxS : quotientMap x∈S := by rwa [hxa]
  have hxT : quotientMap x∈T := by rw [hxa]; exact (hu ⟨haS,haU⟩).1
  have hNM : N x=M x := (hu ⟨haS,haU⟩).2
  obtain ⟨hn,f,hf,hf0,hfm,_⟩ := hN.chart x hxS
  obtain ⟨_,g,hg,hg0,hgm,hgc⟩ := hM.chart x hxT
  rw [← hNM] at hgm hgc
  have hφ : Tendsto (fun y => quotientMap (x+normalGraph (N x) f y))
      (𝓝 (0 : Plane)) (𝓝 a) := by
    have ht : Tendsto (fun y : Plane => x+normalGraph (N x) f y)
        (𝓝 (0 : Plane)) (𝓝 x) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := x)).add (normalGraph_tendsto_zero hf hf0)
    simpa only [Function.comp_def,hxa] using (continuous_quotientMap.tendsto x).comp ht
  have hheight := normalGraph_boundary_height hn hf hf0 hgc
  have he : f =ᶠ[𝓝 (0 : Plane)] g := by
    filter_upwards [hfm,hheight,hφ.eventually (hU.mem_nhds haU)] with y hy he hu'
    exact he.mp (hu ⟨hy.2.1,hu'⟩).1
  have hflux : (fun y => cmcFlux (gradient f y))=ᶠ[𝓝 (0 : Plane)]
      (fun y => cmcFlux (gradient g y)) := by
    filter_upwards [plane_gradient_eventuallyEq he] with y hy
    rw [hy]
  have hd : planeDivergence (fun y => cmcFlux (gradient f y)) 0=
      planeDivergence (fun y => cmcFlux (gradient g y)) 0 := by
    simp only [planeDivergence,hflux.fderiv_eq]
  rw [hfm.self_of_nhds.2.2,hgm.self_of_nhds.2.2] at hd
  linarith

theorem OrientedCMCCharts.eq_of_patch
    {S T : Set Torus} (hS : IsClosed S) (hT : IsClosed T)
    (hSc : IsPreconnected S) (hTc : IsPreconnected T)
    {H K : ℝ} {N M : Cover → Cover}
    (hN : OrientedCMCCharts S H N) (hM : OrientedCMCCharts T K M)
    {U : Set Torus} (hU : IsOpen U) (hpatch : (S∩U).Nonempty)
    (hst : S∩U=T∩U)
    (hu : ∀ a∈S∩U,N (representative a)=M (representative a)) :
    S=T ∧ ∀ a∈S,N (representative a)=M (representative a) := by
  have hsub : S∩U⊆T∩{a | N (representative a)=M (representative a)} := by
    intro a ha
    exact ⟨(hst ▸ ha).1,hu a ha⟩
  have hHK := hN.curvature_eq_of_patch hM hU hpatch hsub
  subst K
  have hST := hN.containment_of_patch hS hT hSc hM hU hpatch hsub
  have hTS := hM.containment_of_patch hT hS hTc hN hU (hst ▸ hpatch) (by
    intro a ha
    have hh : a∈S∩U := hst.symm ▸ ha
    exact ⟨hh.1,(hu a hh).symm⟩)
  exact ⟨Subset.antisymm (fun a ha => (hST ha).1) (fun a ha => (hTS ha).1),fun a ha => (hST ha).2⟩

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_NormalMeasureCoordinateReflection
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma volumeSupport_local_mono {E F U : Set Torus} (hU : IsOpen U)
    (hEF : E∩U⊆F∩U) {a : Torus} (haU : a∈U) (haE : a∈volumeSupport E) :
    a∈volumeSupport F := by
  have hh := Measure.interior_inter_support (μ := torusVolume.restrict E) (s := U)
  rw [hU.interior_eq] at hh
  have hh' := hh ⟨haU,haE⟩
  have he : (torusVolume.restrict E).restrict U=torusVolume.restrict (E∩U) := by
    rw [Measure.restrict_restrict hU.measurableSet,inter_comm]
  rw [he] at hh'
  exact (Measure.support_mono (Measure.restrict_mono (hEF.trans inter_subset_left) le_rfl)) hh'

lemma volumeSupport_local_eq {E F U : Set Torus} (hU : IsOpen U) (hEF : E∩U=F∩U) :
    volumeSupport E∩U=volumeSupport F∩U := by
  ext a
  constructor
  · exact fun ha => ⟨volumeSupport_local_mono hU hEF.subset ha.2 ha.1,ha.2⟩
  · exact fun ha => ⟨volumeSupport_local_mono hU hEF.symm.subset ha.2 ha.1,ha.2⟩

lemma openRepresentative_local_eq {E F U : Set Torus} (hU : IsOpen U) (hEF : E∩U=F∩U) :
    openRepresentative E∩U=openRepresentative F∩U := by
  have hec : Eᶜ∩U=Fᶜ∩U := by
    ext a
    have hh := Set.ext_iff.mp hEF a
    simp only [mem_inter_iff,mem_compl_iff] at *
    tauto
  have hs := volumeSupport_local_eq hU hec
  ext a
  have hh := Set.ext_iff.mp hs a
  simp only [openRepresentative,mem_inter_iff,mem_compl_iff] at *
  tauto

lemma isMinimizerAt_frontier_local_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : E∩U=F∩U) :
    frontier (openRepresentative E)∩U=frontier (openRepresentative F)∩U := by
  have hec : Eᶜ∩U=Fᶜ∩U := by
    ext a
    have hh := Set.ext_iff.mp he a
    simp only [mem_inter_iff,mem_compl_iff] at *
    tauto
  have hh := volumeSupport_local_eq hU he
  have hc := volumeSupport_local_eq hU hec
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmE,
    isMinimizerAt_frontier_openRepresentative hW hF hmF]
  ext a
  have hh' := Set.ext_iff.mp hh a
  have hc' := Set.ext_iff.mp hc a
  simp only [mem_inter_iff] at *
  tauto

lemma local_region_flux_eq {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (he : E∩U=F∩U) {X : Cover → Cover}
    (hz : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,X y=0) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence X x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' F,divergence X x := by
  classical
  rw [← integral_indicator (measurableSet_fundamentalCube.inter (measurable_quotientMap hE)),
    ← integral_indicator (measurableSet_fundamentalCube.inter (measurable_quotientMap hF))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : quotientMap x∈U
  · have hh := Set.ext_iff.mp he (quotientMap x)
    simp only [mem_inter_iff,hx,and_true] at hh
    simp only [Set.indicator_apply,mem_inter_iff,mem_preimage,hh]
  · have he0 : X=ᶠ[𝓝 x] (fun _ => 0) := hz x hx
    have hd : divergence X x=0 := by
      have hd0 : fderiv ℝ X x=0 := he0.fderiv_eq.trans (congrFun (fderiv_const (𝕜 := ℝ) (E := Cover) (c := (0 : Cover))) x)
      simp only [divergence,hd0,zero_apply,PiLp.zero_apply,Finset.sum_const_zero]
    simp only [Set.indicator_apply,hd,ite_self]

lemma local_region_weightedPerimeter_eq {E F U : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (he : E∩U=F∩U)
    {φ : Cover → ℝ} (hzero : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0) :
    weightedPerimeter E φ=weightedPerimeter F φ := by
  unfold weightedPerimeter
  congr 1
  funext X
  congr 1
  funext hX
  rw [local_region_flux_eq hE hF he (X := fun y => φ y • X y) (by
    intro x hx
    filter_upwards [hzero x hx] with y hy
    rw [hy,zero_smul])]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_region_weighted_mass_eq {E F U : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (he : E∩U=F∩U)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hp : ∀ m x,φ (x+latticeVector m)=φ x) (hn : ∀ x,0≤φ x)
    (hz : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0) :
    (∫ z,φ z.1 ∂(μ : Measure NormalBundle))=∫ z,φ z.1 ∂(ν : Measure NormalBundle) := by
  have hh := local_region_weightedPerimeter_eq hE hF he hz
  rw [normalMeasure_weightedPerimeter hμ hφ hp hn,
    normalMeasure_weightedPerimeter hν hφ hp hn] at hh
  have hh' := congrArg ENNReal.toReal hh
  have hm0 : 0≤∫ z,φ z.1 ∂(μ : Measure NormalBundle) := integral_nonneg fun z => hn z.1
  have hn0 : 0≤∫ z,φ z.1 ∂(ν : Measure NormalBundle) := integral_nonneg fun z => hn z.1
  simpa only [ENNReal.toReal_ofReal hm0,ENNReal.toReal_ofReal hn0] using hh'

theorem isMinimizerAt_normal_local_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : E∩U=F∩U)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)∩U) : N x=M x := by
  obtain ⟨φ,hφ,hp,hb,⟨T,hT,hxT,hone⟩,hzero⟩ := exists_periodic_local_cutoff (quotientMap x) hU hx.2
  have hbound := isMinimizerAt_frontier_local_eq hV hW hE hF hmE hmF hU he
  have hxF : quotientMap x∈frontier (openRepresentative F) := (hbound ▸ hx).1
  have hunit (y : Cover) (hy : quotientMap y∈frontier (openRepresentative E)) : ‖N y‖=1 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmE hμ hN.continuous.norm continuous_const
      (fun k y => by rw [hpN]) (fun _ _ => rfl) _ y hy
    filter_upwards [haN] with z hz
    rw [hz,z.2.property]
  have hmass := local_region_weighted_mass_eq hE hF he hμ hν hφ hp (fun y => (hb y).1) hzero
  have hX : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y • N y) := hφ.smul hN
  have hXp : ∀ k y,φ (y+latticeVector k) • N (y+latticeVector k)=φ y • N y :=
    fun k y => by rw [hp,hpN]
  have hflux : (∫ z,φ z.1*⟪(z.2 : Cover),N z.1⟫ ∂(ν : Measure NormalBundle))=
      ∫ z,φ z.1 ∂(ν : Measure NormalBundle) := by
    calc
      _ = ∫ z,⟪(z.2 : Cover),φ z.1 • N z.1⟫ ∂(ν : Measure NormalBundle) := by simp only [real_inner_smul_right]
      _ = ∫ y in fundamentalCube∩quotientMap ⁻¹' F,divergence (fun y => φ y • N y) y := periodic_normal_flux hν hX hXp
      _ = ∫ y in fundamentalCube∩quotientMap ⁻¹' E,divergence (fun y => φ y • N y) y :=
        (local_region_flux_eq hE hF he (by intro y hy; filter_upwards [hzero y hy] with z hz; rw [hz,zero_smul])).symm
      _ = ∫ z,⟪(z.2 : Cover),φ z.1 • N z.1⟫ ∂(μ : Measure NormalBundle) := (periodic_normal_flux hμ hX hXp).symm
      _ = ∫ z,φ z.1 ∂(μ : Measure NormalBundle) := by
        apply integral_congr_ae
        filter_upwards [haN] with z hz
        rw [real_inner_smul_right,hz,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
      _ = _ := hmass
  have hbF := normalMeasure_frontier_ae (E := openRepresentative F) (isOpen_openRepresentative F).measurableSet
    (hν.congr_ae (isMinimizerAt_openRepresentative_ae hW hF hmF).symm)
  have hid : (fun z : NormalBundle => φ z.1*‖N z.1-M z.1‖^2) =ᵐ[(ν : Measure NormalBundle)]
      (fun z => 2*(φ z.1-φ z.1*⟪(z.2 : Cover),N z.1⟫)) := by
    filter_upwards [haM,hbF] with z hz hzF
    by_cases hp0 : φ z.1=0
    · simp only [hp0,zero_mul,sub_self,mul_zero]
    · have hzU : quotientMap z.1∈U := by
        by_contra hh
        exact hp0 (hzero z.1 hh).self_of_nhds
      have hzE : quotientMap z.1∈frontier (openRepresentative E) := (hbound.symm.subset ⟨hzF,hzU⟩).1
      rw [hz,norm_sub_sq_real,hunit z.1 hzE,z.2.property,real_inner_comm]
      ring
  have hiφ := integrable_normal_base hφ.continuous ν
  have hiX : Integrable (fun z : NormalBundle => φ z.1*⟪(z.2 : Cover),N z.1⟫) (ν : Measure NormalBundle) := by
    simpa only [normalTest,ContinuousMap.coe_mk,real_inner_smul_right] using
      (normalTest _ hX.continuous).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := integrable_normal_base
    (hφ.continuous.mul ((hN.continuous.sub hM.continuous).norm.pow 2)) ν
  have hiz : (∫ z,φ z.1*‖N z.1-M z.1‖^2 ∂(ν : Measure NormalBundle))=0 := by
    rw [integral_congr_ae hid,integral_const_mul,integral_sub hiφ hiX,hflux,sub_self,mul_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle =>
    mul_nonneg (hb z.1).1 (sq_nonneg _)) hi).mp hiz
  have hxzero := isMinimizerAt_periodic_ae_eq_boundary hW hF hmF hν
    (hφ.continuous.mul ((hN.continuous.sub hM.continuous).norm.pow 2)) continuous_const
    (fun k y => by
      change φ (y+latticeVector k)*‖N (y+latticeVector k)-M (y+latticeVector k)‖^2=φ y*‖N y-M y‖^2
      rw [hp,hpN,hpM]) (fun _ _ => rfl) hae x hxF
  change φ x*‖N x-M x‖^2=0 at hxzero
  rw [(hone x hxT).self_of_nhds,one_mul] at hxzero
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hxzero))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_connected_of_shared_patch {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    (hU : IsOpen U) (he : E∩U=F∩U)
    (hpatch : (frontier (openRepresentative E)∩U).Nonempty) :
    IsPreconnected (frontier (openRepresentative F)) := by
  obtain ⟨μ,H,N,hμ,haN,hchart⟩ := isMinimizerAt_oriented_CMC_charts hV hE hmE
  obtain ⟨ν,K,M,hν,hM,hpM,haM,hgeom,_,hc|hq⟩ :=
    Periodic.isMinimizerAt_connected_or_zero_curvature hW hF hmF
  · exact hc
  · exfalso
    obtain ⟨a,ha,haU⟩ := hpatch
    let x := representative a
    have hxa : quotientMap x=a := quotientMap_representative a
    have hb := isMinimizerAt_frontier_local_eq hV hW hE hF hmE hmF hU he
    have hxF : quotientMap x∈frontier (openRepresentative F) := by rw [hxa]; exact (hb ▸ (show a∈frontier (openRepresentative E)∩U from ⟨ha,haU⟩)).1
    have hloc := (isMinimizerAt_zero_curvature_local_normal hW hF hmF hν hM hpM haM
      (fun z hz => (hgeom z hz).1) hq x hxF).2
    have hxU : quotientMap x∈U := by rwa [hxa]
    have hnb : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈U := by
      have hh : Tendsto (fun v : Cover => quotientMap (x+v)) (𝓝 0) (𝓝 (quotientMap (x+0))) :=
        (continuous_quotientMap.comp (continuous_const.add continuous_id)).tendsto (0 : Cover)
      apply hh.eventually_mem
      simpa only [add_zero] using hU.mem_nhds hxU
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hloc.and hnb)
    let T := quotientMap '' Metric.ball x r
    have hT : IsOpen T := by
      dsimp only [T]
      rw [quotientMap_image_ball]
      exact Metric.isOpen_ball
    have haT : a∈T := ⟨x,Metric.mem_ball_self hr,hxa⟩
    have hTU : T⊆U := by
      rintro b ⟨z,hz,rfl⟩
      have hz' : z-x∈Metric.ball (0 : Cover) r := by simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hz
      simpa only [add_sub_cancel] using (hball hz').2
    have hnorm (b : Torus) (hbt : b∈frontier (openRepresentative E)∩T) :
        N (representative b)=M x := by
      obtain ⟨z,hz,hzb⟩ := hbt.2
      have hz' : z-x∈Metric.ball (0 : Cover) r := by simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hz
      have hzE : quotientMap z∈frontier (openRepresentative E)∩U := by rw [hzb]; exact ⟨hbt.1,hTU hbt.2⟩
      have hzF : quotientMap z∈frontier (openRepresentative F) := (hb ▸ hzE).1
      have hh : M z=M x := by
        simpa only [add_sub_cancel] using (hball hz').1.2 (by simpa only [add_sub_cancel] using hzF)
      rw [← hzb,periodic_representative hchart.normal_periodic]
      exact (isMinimizerAt_normal_local_eq hV hW hE hF hmE hmF hU he hμ hν
        hchart.normal_smooth hM hchart.normal_periodic hpM haN haM z hzE).trans hh
    exact isMinimizerAt_no_constant_normal_patch hV hE hmE hconn hμ hchart.normal_smooth
      hchart.normal_periodic haN hT ⟨a,ha,haT⟩ (M x) hnorm

theorem isMinimizerAt_boundary_eq_of_shared_patch {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    (hU : IsOpen U) (he : E∩U=F∩U)
    (hpatch : (frontier (openRepresentative E)∩U).Nonempty) :
    frontier (openRepresentative E)=frontier (openRepresentative F) ∧
      ∃ (μ ν : FiniteMeasure NormalBundle) (N M : Cover → Cover),
        IsNormalMeasure E μ ∧ IsNormalMeasure F ν ∧
        ContDiff ℝ (⊤ : ℕ∞) N ∧ ContDiff ℝ (⊤ : ℕ∞) M ∧
        (∀ k x,N (x+latticeVector k)=N x) ∧ (∀ k x,M (x+latticeVector k)=M x) ∧
        (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
        (∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover)) ∧
        ∀ x,quotientMap x∈frontier (openRepresentative E) → N x=M x := by
  have hcF := isMinimizerAt_connected_of_shared_patch hV hW hE hF hmE hmF hconn hU he hpatch
  obtain ⟨μ,H,N,hμ,haN,hN⟩ := isMinimizerAt_oriented_CMC_charts hV hE hmE
  obtain ⟨ν,K,M,hν,haM,hM⟩ := isMinimizerAt_oriented_CMC_charts hW hF hmF
  have hb := isMinimizerAt_frontier_local_eq hV hW hE hF hmE hmF hU he
  have hnloc (a : Torus) (ha : a∈frontier (openRepresentative E)∩U) : N (representative a)=M (representative a) :=
    isMinimizerAt_normal_local_eq hV hW hE hF hmE hmF hU he hμ hν hN.normal_smooth hM.normal_smooth
      hN.normal_periodic hM.normal_periodic haN haM (representative a) (by simpa only [quotientMap_representative] using ha)
  have hh := hN.eq_of_patch isClosed_frontier isClosed_frontier hconn hcF hM hU hpatch hb hnloc
  refine ⟨hh.1,μ,ν,N,M,hμ,hν,hN.normal_smooth,hM.normal_smooth,hN.normal_periodic,hM.normal_periodic,haN,haM,?_⟩
  intro x hx
  simpa only [periodic_representative hN.normal_periodic,periodic_representative hM.normal_periodic] using hh.2 (quotientMap x) hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_replace_ae {E F U : Set Torus} (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus)) :
    ((F\U)∪(E∩U) : Set Torus) =ᵐ[torusVolume] F := by
  filter_upwards [he] with a ha
  have hh : (a∈E ∧ a∈U) ↔ (a∈F ∧ a∈U) := Iff.of_eq ha
  change (a∈(F\U)∪(E∩U))=(a∈F)
  apply propext
  simp only [mem_union,Set.mem_sdiff,mem_inter_iff]
  tauto

lemma local_replace_inter (E F U : Set Torus) : ((F\U)∪(E∩U))∩U=E∩U := by
  ext a
  simp only [mem_union,Set.mem_sdiff,mem_inter_iff]
  tauto

lemma openRepresentative_local_ae_eq {E F U : Set Torus} (hU : IsOpen U)
    (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus)) :
    openRepresentative E∩U=openRepresentative F∩U := by
  have hh := openRepresentative_local_eq hU (local_replace_inter E F U).symm
  rwa [openRepresentative_congr_ae (local_replace_ae he)] at hh

lemma isMinimizerAt_normal_local_ae_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus))
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)∩U) : N x=M x := by
  let F' := (F\U)∪(E∩U)
  have hF' : MeasurableSet F' := (hF.diff hU.measurableSet).union (hE.inter hU.measurableSet)
  have hrep : F' =ᵐ[torusVolume] F := local_replace_ae he
  exact isMinimizerAt_normal_local_eq hV hW hE hF' hmE ((isMinimizerAt_congr_ae hrep).mpr hmF)
    hU (local_replace_inter E F U).symm hμ (hν.congr_ae hrep.symm) hN hM hpN hpM haN haM x hx

lemma quotient_chart_ae {A : Set Cover} (hc : A⊆fundamentalCube)
    {P : Torus → Prop} (hP : MeasurableSet {a | a∈quotientMap '' A → P a})
    (he : ∀ᵐ x : Cover ∂volume,x∈A → P (quotientMap x)) :
    ∀ᵐ a ∂torusVolume,a∈quotientMap '' A → P a := by
  change ∀ᵐ a ∂Measure.map quotientMap (volume.restrict fundamentalCube),_
  apply (ae_map_iff measurable_quotientMap.aemeasurable hP).mpr
  filter_upwards [ae_restrict_of_ae he,ae_restrict_mem measurableSet_fundamentalCube] with x hx hxc hxa
  have hz : representative (quotientMap x)∈A := by
    change quotientMap x∈representative ⁻¹' A
    rw [← image_quotientMap_eq_preimage_representative hc]
    exact hxa
  rw [representative_quotientMap_of_mem hxc] at hz
  exact hx hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_common_boundary_phases {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hb : frontier (openRepresentative E)=frontier (openRepresentative F))
    (ha : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ U : Set Torus,IsOpen U ∧ quotientMap cubeCenter∈U ∧
      ((E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus) ∨
       (E∩U : Set Torus) =ᵐ[torusVolume] (Fᶜ∩U : Set Torus)) := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,_,hcover,_,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmE (quotientMap cubeCenter) ha
  have hcov (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x (Metric.ball_subset_ball (by linarith) hx)
  have hgr : ContDiffOn ℝ 1 g (Metric.ball 0 (r/2)) :=
    (hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))
  obtain ⟨R,ρ,A,_,_,_,_,_,hρ,_,hA,hρA,_,hAc,_,hphaseE⟩ :=
    actual_centered_graph_phase_patch hV hE hmE ha hn (by linarith : 0 < r/2) hg hg0 hgr hcov
  obtain ⟨S,σ,B,_,_,_,_,_,hσ,_,hB,hσB,_,_,_,hphaseF⟩ :=
    actual_centered_graph_phase_patch hW hF hmF (hb ▸ ha) hn (by linarith : 0 < r/2) hg hg0 hgr (by rwa [← hb])
  let ε := min ρ σ
  have hε : 0<ε := lt_min hρ hσ
  let C := Metric.ball cubeCenter ε
  let U := quotientMap '' C
  have hCA : C⊆A := (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by
    have hh : ε≤ρ := min_le_left _ _; linarith))).trans hρA
  have hCB : C⊆B := (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by
    have hh : ε≤σ := min_le_right _ _; linarith))).trans hσB
  have hCc : C⊆fundamentalCube := fun x hx i => ⟨(hAc (hCA hx) i).1.le,(hAc (hCA hx) i).2⟩
  have hU : IsOpen U := by dsimp [U,C]; rw [quotientMap_image_ball]; exact Metric.isOpen_ball
  have hnz : ∀ᵐ x : Cover ∂volume,graphSignedHeight cubeCenter n g x≠0 := by
    rw [ae_iff]
    simpa only [graphSignedHeight,not_not,sub_eq_zero] using graph_trace_volume_zero cubeCenter hn hg.continuous
  have htransfer (G : Set Torus) (hG : MeasurableSet G)
      (he : ∀ᵐ x : Cover ∂volume,x∈C → (quotientMap x∈E ↔ quotientMap x∈G)) :
      (E∩U : Set Torus) =ᵐ[torusVolume] (G∩U : Set Torus) := by
    have hh := quotient_chart_ae hCc
      (show MeasurableSet {a : Torus | a∈U → (a∈E ↔ a∈G)} from
        hU.measurableSet.imp (hE.iff hG)) he
    filter_upwards [hh] with a ha
    change (a ∈ E ∩ U) = (a ∈ G ∩ U)
    simp only [mem_inter_iff]
    by_cases hu : a∈U
    · exact propext (and_congr_left (fun _ => ha hu))
    · simp only [hu,and_false]
  refine ⟨U,hU,⟨cubeCenter,Metric.mem_ball_self hε,rfl⟩,?_⟩
  rcases hphaseE with he|he <;> rcases hphaseF with hf|hf
  · left
    apply htransfer F hF
    filter_upwards [he,hf] with x hx hy hxc
    exact (hx (hCA hxc)).trans (hy (hCB hxc)).symm
  · right
    apply htransfer Fᶜ hF.compl
    filter_upwards [he,hf,hnz] with x hx hy hz hxc
    rw [mem_compl_iff,hy (hCB hxc),not_lt,hx (hCA hxc)]
    exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h hz⟩
  · right
    apply htransfer Fᶜ hF.compl
    filter_upwards [he,hf,hnz] with x hx hy hz hxc
    rw [mem_compl_iff,hy (hCB hxc),not_lt,hx (hCA hxc)]
    exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h (Ne.symm hz)⟩
  · left
    apply htransfer F hF
    filter_upwards [he,hf] with x hx hy hxc
    exact (hx (hCA hxc)).trans (hy (hCB hxc)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_common_boundary_phases {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hb : frontier (openRepresentative E)=frontier (openRepresentative F))
    (a : Torus) (ha : a∈frontier (openRepresentative E)) :
    ∃ U : Set Torus,IsOpen U ∧ a∈U ∧
      ((E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus) ∨
       (E∩U : Set Torus) =ᵐ[torusVolume] (Fᶜ∩U : Set Torus)) := by
  let b := a-quotientMap cubeCenter
  let E' := (fun z : Torus => z+b) ⁻¹' E
  let F' := (fun z : Torus => z+b) ⁻¹' F
  have hE' : MeasurableSet E' := (continuous_add_const b).measurable hE
  have hF' : MeasurableSet F' := (continuous_add_const b).measurable hF
  have hmE' : IsMinimizerAt V E' := isMinimizerAt_translation hmE b
  have hmF' : IsMinimizerAt W F' := isMinimizerAt_translation hmF b
  have hbd : frontier (openRepresentative E')=frontier (openRepresentative F') := by
    rw [frontier_openRepresentative_translation hE,frontier_openRepresentative_translation hF,hb]
  have hcenter : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+b∈frontier (openRepresentative E)
    have he : quotientMap cubeCenter+b=a := by dsimp [b]; abel
    rw [he]
    exact ha
  obtain ⟨U,hU,haU,hph⟩ := isMinimizerAt_centered_common_boundary_phases hV hW hE' hF' hmE' hmF' hbd hcenter
  let T := (fun z : Torus => z-b) ⁻¹' U
  have hT : IsOpen T := hU.preimage (continuous_id.sub continuous_const)
  have haT : a∈T := by
    change a-b∈U
    simpa only [b,sub_sub_cancel] using haU
  have hback (G : Set Torus)
      (hh : (E'∩U : Set Torus) =ᵐ[torusVolume] (((fun z : Torus => z+b) ⁻¹' G)∩U : Set Torus)) :
      (E∩T : Set Torus) =ᵐ[torusVolume] (G∩T : Set Torus) := by
    have hmp := (measurePreserving_add_right torusVolume (-b)).quasiMeasurePreserving.preimage_ae_eq hh
    filter_upwards [hmp] with z hz
    change ((z + -b + b∈E) ∧ z + -b∈U)=((z + -b + b∈G) ∧ z + -b∈U) at hz
    change (z∈E ∧ z-b∈U)=(z∈G ∧ z-b∈U)
    simpa only [sub_eq_add_neg,add_assoc,neg_add_cancel,add_zero] using hz
  refine ⟨T,hT,haT,?_⟩
  rcases hph with h|h
  · exact Or.inl (hback F h)
  · exact Or.inr (hback Fᶜ h)

lemma normal_reverse_ae {ν : FiniteMeasure NormalBundle} {M : Cover → Cover}
    (hM : Continuous M) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover)) :
    ∀ᵐ z ∂(ν.map reverseNormal : Measure NormalBundle),-M z.1=(z.2 : Cover) := by
  have hh := polar_reverse_normal (continuous_periodic_descent hM hpM).measurable (μ := ν) (N := fun a => M (representative a)) (by
    simpa only [periodic_representative hpM] using haM)
  simpa only [periodic_representative hpM] using hh

theorem isMinimizerAt_oriented_boundary_local_ae {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hb : frontier (openRepresentative E)=frontier (openRepresentative F))
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (he : ∀ x,quotientMap x∈frontier (openRepresentative E) → N x=M x)
    (a : Torus) (ha : a∈frontier (openRepresentative E)) :
    ∃ U : Set Torus,IsOpen U ∧ a∈U ∧ (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus) := by
  obtain ⟨U,hU,haU,hph⟩ := isMinimizerAt_common_boundary_phases hV hW hE hF hmE hmF hb a ha
  rcases hph with hh|hh
  · exact ⟨U,hU,haU,hh⟩
  · exfalso
    let x := representative a
    have hx : quotientMap x∈frontier (openRepresentative E)∩U := by
      dsimp only [x]
      simpa only [quotientMap_representative,mem_inter_iff] using And.intro ha haU
    have hneg := isMinimizerAt_normal_local_ae_eq hV (by constructor <;> linarith [hW.1,hW.2] : 1-W∈Ioo 0 1)
      hE hF.compl hmE ((isMinimizerAt_compl ⟨hW.1.le,hW.2.le⟩).mpr hmF) hU hh hμ (isNormalMeasure_compl hF hν)
      hN hM.neg hpN (fun k y => by rw [hpM]) haN (normal_reverse_ae hM.continuous hpM haM) x hx
    have hxzero : N x=0 := by
      have hn := he x hx.1
      have hsum : (2:ℝ) • N x=0 := by
        rw [two_smul]
        calc N x+N x = -M x+M x := congrArg₂ (·+·) hneg hn
             _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp hsum).resolve_left (by norm_num)
    have hunit : ‖N x‖=1 := by
      apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmE hμ hN.continuous.norm continuous_const
        (fun k y => by rw [hpN]) (fun _ _ => rfl) _ x hx.1
      filter_upwards [haN] with z hz
      rw [hz,z.2.property]
    norm_num [hxzero] at hunit

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sets_eq_of_common_frontier_local_eq {E F : Set Torus}
    (hb : frontier E=frontier F) (hne : (frontier E).Nonempty)
    (hloc : ∀ a∈frontier E,∃ U : Set Torus,IsOpen U ∧ a∈U ∧ E∩U=F∩U) : E=F := by
  let : ConnectedSpace Torus := quotientMap_surjective.connectedSpace continuous_quotientMap
  let D := (E∩Fᶜ)∪(F∩Eᶜ)
  have hfront : frontier D⊆frontier E := by
    intro a ha
    rcases frontier_union_subset (E∩Fᶜ) (F∩Eᶜ) ha with hh|hh
    · rcases frontier_inter_subset E Fᶜ hh.1 with hz|hz
      · exact hz.1
      · rw [frontier_compl,← hb] at hz
        exact hz.2
    · rcases frontier_inter_subset F Eᶜ hh.2 with hz|hz
      · exact hb.symm ▸ hz.1
      · rw [frontier_compl] at hz
        exact hz.2
  have havoid (a : Torus) (ha : a∈frontier E) : a∉closure D := by
    obtain ⟨U,hU,haU,he⟩ := hloc a ha
    intro hc
    obtain ⟨b,hbU,hbD⟩ := mem_closure_iff.mp hc U hU haU
    have hh := Set.ext_iff.mp he b
    simp only [mem_inter_iff,hbU,and_true] at hh
    change (b∈E ∧ b∉F) ∨ (b∈F ∧ b∉E) at hbD
    tauto
  have hcl : IsClopen D := isClopen_iff_frontier_eq_empty.mpr (eq_empty_iff_forall_notMem.mpr (by
    intro a ha
    exact havoid a (hfront ha) (frontier_subset_closure ha)))
  have hD : D=∅ := by
    by_contra hn
    have hdall := hcl.eq_univ (nonempty_iff_ne_empty.mpr hn)
    obtain ⟨a,ha⟩ := hne
    exact havoid a ha (subset_closure (by rw [hdall]; exact mem_univ a))
  ext a
  have hh : a∉D := by rw [hD]; exact notMem_empty a
  change ¬((a∈E ∧ a∉F) ∨ (a∈F ∧ a∉E)) at hh
  tauto

theorem isMinimizerAt_region_eq_of_shared_patch {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    (hU : IsOpen U) (he : E∩U=F∩U)
    (hpatch : (frontier (openRepresentative E)∩U).Nonempty) : E =ᵐ[torusVolume] F := by
  obtain ⟨hb,μ,ν,N,M,hμ,hν,hN,hM,hpN,hpM,haN,haM,heN⟩ :=
    isMinimizerAt_boundary_eq_of_shared_patch hV hW hE hF hmE hmF hconn hU he hpatch
  have hop : openRepresentative E=openRepresentative F := by
    apply sets_eq_of_common_frontier_local_eq hb (hpatch.mono inter_subset_left)
    intro a ha
    obtain ⟨T,hT,haT,hh⟩ := isMinimizerAt_oriented_boundary_local_ae hV hW hE hF hmE hmF hb
      hμ hν hN hM hpN hpM haN haM heN a ha
    exact ⟨T,hT,haT,openRepresentative_local_ae_eq hT hh⟩
  apply (isMinimizerAt_openRepresentative_ae hV hE hmE).symm.trans
  rw [hop]
  exact isMinimizerAt_openRepresentative_ae hW hF hmF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_two_phase_frontier {V : ℝ} (hV : V∈Ioo 0 1)
    {E U : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hconn : IsPreconnected U)
    (h₁ : 0<torusVolume.real (E∩U)) (h₂ : 0<torusVolume.real (Eᶜ∩U)) :
    (frontier (openRepresentative E)∩U).Nonempty := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hmE
  have hp₁ : 0<torusVolume.real (openRepresentative E∩U) := by
    convert h₁ using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg ENNReal.toReal (measure_congr (hae.inter EventuallyEq.rfl))
  have hp₂ : 0<torusVolume.real ((openRepresentative E)ᶜ∩U) := by
    convert h₂ using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg ENNReal.toReal (measure_congr (hae.compl.inter EventuallyEq.rfl))
  simpa only [inter_comm] using preconnected_crosses_frontier hconn (isOpen_openRepresentative E)
    (by simpa only [inter_comm] using nonempty_of_measureReal_ne_zero hp₁.ne')
    (by simpa only [inter_comm] using nonempty_of_measureReal_ne_zero hp₂.ne')

theorem isMinimizerAt_reflection_symmetry_of_competitor_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3)
    (hmF : IsMinimizerAt V (reflectionCompetitor i E (coordinateHalf i 0))) :
    coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E := by
  let B := coordinateHalf i 0
  let F := reflectionCompetitor i E B
  have hB : IsOpen B := coordinateHalf_open i
  have hd : Disjoint B (coordinateReflection i ⁻¹' B) := by
    dsimp only [B]
    rw [coordinateHalf_zero]
    exact reflection_sublevel_disjoint (coordinateSine_periodic i) (coordinateSine_reflection i)
  have hF : MeasurableSet F := reflectionCompetitor_measurable i hE hB.measurableSet
  have hvF : torusVolume.real F=V := by
    rw [Measure.real_def,hmF.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hv : torusVolume.real (E∩B)=V/2 := by
    have hh := reflectionCompetitor_realVolume i hE hB.measurableSet hd
    change torusVolume.real F=2*torusVolume.real (E∩B) at hh
    linarith
  have hsum : torusVolume.real (E∩B)+torusVolume.real (Eᶜ∩B)=1/2 := by
    rw [← measureReal_union (Disjoint.mono inter_subset_left inter_subset_left disjoint_compl_right)
      (hE.compl.inter hB.measurableSet)]
    have he : (E∩B)∪(Eᶜ∩B)=B := by ext z; simp only [mem_union,mem_inter_iff,mem_compl_iff]; tauto
    rw [he]
    exact coordinateHalf_realVolume i
  have hpatch := isMinimizerAt_two_phase_frontier hV hE hmE (coordinateHalf_preconnected i)
    (by rw [hv]; linarith [hV.1]) (by linarith [hV.2])
  have he : E =ᵐ[torusVolume] F := isMinimizerAt_region_eq_of_shared_patch hV hV hE hF hmE hmF
    hconn hB (reflectionCompetitor_retained i E hd) hpatch
  have hh := (coordinateReflection_measurePreserving i).quasiMeasurePreserving.preimage_ae_eq he
  rw [reflectionCompetitor_invariant] at hh
  exact hh.trans he.symm

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor_oai := @OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor_oai
