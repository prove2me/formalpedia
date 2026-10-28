-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:21:36.016613+00:00
-- url     : https://prove2.me/submissions/0de467e6-7e8c-4935-a50f-2301794e8fac

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_H1_translation_jacobi
import Theorems.Thm_OAI_CubicTorus_actual_centered_graph_phase_patch
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_center_normal_unique
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_nodal_truncation_impossible
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_smooth_CMC

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

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

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

end CubicTorus

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
open Filter
open scoped Topology RealInnerProductSpace

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

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

namespace CubicTorus
open scoped RealInnerProductSpace

lemma compactCell_coordinates (z : CompactCell) (i : Fin 3) :
    0 ≤ (z : Cover) i ∧ (z : Cover) i ≤ 1 := by
  obtain ⟨x, hx, he⟩ := z.property
  rw [← he]
  exact ⟨hx.1 i, hx.2 i⟩

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

lemma setIntegral_characteristic {E : Set Torus} (hE : MeasurableSet E) (s : Set Torus)
    (_hs : MeasurableSet s) :
    (∫ x in s, characteristic E x ∂torusVolume) = torusVolume.real (E ∩ s) := by
  change (∫ x in s, E.indicator (fun _ ↦ (1 : ℝ)) x ∂torusVolume) = _
  rw [integral_indicator hE, Measure.restrict_restrict hE,
    integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]

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

lemma radialDensityWeight_contDiff (a : Cover) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDensityWeight a r ε) :=
  sublevelCutoff_contDiff ((contDiff_id.sub contDiff_const).norm_sq ℝ) _ _

lemma radialDensityWeight_nonneg (a : Cover) (r ε : ℝ) (x : Cover) :
    0 ≤ radialDensityWeight a r ε x := Real.smoothTransition.nonneg _

lemma radialDensityWeight_zero {a x : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hx : r ≤ ‖x - a‖) : radialDensityWeight a r ε x = 0 := by
  apply sublevelCutoff_eq_zero hε
  nlinarith

end CubicTorus

end
end

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_halfspaceIndicator (n : Cover) : Measurable (halfspaceIndicator n) :=
  measurable_const.indicator (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet

lemma halfspaceIndicator_bound (n x : Cover) : |halfspaceIndicator n x| ≤ 1 := by
  classical
  by_cases hx : ⟪n, x⟫ < 0 <;> simp [halfspaceIndicator, hx]

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

lemma divergence_tsupport_subset (F : Cover → Cover) :
    tsupport (divergence F) ⊆ tsupport F := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hh
  exact hx (divergence_of_notMem_tsupport hh)

theorem normalMeasure_local_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)) =
      ∫ x : Cover, characteristic E (quotientMap x) * divergence F x := by
  let G := latticePeriodize F
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := latticePeriodize_contDiff hF hc
  have hGp : ∀ n x, G (x + latticeVector n) = G x := latticePeriodize_periodic F
  obtain ⟨M, hM, hb⟩ := periodic_bounded hG.continuous hGp
  have hflux := normalMeasure_flux hμ hG hGp (by linarith : 0 < M + 1)
    (fun x ↦ (hb x).trans (by linarith : M ≤ M + 1))
  have he (z : NormalBundle) : G z.1 = F z.1 :=
    (latticePeriodize_eventuallyEq hc hs (compactCell_coordinates z.1)).eq_of_nhds
  change (∫ z, ⟪(z.2 : Cover), G z.1⟫ ∂(μ : Measure NormalBundle)) = _ at hflux
  simp_rw [he] at hflux
  have hdiv : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence G x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))]
      with x hx
    have hd := (latticePeriodize_eventuallyEq hc hs (fun i ↦ ⟨(hx.1 i).1, (hx.1 i).2.le⟩)).fderiv_eq (𝕜 := ℝ)
    simp only [divergence, G, hd]
  rw [hdiv] at hflux
  rw [hflux, ← integral_indicator (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ fundamentalCube
  · by_cases he : quotientMap x ∈ E <;> simp [characteristic, hx, he]
  · have hd : divergence F x = 0 := by
      apply divergence_of_notMem_tsupport
      intro hh
      apply hx
      exact fun i ↦ ⟨(hs hh i).1.le, (hs hh i).2⟩
    simp [hx, hd]

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

lemma integral_cover_affine_scaling (g : Cover → ℝ) (a : Cover) {r : ℝ} (hr : 0 < r) :
    (∫ x, g x) = r ^ 3 * ∫ y : Cover, g (r • y + a) := by
  have h := Measure.integral_comp_smul (volume : Measure Cover) (fun x ↦ g (x + a)) r
  rw [integral_add_right_eq_self, show Module.finrank ℝ Cover = 3 by simp [Cover],
    smul_eq_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le 3))] at h
  rw [h]
  field_simp

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialDensityWeight_le_one (a : Cover) (r ε : ℝ) (x : Cover) :
    radialDensityWeight a r ε x ≤ 1 := Real.smoothTransition.le_one _

lemma radialDensityWeight_tsupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (radialDensityWeight a r ε) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  exact hx (radialDensityWeight_zero hr hε (le_of_lt (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hh)))

lemma radialDensityWeight_hasCompactSupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    HasCompactSupport (radialDensityWeight a r ε) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (radialDensityWeight_tsupport hr hε)

lemma radialHeightCutoff_one {a x : Cover} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.closedBall a r) : radialHeightCutoff a r x = 1 := by
  have hnorm : ‖x - a‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (by positivity : 0 < 3 * r ^ 2)).mpr
  nlinarith [norm_nonneg (x - a)]

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
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma integral_compact_fderiv_zero {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (v : X) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hi : Integrable (fun x ↦ fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : X ↦ (1 : ℝ)) (g := f) (v := v)
    (by simp)
    (by simpa using hi) (by simpa using hf.continuous.integrable_of_hasCompactSupport hs)
    (fun _ _ ↦ differentiableAt_const 1) (fun _ _ ↦ hf.differentiable (by simp) |>.differentiableAt)
  simpa using hh

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

lemma normalPlaneCoordinates_lipschitz (n : Cover) :
    LipschitzWith 1 (normalPlaneCoordinates n) := by
  apply (normalPlaneCoordinates n).lipschitz.weaken
  change ‖(normalPlaneLinearIsometry n).toContinuousLinearMap.adjoint‖₊ ≤ 1
  simp

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

lemma integral_normalColumnChart (a n : Cover) {f : Cover → ℝ} (hf : Integrable f) :
    (∫ x : Cover, f x) = ∫ y : Plane, ∫ t : ℝ, f (normalColumnChart a n (t, y)) := by
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f]
  have hi := (normalColumnChart_measurePreserving a n).integrable_comp
    hf.aestronglyMeasurable |>.mpr hf
  exact integral_prod_symm (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z))
    (by simpa only [Measure.volume_eq_prod, Function.comp_def] using hi)

lemma normalColumnChart_height (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) : ⟪n, normalColumnChart a n (t, y) - a⟫ = t := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, inner_add_right,
    normalPlaneEmbedding_inner hn, inner_smul_right, real_inner_self_eq_norm_sq,
    hn, one_pow, mul_one, zero_add]

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

lemma normalColumnChart_line_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (y : Plane) :
    Isometry (fun t : ℝ ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + s • n) -
      (a + (normalPlaneEmbedding n y + t • n)) = (s - t) • n := by rw [sub_smul]; abel
  rw [he, norm_smul, Real.norm_eq_abs, hn, mul_one, Real.dist_eq]

lemma normalColumnChart_plane_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) :
    Isometry (fun y : Plane ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + t • n) -
      (a + (normalPlaneEmbedding n z + t • n)) = normalPlaneEmbedding n (y - z) := by
    rw [show normalPlaneEmbedding n (y - z) = normalPlaneEmbedding n y - normalPlaneEmbedding n z from
      (normalPlaneLinearIsometry n).map_sub y z]; abel
  rw [he, normalPlaneEmbedding_norm, dist_eq_norm]

lemma halfspace_directional_integrable {ψ : Cover → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (a n v : Cover) :
    Integrable (fun x ↦ halfspaceIndicator n (x - a) * fderiv ℝ ψ x v) := by
  exact (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hs.fderiv_apply ℝ v)).bdd_mul
      ((measurable_halfspaceIndicator n).comp (measurable_id.sub_const a)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n (x-a))

lemma integral_halfspace_normal_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) =
      ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  rw [integral_normalColumnChart a n (halfspace_directional_integrable hψ hs a n n)]
  apply integral_congr_ae
  filter_upwards [] with y
  let f : ℝ → ℝ := fun t ↦ ψ (normalColumnChart a n (t,y))
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ normalColumnChart a n (t,y)) := by
    simp_rw [normalColumnChart_apply a hn]
    fun_prop
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hψ.comp hc
  have hfs : HasCompactSupport f := hs.comp_isClosedEmbedding
    (normalColumnChart_line_isometry a hn y).isClosedEmbedding
  have hd (t : ℝ) : deriv f t = fderiv ℝ ψ (normalColumnChart a n (t,y)) n := by
    have hh : HasDerivAt (fun s : ℝ ↦ normalColumnChart a n (s,y)) n t := by
      simp_rw [normalColumnChart_apply a hn]
      simpa only [one_smul, add_zero, zero_add, id_eq, add_assoc] using
        ((hasDerivAt_id t).smul_const n).const_add (a + normalPlaneEmbedding n y)
    exact (((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hh).deriv
  have he (t : ℝ) : halfspaceIndicator n (normalColumnChart a n (t,y)-a) *
      fderiv ℝ ψ (normalColumnChart a n (t,y)) n = (Iio (0 : ℝ)).indicator (deriv f) t := by
    by_cases ht : t < 0 <;> simp [halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    hfs.integral_Iic_deriv_eq (hf.of_le (by simp)) 0]
  simp [f, normalColumnChart_apply a hn]

lemma integral_halfspace_tangent_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Plane) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)) = 0 := by
  let f : Cover → ℝ := fun x ↦ halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)
  have hi := halfspace_directional_integrable hψ hs a n (normalPlaneEmbedding n v)
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f, Measure.volume_eq_prod]
  have hic := (normalColumnChart_measurePreserving a n).integrable_comp hi.aestronglyMeasurable |>.mpr hi
  rw [integral_prod (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z)) (by
    simpa only [Measure.volume_eq_prod, Function.comp_def] using hic)]
  have he (t : ℝ) : (∫ y : Plane, f (normalColumnChart a n (t,y))) = 0 := by
    let g : Plane → ℝ := fun y ↦ ψ (normalColumnChart a n (t,y))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ normalColumnChart a n (t,y)) := by
      simp_rw [normalColumnChart_apply a hn]
      exact contDiff_const.add ((normalPlaneLinearIsometry n).contDiff.add contDiff_const)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hψ.comp hc
    have hs' : HasCompactSupport g := hs.comp_isClosedEmbedding
      (normalColumnChart_plane_isometry a hn t).isClosedEmbedding
    have hd (y : Plane) : fderiv ℝ g y v =
        fderiv ℝ ψ (normalColumnChart a n (t,y)) (normalPlaneEmbedding n v) := by
      have hline := ((normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt (x := y)).add_const (t • n) |>.const_add a
      have hh := ((hψ.differentiable (by simp) _).hasFDerivAt.comp y hline).fderiv
      have he : g = ψ ∘ (fun z : Plane ↦ a + ((normalPlaneLinearIsometry n).toContinuousLinearMap z + t • n)) := by
        funext z
        simp only [g, Function.comp_def, normalColumnChart_apply a hn]
        rfl
      rw [he, hh, normalColumnChart_apply a hn]
      rfl
    have hh : (fun y : Plane ↦ f (normalColumnChart a n (t,y))) =
        fun y ↦ (if t < 0 then (1 : ℝ) else 0) * fderiv ℝ g y v := by
      ext y
      by_cases ht : t < 0 <;> simp [f, halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
    rw [hh, integral_const_mul, integral_compact_fderiv_zero hg hs', mul_zero]
  simp_rw [he]
  simp

lemma integral_halfspace_directional_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Cover) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x v) =
      ⟪n,v⟫ * ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  have he (x : Cover) : halfspaceIndicator n (x-a) * fderiv ℝ ψ x v =
      halfspaceIndicator n (x-a) * fderiv ℝ ψ x
        (normalPlaneEmbedding n (normalPlaneCoordinates n v)) +
      ⟪n,v⟫ * (halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) := by
    conv_lhs => arg 2; arg 2; rw [← normalPlaneCoordinates_reconstruct hn v]
    rw [map_add, map_smul]
    ring
  simp_rw [he]
  rw [integral_add (halfspace_directional_integrable hψ hs a n _)
      ((halfspace_directional_integrable hψ hs a n n).const_mul ⟪n,v⟫),
    integral_const_mul, integral_halfspace_tangent_derivative a hn hψ hs,
    integral_halfspace_normal_derivative a hn hψ hs, zero_add]

theorem integral_halfspace_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * divergence F x) =
      ∫ y : Plane, ⟪n, F (a + normalPlaneEmbedding n y)⟫ := by
  let ψ : Fin 3 → Cover → ℝ := fun i x ↦ F x i
  have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hps (i : Fin 3) : HasCompactSupport (ψ i) := hs.comp_left
    (show (EuclideanSpace.proj i) (0 : Cover) = 0 by simp)
  have hd (x : Cover) : divergence F x = ∑ i : Fin 3,
      fderiv ℝ (ψ i) x (EuclideanSpace.single i 1) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have hh := (((EuclideanSpace.proj i).hasFDerivAt).comp x
      ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv
    change fderiv ℝ (ψ i) x = _ at hh
    rw [hh]
    rfl
  simp_rw [hd, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ halfspace_directional_integrable (hp i) (hps i) a n _)]
  simp_rw [integral_halfspace_directional_derivative a hn (hp _) (hps _)]
  have hg (i : Fin 3) : Integrable (fun y : Plane ↦ ⟪n, EuclideanSpace.single i 1⟫ *
      ψ i (a + normalPlaneEmbedding n y)) := by
    have hc := (hp i).continuous.comp (normalColumnChart_plane_isometry a hn 0).continuous
    have hcc := (hps i).comp_isClosedEmbedding (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
    have hi := (hc.integrable_of_hasCompactSupport (μ := volume) hcc).const_mul ⟪n, EuclideanSpace.single i 1⟫
    simpa only [Function.comp_def, normalColumnChart_apply a hn, zero_smul, add_zero] using hi
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ ↦ hg i)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [EuclideanSpace.inner_single_right, ψ]
  simp [PiLp.inner_apply, mul_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalMove_hasFDerivAt (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (normalMove n f)
      (ContinuousLinearMap.id ℝ Cover + (fderiv ℝ f x).smulRight n) x := by
  exact (hasFDerivAt_id x).add (hf.hasFDerivAt.smul_const n)

lemma normalMove_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (normalMove n f) := contDiff_id.add (hf.smul_const n)

lemma normalPullback_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (normalPullback n f F) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hG := hF.comp (normalMove_contDiff n hf)
  exact (contDiff_const.add (hd.clm_apply contDiff_const)).smul hG |>.sub
    ((hd.clm_apply hG).smul contDiff_const)

lemma divergence_comp_normalMove (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) {F : Cover → Cover}
    (hF : DifferentiableAt ℝ F (normalMove n f x)) :
    divergence (fun y ↦ F (normalMove n f y)) x =
      divergence F (normalMove n f x) +
        fderiv ℝ f x (fderiv ℝ F (normalMove n f x) n) := by
  have hd := (hF.hasFDerivAt.comp x (normalMove_hasFDerivAt n hf)).fderiv
  change fderiv ℝ (fun y ↦ F (normalMove n f y)) x = _ at hd
  simp only [divergence, hd, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [linearForm_apply_basis]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalPullback_divergence (n : Cover) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (normalPullback n f F) x =
      normalJacobian n f x * divergence F (normalMove n f x) := by
  have hfd := (hf.differentiable (by simp)).differentiableAt (x := x)
  have hdf := ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp)).differentiableAt (x := x)
  have hm := normalMove_hasFDerivAt n hfd
  have hg := (hF.differentiable (by simp)).differentiableAt (x := normalMove n f x)
  have hu := hg.hasFDerivAt.comp x hm
  have hj := (hdf.hasFDerivAt.clm_apply (hasFDerivAt_const n x)).const_add 1
  have hb := hdf.hasFDerivAt.clm_apply hu
  have he := ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)) n (F (normalMove n f x))
  change divergence (fun y ↦ normalJacobian n f y • F (normalMove n f y) -
    fderiv ℝ f y (F (normalMove n f y)) • n) x = _
  have hjf := hj.fderiv
  change fderiv ℝ (normalJacobian n f) x = _ at hjf
  dsimp only [Function.comp_def] at hb
  have hJ : DifferentiableAt ℝ (normalJacobian n f) x := hj.differentiableAt
  have hU : DifferentiableAt ℝ (fun y ↦ F (normalMove n f y)) x := hu.differentiableAt
  have hB : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y (F (normalMove n f y))) x := hb.differentiableAt
  have hA : DifferentiableAt ℝ
      (fun y ↦ normalJacobian n f y • F (normalMove n f y)) x := hJ.smul hU
  have hC : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (F (normalMove n f y)) • n) x := hB.smul_const n
  rw [divergence_sub_fields hA hC,
    divergence_smul_function hJ hU, divergence_smul_const hB, inner_gradient_left,
    hjf, hb.fderiv, divergence_comp_normalMove n hfd hg]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, zero_add,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, map_zero, smul_eq_mul]
  dsimp only [normalJacobian, Function.comp_def]
  rw [← he]
  ring

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

lemma graphHeightExtension_fderiv (a n : Cover) {g : Plane → ℝ} (hg : Differentiable ℝ g)
    (x : Cover) : fderiv ℝ (graphHeightExtension a n g) x =
      (fderiv ℝ g (normalPlaneCoordinates n (x-a))).comp (normalPlaneCoordinates n) := by
  unfold graphHeightExtension
  have hp := (normalPlaneCoordinates n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, graphHeightExtension] using
    ((hg _).hasFDerivAt.comp x hp).fderiv

lemma graphHeightExtension_normal (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    fderiv ℝ (graphHeightExtension a n g) x n = 0 := by
  rw [graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    normalPlaneCoordinates_normal hn, map_zero]

lemma graphShear_jacobian (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    normalJacobian n (graphHeightExtension a n g) x = 1 := by
  rw [normalJacobian, graphHeightExtension_normal a hn hg, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphSublevelIndicator_shear (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) :
    graphSublevelIndicator a n g (graphShear a n g x) = halfspaceIndicator n (x-a) := by
  have hheight : ⟪n, graphShear a n g x - a⟫ = ⟪n,x-a⟫ + graphHeightExtension a n g x := by
    simp only [graphShear, normalMove, add_sub_right_comm, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  have hp : graphHeightExtension a n g (graphShear a n g x) = graphHeightExtension a n g x :=
    congrArg g (graphShear_projection a hn g x)
  simp only [graphSublevelIndicator, Set.indicator, Set.mem_ofPred_eq, hheight, hp,
    add_lt_iff_neg_right, halfspaceIndicator]

lemma normalPullback_graph_compactSupport (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {F : Cover → Cover} (hs : HasCompactSupport F) :
    HasCompactSupport (normalPullback n (graphHeightExtension a n g) F) := by
  have hc := hs.comp_homeomorph (graphShearHomeomorph a hn hg)
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx
  dsimp only [Function.comp_def, graphShearHomeomorph] at hx
  have hh : F (graphShear a n g x) = 0 := hx
  simp only [Function.mem_support, not_not]
  change normalPullback n (graphHeightExtension a n g) F x = 0
  change F (normalMove n (graphHeightExtension a n g) x) = 0 at hh
  simp only [normalPullback, hh, smul_zero, map_zero, zero_smul, sub_self]

lemma graphAreaVector_pullback (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (F : Cover → Cover) (y : Plane) :
    ⟪n, normalPullback n (graphHeightExtension a n g) F (a+normalPlaneEmbedding n y)⟫ =
      ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hs : graphShear a n g (a+normalPlaneEmbedding n y) = a+normalGraph n g y := by
    simp only [graphShear, normalMove, graphHeightExtension, add_sub_cancel_left,
      normalPlaneCoordinates_embedding, normalGraph]
    abel
  rw [normalPullback, graphShear_jacobian a hn hg, one_smul, ← graphShear, hs,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow,
    mul_one, graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    add_sub_cancel_left, normalPlaneCoordinates_embedding]
  rw [graphAreaVector, inner_sub_left]
  congr 1
  rw [show normalPlaneEmbedding n (gradient g y) =
    (normalPlaneLinearIsometry n).toContinuousLinearMap (gradient g y) from rfl,
    ← ContinuousLinearMap.adjoint_inner_right, inner_gradient_left]
  rfl

theorem integral_graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hmp : MeasurePreserving (graphShearHomeomorph a hn hg.continuous).toMeasurableEquiv :=
    graphShear_measurePreserving a hn hg.continuous.measurable
  rw [← hmp.integral_comp' (fun x : Cover ↦ graphSublevelIndicator a n g x * divergence F x)]
  have he (x : Cover) : graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
      divergence F (graphShearHomeomorph a hn hg.continuous x) =
      halfspaceIndicator n (x-a) * divergence (normalPullback n (graphHeightExtension a n g) F) x := by
    change graphSublevelIndicator a n g (graphShear a n g x) * divergence F (graphShear a n g x) = _
    rw [graphSublevelIndicator_shear a hn, normalPullback_divergence n
      (graphHeightExtension_contDiff a n hg) hF,
      graphShear_jacobian a hn (hg.differentiable (by simp)), one_mul]
    rfl
  change (∫ x : Cover, graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
    divergence F (graphShearHomeomorph a hn hg.continuous x)) = _
  simp_rw [he]
  rw [integral_halfspace_divergence a hn
    (normalPullback_contDiff n (graphHeightExtension_contDiff a n hg) hF)
    (normalPullback_graph_compactSupport a hn hg.continuous hs)]
  apply integral_congr_ae
  exact Eventually.of_forall (graphAreaVector_pullback a hn (hg.differentiable (by simp)) F)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma plane_gradient_norm (g : Plane → ℝ) (y : Plane) :
    ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

lemma graph_trace_compactSupport {X : Type*} [Zero X]
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} (hg : Continuous g)
    {F : Cover → X} (hs : HasCompactSupport F) :
    HasCompactSupport (fun y : Plane ↦ F (a+normalGraph n g y)) := by
  have hc := (hs.comp_homeomorph (graphShearHomeomorph a hn hg)).comp_isClosedEmbedding
    (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
  have he (y : Plane) : graphShearHomeomorph a hn hg (normalColumnChart a n (0,y)) =
      a+normalGraph n g y := by
    change graphShear a n g (normalColumnChart a n (0,y)) = _
    rw [graphShear_columnChart a hn, zero_add, normalColumnChart_apply a hn]
    rfl
  simpa only [Function.comp_def, he] using hc

lemma graphAreaVector_continuous (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (graphAreaVector n g) := by
  have hd := (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  exact continuous_const.sub ((normalPlaneLinearIsometry n).continuous.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp hd))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_probability_average_integrable {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (_hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) ν := by
  apply (integrable_const (|f x|+(K : ℝ)*δ)).mono'
    (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  filter_upwards [hb] with y hy
  have hh := hf.dist_le_mul (x-y) x
  rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
  rw [Real.norm_eq_abs]
  have ht := abs_add_le (f (x-y)-f x) (f x)
  rw [sub_add_cancel] at ht
  exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hy K.coe_nonneg])

lemma lipschitz_probability_average_error {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    |(∫ y, f (x-y) ∂ν)-f x| ≤ (K : ℝ)*δ := by
  have hi := lipschitz_probability_average_integrable hf hδ hb x
  have he : f x = ∫ _y : Plane, f x ∂ν := by simp
  rw [he, ← integral_sub hi (integrable_const _)]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  change (∫ y, ‖f (x-y)-f x‖ ∂ν) ≤ _
  calc
    _ ≤ ∫ _y : Plane, (K : ℝ)*δ ∂ν := by
      apply integral_mono_ae (hi.sub (integrable_const _)).norm (integrable_const _)
      filter_upwards [hb] with y hy
      have hh := hf.dist_le_mul (x-y) x
      rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
    _ = _ := by simp

lemma lipschitz_probability_average_hasFDerivAt {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ fderiv ℝ f (x-y)) ν ∧
      HasFDerivAt (fun z ↦ ∫ y, f (z-y) ∂ν) (∫ y, fderiv ℝ f (x-y) ∂ν) x := by
  refine hasFDerivAt_integral_of_dominated_loc_of_lip
    (F := fun z y : Plane ↦ f (z-y)) (F' := fun y ↦ fderiv ℝ f (x-y))
    (x₀ := x) (s := univ) (bound := fun _ ↦ (K : ℝ)) (Filter.univ_mem)
    (Eventually.of_forall fun z ↦ (hf.continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (lipschitz_probability_average_integrable hf hδ hb x)
    ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun y ↦ by
      have hl : LipschitzWith K (fun z : Plane ↦ f (z-y)) := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        simpa only [dist_sub_right] using hf.dist_le_mul (z-y) (w-y)
      simpa only [Real.nnabs_of_nonneg K.coe_nonneg, Real.toNNReal_coe] using hl.lipschitzOnWith
  · have hd : ∀ᵐ y ∂ν, DifferentiableAt ℝ f (x-y) := hν.ae_le
      ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hf.ae_differentiableAt)
    filter_upwards [hd] with y hy
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      hy.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma graphSmoothingMeasure_ac (b : ContDiffBump (0 : Plane)) :
    graphSmoothingMeasure b ≪ volume := withDensity_absolutelyContinuous _ _

lemma graphSmoothingMeasure_radius (b : ContDiffBump (0 : Plane)) :
    ∀ᵐ y ∂graphSmoothingMeasure b, ‖y‖ ≤ b.rOut := by
  rw [graphSmoothingMeasure, ae_withDensity_iff b.continuous_normed.measurable.ennreal_ofReal]
  filter_upwards [] with y hy
  have hh : y ∈ Function.support (b.normed volume) := by
    change b.normed volume y ≠ 0
    intro he
    simp [he] at hy
  rw [b.support_normed_eq, Metric.mem_ball, dist_zero_right] at hh
  exact hh.le

lemma graphSmooth_eq_convolution (b : ContDiffBump (0 : Plane)) (f : Plane → ℝ) :
    graphSmooth b f = b.normed volume ⋆ f := by
  funext x
  rw [graphSmooth, graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _), convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

lemma graphSmooth_contDiff (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : ContDiff ℝ (⊤ : ℕ∞) (graphSmooth b f) := by
  rw [graphSmooth_eq_convolution]
  exact b.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) b.contDiff_normed hf.continuous.locallyIntegrable

lemma graphSmooth_error (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : Plane) :
    |graphSmooth b f x-f x| ≤ (K : ℝ)*b.rOut :=
  lipschitz_probability_average_error hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_norm_ge {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖y‖ ≤ ‖normalGraph n g y‖ := by
  have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul (normalGraph n g y) 0
  simpa only [normalPlaneCoordinates_graph hn, map_zero, dist_zero_right,
    NNReal.coe_one, one_mul] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphRescaling
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

lemma graphSmooth_integrable (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) (graphSmoothingMeasure b) :=
  lipschitz_probability_average_integrable hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

lemma graphSmooth_lipschitz (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (graphSmooth b f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq,graphSmooth,graphSmooth,← integral_sub
    (graphSmooth_integrable b hf x) (graphSmooth_integrable b hf z)]
  calc
    _ ≤ ∫ y, |f (x-y)-f (z-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, (K : ℝ)*dist x z ∂graphSmoothingMeasure b := by
      apply integral_mono ((graphSmooth_integrable b hf x).sub (graphSmooth_integrable b hf z)).norm
        (integrable_const _)
      intro y
      change ‖f (x-y)-f (z-y)‖ ≤ (K : ℝ)*dist x z
      simpa only [Real.norm_eq_abs,← Real.dist_eq,dist_sub_right] using hf.dist_le_mul (x-y) (z-y)
    _ = _ := by simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVC1Patch
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

lemma integral_ball_affine_scaling (f : Cover → ℝ) (a : Cover) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    (∫ x in Metric.ball a (r*R), f x) =
      r^3 * ∫ y in Metric.ball (0 : Cover) R, f (a+r • y) := by
  have h := integral_cover_affine_scaling ((Metric.ball a (r*R)).indicator f) a hr
  rw [integral_indicator Metric.isOpen_ball.measurableSet] at h
  rw [h, ← integral_indicator Metric.isOpen_ball.measurableSet]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hm : r • x+a ∈ Metric.ball a (r*R) ↔ x ∈ Metric.ball (0 : Cover) R := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero,
      norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_iff_right₀ hr
  change (Metric.ball a (r*R)).indicator f (r • x+a) =
    (Metric.ball (0 : Cover) R).indicator (fun y ↦ f (a+r • y)) x
  by_cases hx : x ∈ Metric.ball (0 : Cover) R
  · rw [indicator_of_mem (hm.mpr hx),indicator_of_mem hx,add_comm]
  · rw [indicator_of_notMem ((not_congr hm).mpr hx),indicator_of_notMem hx]

lemma fundamentalCube_inter_ball_preimage (c : Cover) (r : ℝ)
    (hc : Metric.ball c r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    fundamentalCube ∩ quotientMap ⁻¹' Metric.ball (quotientMap c) r = Metric.ball c r := by
  ext x
  constructor
  · rintro ⟨hx,hq⟩
    rw [← quotientMap_image_ball c r] at hq
    obtain ⟨y,hy,he⟩ := hq
    have he' := quotientMap_injective_open_closed_cell
      (fun i ↦ ⟨(hx i).1,(hx i).2.le⟩) (hc hy) he.symm
    rwa [he']
  · intro hx
    refine ⟨fun i ↦ ⟨(hc hx i).1.le,(hc hx i).2⟩,?_⟩
    rw [mem_preimage, ← quotientMap_image_ball c r]
    exact mem_image_of_mem _ hx

lemma integral_quotient_ball (f : Torus → ℝ) (hf : Measurable f)
    (c : Cover) (r : ℝ)
    (hc : Metric.ball c r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x in Metric.ball (quotientMap c) r, f x ∂torusVolume) =
      ∫ x in Metric.ball c r, f (quotientMap x) := by
  rw [setIntegral_lift_measurable hf Metric.isOpen_ball.measurableSet,
    fundamentalCube_inter_ball_preimage c r hc]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupNormalMeasure
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
namespace CubicTorus

lemma integral_blowupCharacteristic_ball {E : Set Torus} (hE : MeasurableSet E)
    (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (hc : Metric.ball c (r*R) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    torusVolume.real (E ∩ Metric.ball (quotientMap c) (r*R)) =
      r^3 * ∫ x in Metric.ball (0 : Cover) R, blowupCharacteristic E c r x := by
  rw [← setIntegral_characteristic hE _ Metric.isOpen_ball.measurableSet,
    integral_quotient_ball _ (measurable_characteristic hE) c _ hc,
    integral_ball_affine_scaling _ c hr R]
  rfl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVOneDimensionalHat
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
namespace CubicTorus

lemma blowupCharacteristic_affine (E : Set Torus) (c p x : Cover) (r s : ℝ) :
    blowupCharacteristic E c r (p+s • x) =
      blowupCharacteristic E (c+r • p) (r*s) x := by
  simp [blowupCharacteristic,smul_add,mul_smul,add_assoc]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVPlanarLocalModels
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma blowup_test_inner_bound {F : Cover → Cover} (hn : ∀ x, ‖F x‖ ≤ 1)
    (z : BlowupNormalBundle) : |⟪(z.2 : Cover),F z.1⟫| ≤ 1 := by
  have hh : |⟪(z.2 : Cover),F z.1⟫| ≤ ‖F z.1‖ := by
    simpa only [Real.norm_eq_abs,z.2.property,one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (z.2 : Cover) (F z.1)
  exact hh.trans (hn _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma setIntegral_divergence_congr_local {A B O : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ x ∂(volume : Measure Cover), x ∈ O → (x ∈ A ↔ x ∈ B))
    {F : Cover → Cover} (hs : tsupport F ⊆ O) :
    (∫ x in A, divergence F x) = ∫ x in B, divergence F x := by
  rw [← integral_indicator hA,← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [hAB] with x hx
  by_cases ho : x ∈ O
  · have hh := hx ho
    by_cases ha : x ∈ A
    · simp only [indicator_of_mem ha,indicator_of_mem (hh.mp ha)]
    · simp only [indicator_of_notMem ha,indicator_of_notMem (mt hh.mpr ha)]
  · have hz : divergence F x = 0 := divergence_of_notMem_tsupport (fun hh ↦ ho (hs hh))
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha,hb,hz]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupComplement
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma divergence_eq_trace (F : Cover → Cover) (x : Cover) :
    divergence F x = LinearMap.trace ℝ Cover (fderiv ℝ F x).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [divergence,Matrix.trace,LinearMap.toMatrix_apply]

lemma divergence_isometry_pullback (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : Differentiable ℝ F) (x : Cover) :
    divergence (fun y ↦ R.symm (F (R y))) x = divergence F (R x) := by
  rw [divergence_eq_trace,divergence_eq_trace]
  have hd := R.symm.toContinuousLinearEquiv.hasFDerivAt.comp x
    ((hF (R x)).hasFDerivAt.comp x R.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y ↦ R.symm (F (R y))) _ x at hd
  rw [hd.fderiv]
  have he : (R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((fderiv ℝ F (R x)).comp R.toContinuousLinearEquiv.toContinuousLinearMap)).toLinearMap =
      R.symm.toLinearEquiv.conj (fderiv ℝ F (R x)).toLinearMap := rfl
  rw [he,LinearMap.trace_conj']

lemma isometry_pullback_contDiff (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ R.symm (F (R x))) :=
  R.symm.toContinuousLinearEquiv.contDiff.comp (hF.comp R.toContinuousLinearEquiv.contDiff)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlanarEssentialBoundary
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

lemma measureSupport_preimage_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {D : Set Y} {p : X}
    (hq : Measure.QuasiMeasurePreserving f μ ν) (hf : ContinuousAt f p)
    (hp : p ∈ (μ.restrict (f ⁻¹' D)).support) : f p ∈ (ν.restrict D).support := by
  rw [(nhds_basis_opens (f p)).mem_measureSupport]
  rintro U ⟨hpU,hU⟩
  rw [Measure.restrict_apply hU.measurableSet]
  by_contra h
  have hzero : ν (U ∩ D) = 0 := (not_lt.mp h).antisymm bot_le
  have hz := hq.preimage_null hzero
  have hpos := (Measure.mem_support_iff_forall p).mp hp (f ⁻¹' U)
    (hf (hU.mem_nhds hpU))
  rw [Measure.restrict_apply (hU.measurableSet.preimage hq.measurable)] at hpos
  exact (ne_of_gt hpos) hz

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_CoverEssentialBoundary
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

lemma cover_integral_indicator_ball {A : Set Cover} (hA : MeasurableSet A) (x : Cover) (t : ℝ) :
    (∫ y in Metric.ball x t, A.indicator (fun _ ↦ (1:ℝ)) y) =
      volume.real (A ∩ Metric.ball x t) := by
  rw [integral_indicator hA,Measure.restrict_restrict hA,integral_const,smul_eq_mul,mul_one,
    Measure.real_def,Measure.restrict_apply_univ]
  rfl

lemma integral_blowupCharacteristic_ball_center {E : Set Torus} (hE : MeasurableSet E)
    (c p : Cover) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hc : Metric.ball (c+r • p) (r*t) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    torusVolume.real (E ∩ Metric.ball (quotientMap (c+r • p)) (r*t)) =
      r^3 * ∫ x in Metric.ball p t, blowupCharacteristic E c r x := by
  have hh := integral_blowupCharacteristic_ball hE (c+r • p) hr t hc
  have he := integral_ball_affine_scaling (blowupCharacteristic E c r) p (by norm_num : (0:ℝ)<1) t
  have ha (y : Cover) : blowupCharacteristic E c r (p+y) =
      blowupCharacteristic E (c+r • p) r y := by
    simpa only [one_smul,mul_one] using blowupCharacteristic_affine E c p y r 1
  simp only [one_mul,one_pow,one_smul] at he
  simp_rw [ha] at he
  rw [he]
  exact hh

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

lemma graphMollifier_radius_tendsto :
    Tendsto (fun i ↦ (graphMollifier i).rOut) atTop (𝓝 0) := by
  simpa only [graphMollifier,one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma graphSmooth_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    Tendsto (fun i ↦ graphSmooth (graphMollifier i) g y) atTop (𝓝 (g y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    (by simpa only [mul_zero] using graphMollifier_radius_tendsto.const_mul (K:ℝ))
  exact graphSmooth_error _ hg y

theorem graphSmooth_fderiv_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {y : Plane} (hc : ContinuousAt (fderiv ℝ g) y) :
    Tendsto (fun i ↦ fderiv ℝ (graphSmooth (graphMollifier i) g) y)
      atTop (𝓝 (fderiv ℝ g y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  filter_upwards [graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hδ)] with i hi
  have ha := lipschitz_probability_average_hasFDerivAt (graphSmoothingMeasure_ac (graphMollifier i))
    hg (graphMollifier i).rOut_pos.le (graphSmoothingMeasure_radius (graphMollifier i)) y
  change dist (fderiv ℝ (fun z ↦ ∫ w, g (z-w) ∂graphSmoothingMeasure (graphMollifier i)) y) _ < ε
  rw [ha.2.fderiv,dist_eq_norm]
  have he : (∫ _w : Plane, fderiv ℝ g y ∂graphSmoothingMeasure (graphMollifier i)) = fderiv ℝ g y := by simp
  rw [← he,← integral_sub ha.1 (integrable_const _)]
  apply lt_of_le_of_lt (norm_integral_le_integral_norm _) ?_
  have hb : (∫ w, ‖fderiv ℝ g (y-w)-fderiv ℝ g y‖ ∂graphSmoothingMeasure (graphMollifier i)) ≤ ε/2 := by
    calc
      _ ≤ ∫ _w : Plane, ε/2 ∂graphSmoothingMeasure (graphMollifier i) := by
        apply integral_mono_ae (ha.1.sub (integrable_const _)).norm (integrable_const _)
        filter_upwards [graphSmoothingMeasure_radius (graphMollifier i)] with w hw
        have hh : dist (y-w) y < δ := by simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hw.trans_lt hi
        simpa only [dist_eq_norm,Pi.sub_apply] using (hclose hh).le
      _ = _ := by simp
  exact hb.trans_lt (by linarith)

lemma graphSmooth_gradient_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {y : Plane} (hc : ContinuousAt (fderiv ℝ g) y) :
    Tendsto (fun i ↦ gradient (graphSmooth (graphMollifier i) g) y) atTop (𝓝 (gradient g y)) := by
  exact ((InnerProductSpace.toDual ℝ Plane).symm.continuous.tendsto _).comp
    (graphSmooth_fderiv_tendsto hg hc)

end CubicTorus

end
end

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

lemma measurable_graphSublevelIndicator (a n : Cover) {g : Plane → ℝ} (hg : Measurable g) :
    Measurable (graphSublevelIndicator a n g) := by
  exact measurable_const.indicator (measurableSet_lt (by fun_prop)
    (hg.comp ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const))))

lemma graphSublevelIndicator_bound (a n : Cover) (g : Plane → ℝ) (x : Cover) :
    |graphSublevelIndicator a n g x| ≤ 1 := by
  classical
  by_cases hx : ⟪n,x-a⟫ < graphHeightExtension a n g x <;>
    simp [graphSublevelIndicator,hx]

lemma graphSublevelIndicator_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (a n : Cover) {x : Cover} (hx : ⟪n,x-a⟫ ≠ graphHeightExtension a n g x) :
    Tendsto (fun i ↦ graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x)
      atTop (𝓝 (graphSublevelIndicator a n g x)) := by
  have ht := graphSmooth_tendsto hg (normalPlaneCoordinates n (x-a))
  have he : ∀ᶠ i in atTop,
      graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x = graphSublevelIndicator a n g x := by
    by_cases hl : ⟪n,x-a⟫ < graphHeightExtension a n g x
    · filter_upwards [ht.eventually (Ioi_mem_nhds hl)] with i hi
      change (if ⟪n,x-a⟫ < graphSmooth (graphMollifier i) g (normalPlaneCoordinates n (x-a)) then (1:ℝ) else 0) = _
      rw [ite_eq_left hi]
      exact (indicator_of_mem hl (fun _ ↦ (1:ℝ))).symm
    · have hh : graphHeightExtension a n g x < ⟪n,x-a⟫ := lt_of_le_of_ne (not_lt.mp hl) hx.symm
      filter_upwards [ht.eventually (Iio_mem_nhds hh)] with i hi
      have hi' : ¬ ⟪n,x-a⟫ < graphHeightExtension a n (graphSmooth (graphMollifier i) g) x := not_lt.mpr hi.le
      simp [graphSublevelIndicator,hl,hi']
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with i hi
  exact hi.symm

lemma graphSublevel_flux_mollification_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    Tendsto (fun i ↦ ∫ x : Cover, graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x * divergence F x)
      atTop (𝓝 (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x)) := by
  have hi : Integrable (divergence F) := (continuous_divergence hF).integrable_of_hasCompactSupport
    (hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F))
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖divergence F x‖)
    (fun i ↦ ((measurable_graphSublevelIndicator a n (graphSmooth_contDiff _ hg).continuous.measurable).mul
      (continuous_divergence hF).measurable).aestronglyMeasurable) hi.norm
  · intro i
    filter_upwards [] with x
    simp only [Pi.mul_apply,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (graphSublevelIndicator_bound a n _ x)
  · have hae : ∀ᵐ x : Cover ∂volume, ⟪n,x-a⟫ ≠ graphHeightExtension a n g x := by
      simpa only [ae_iff,not_not] using graph_trace_volume_zero a hn hg.continuous
    filter_upwards [hae] with x hx
    exact (graphSublevelIndicator_tendsto hg a n hx).mul_const _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphAreaVector_norm_linear {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    ‖graphAreaVector n g y‖ ≤ 1+(K:ℝ) := by
  calc
    _ ≤ ‖n‖+‖normalPlaneEmbedding n (gradient g y)‖ := norm_sub_le _ _
    _ = 1+‖fderiv ℝ g y‖ := by rw [hn,normalPlaneEmbedding_norm,plane_gradient_norm]
    _ ≤ _ := add_le_add le_rfl (norm_fderiv_le_of_lipschitz ℝ hg)

lemma graph_trace_zero_outside {X : Type*} [Zero X] {a n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → X} {R : ℝ} (hs : tsupport F ⊆ Metric.closedBall a R)
    (g : Plane → ℝ) {y : Plane} (hy : y ∉ Metric.closedBall (0 : Plane) R) :
    F (a+normalGraph n g y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := hs h
  rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left] at hh
  exact hy (by simpa only [Metric.mem_closedBall,dist_zero_right] using
    (normalGraph_norm_ge hn g y).trans hh)

theorem integral_C1graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall a R) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hFs : HasCompactSupport F := (isCompact_closedBall a R).of_isClosed_subset isClosed_closure hs
  obtain ⟨M,hM⟩ := hF.continuous.norm.bddAbove_range_of_hasCompactSupport hFs.norm
  have hMb (x : Cover) : ‖F x‖ ≤ M := hM (mem_range_self x)
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans (hMb 0)
  let B : Plane → ℝ := (Metric.closedBall (0 : Plane) R).indicator (fun _ ↦ (1+(K:ℝ))*M)
  have hBi : Integrable B := (integrableOn_const (isCompact_closedBall (0 : Plane) R).measure_lt_top.ne).integrable_indicator Metric.isClosed_closedBall.measurableSet
  have ht : Tendsto (fun i ↦ ∫ y : Plane,
      ⟪graphAreaVector n (graphSmooth (graphMollifier i) g) y,
        F (a+normalGraph n (graphSmooth (graphMollifier i) g) y)⟫) atTop
      (𝓝 (∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫)) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun i ↦ ((graphAreaVector_continuous n (graphSmooth_contDiff _ hg)).inner
        (graph_trace_continuous a n (graphSmooth_contDiff _ hg).continuous hF.continuous)).aestronglyMeasurable) hBi
    · intro i
      filter_upwards [] with y
      by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
      · rw [show B y = (1+(K:ℝ))*M from indicator_of_mem hy _]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (graphAreaVector_norm_linear hn (graphSmooth_lipschitz _ hg) y)
            (hMb _) (norm_nonneg _) (by positivity))
      · rw [graph_trace_zero_outside hn hs _ hy,inner_zero_right,norm_zero,
          show B y = 0 from indicator_of_notMem hy _]
    · filter_upwards [] with y
      by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
      · have hd := graphSmooth_gradient_tendsto hg (hc y hy)
        have hnG : Tendsto (fun i ↦ normalGraph n (graphSmooth (graphMollifier i) g) y)
            atTop (𝓝 (normalGraph n g y)) :=
          tendsto_const_nhds.add ((graphSmooth_tendsto hg y).smul_const n)
        have hnA : Tendsto (fun i ↦ graphAreaVector n (graphSmooth (graphMollifier i) g) y)
            atTop (𝓝 (graphAreaVector n g y)) :=
          tendsto_const_nhds.sub (((normalPlaneLinearIsometry n).continuous.tendsto _).comp hd)
        exact hnA.inner ((hF.continuous.tendsto _).comp (tendsto_const_nhds.add hnG))
      · simp only [graph_trace_zero_outside hn hs _ hy,inner_zero_right]
        exact tendsto_const_nhds
  apply tendsto_nhds_unique (graphSublevel_flux_mollification_tendsto a hn hg hF hFs)
  simpa only [integral_graphSublevel_divergence a hn (graphSmooth_contDiff _ hg) hF hFs] using ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphAreaVector_continuousAt (n : Cover) {g : Plane → ℝ} {y : Plane}
    (hc : ContinuousAt (fderiv ℝ g) y) : ContinuousAt (graphAreaVector n g) y := by
  exact continuousAt_const.sub ((normalPlaneLinearIsometry n).continuous.continuousAt.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.continuousAt.comp hc))

lemma graph_weighted_continuous (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {R : ℝ}
    {φ : Cover → ℝ} (hφ : Continuous φ) (hs : tsupport φ ⊆ Metric.closedBall a R)
    {ψ : Plane → ℝ} (hψ : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt ψ y) :
    Continuous (fun y : Plane ↦ φ (a+normalGraph n g y)*ψ y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
  · exact (graph_trace_continuous a n hg hφ).continuousAt.mul (hψ y hy)
  · have he : (fun z : Plane ↦ φ (a+normalGraph n g z)*ψ z) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      rw [graph_trace_zero_outside hn hs _ hz,zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq he

lemma graph_weighted_integrable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {R : ℝ}
    {φ : Cover → ℝ} (hφ : Continuous φ) (hsφ : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Metric.closedBall a R)
    {ψ : Plane → ℝ} (hψ : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt ψ y) :
    Integrable (fun y : Plane ↦ φ (a+normalGraph n g y)*ψ y) :=
  (graph_weighted_continuous a hn hg hφ hs hψ).integrable_of_hasCompactSupport
    (graph_trace_compactSupport a hn hg hsφ).mul_right

lemma setIntegral_graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall a R) :
    (∫ x in {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x}, divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫ := by
  rw [← integral_C1graphSublevel_divergence a hn hg hc hF hs]
  have hm : MeasurableSet {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x} :=
    measurableSet_lt (by fun_prop) (hg.continuous.measurable.comp
      ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))
  rw [← integral_indicator hm]
  congr 1
  funext x
  classical
  by_cases hx : ⟪n,x-a⟫ < graphHeightExtension a n g x <;>
    simp [graphSublevelIndicator,hx]

theorem blowup_graph_patch_weighted_flux {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫ := by
  let H : Cover → Cover := fun x ↦ φ x • F x
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hφ.smul hF
  have hsH : HasCompactSupport H := hsφ.smul_right
  have hHO : tsupport H ⊆ O := (tsupport_smul_subset_left _ _).trans hφO
  have hnH (x) : ‖H x‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hφb x).1]
    exact (mul_le_mul (hφb x).2 (hnF x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have he : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),H z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) = ∫ z, ⟪(z.2 : Cover),H z.1⟫ ∂(ν : Measure BlowupNormalBundle) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hh : H z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hHO h))
    simp only [hh,inner_zero_right]
  have hm : MeasurableSet {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x} :=
    measurableSet_lt (by fun_prop) (hg.continuous.measurable.comp
      ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))
  have hh := hflux H hH hsH hHO hnH
  rw [setIntegral_divergence_congr_local hA hm hgraph
      ((tsupport_smul_subset_left _ _).trans hφU),
    setIntegral_graphSublevel_divergence a hn hg hc hH
      ((tsupport_smul_subset_left _ _).trans hφR)] at hh
  rw [← he] at hh
  simpa only [H,inner_smul_right] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphUnitNormalExtension_contDiff (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (graphUnitNormalExtension a n g) := by
  have hd := hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (gradient g) :=
    (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp hd
  exact (graphSlopeNormal_contDiff hn).comp (hgrad.comp
    ((normalPlaneCoordinates n).contDiff.comp (contDiff_id.sub contDiff_const)))

lemma graphUnitNormalExtension_graph (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g f : Plane → ℝ) (y : Plane) :
    graphUnitNormalExtension a n f (a+normalGraph n g y) = graphSlopeNormal n (gradient f y) := by
  unfold graphUnitNormalExtension
  rw [add_sub_cancel_left,normalGraph, map_add,map_smul,
    normalPlaneCoordinates_embedding,normalPlaneCoordinates_normal hn,smul_zero,add_zero]

lemma graphUnitNormalExtension_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {x : Cover}
    (hc : ContinuousAt (fderiv ℝ g) (normalPlaneCoordinates n (x-a))) :
    Tendsto (fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g) x)
      atTop (𝓝 (graphUnitNormalExtension a n g x)) :=
  ((graphSlopeNormal_contDiff hn).continuous.tendsto _).comp (graphSmooth_gradient_tendsto hg hc)

lemma graphAreaVector_inner_unit {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ⟪graphAreaVector n g y,graphSlopeNormal n (gradient g y)⟫ = ‖graphAreaVector n g y‖ := by
  have hh : 0 < ‖graphAreaVector n g y‖ := lt_of_lt_of_le (by norm_num) (graphSlopeVector_norm_ge hn _)
  rw [graphSlopeNormal,inner_smul_right,show n-normalPlaneEmbedding n (gradient g y)=graphAreaVector n g y from rfl,
    real_inner_self_eq_norm_sq]
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_area_trace_mollified_normal_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {φ : Cover → ℝ} (hφ : Continuous φ) (hsφ : HasCompactSupport φ)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφ0 : ∀ x, 0 ≤ φ x) :
    Tendsto (fun i ↦ ∫ y : Plane, φ (a+normalGraph n g y)*
      ⟪graphAreaVector n g y,graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g) (a+normalGraph n g y)⟫)
      atTop (𝓝 (∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
  have hi := graph_weighted_integrable a hn hg.continuous hφ hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  apply tendsto_integral_of_dominated_convergence
    (fun y ↦ φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) ?_ hi
  · intro i
    filter_upwards [] with y
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]
    apply mul_le_mul_of_nonneg_left _ (hφ0 _)
    exact (norm_inner_le_norm _ _).trans_eq (by rw [graphUnitNormalExtension_unit a hn,mul_one])
  · filter_upwards [] with y
    by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
    · have ht : Tendsto (fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
          (a+normalGraph n g y)) atTop (𝓝 (graphSlopeNormal n (gradient g y))) := by
        simp only [graphUnitNormalExtension_graph a hn]
        exact ((graphSlopeNormal_contDiff hn).continuous.tendsto _).comp
          (graphSmooth_gradient_tendsto hg (hc y hy))
      simpa only [graphAreaVector_inner_unit hn] using ((show Tendsto (fun _ : ℕ ↦ graphAreaVector n g y) atTop
        (𝓝 (graphAreaVector n g y)) from tendsto_const_nhds).inner ht).const_mul (φ (a+normalGraph n g y))
    · simp only [graph_trace_zero_outside hn hφR _ hy,zero_mul]
      exact tendsto_const_nhds
  · intro i
    exact (graph_weighted_continuous a hn hg.continuous hφ hφR (fun y hy ↦
      (graphAreaVector_continuousAt n (hc y hy)).inner
        (graph_trace_continuous a n hg.continuous
          (graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)).continuous).continuousAt)).aestronglyMeasurable

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_norm_le (n x : Cover) : ‖normalPlaneCoordinates n x‖ ≤ ‖x‖ := by
  simpa only [map_zero,dist_zero_right,NNReal.coe_one,one_mul] using
    (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0

lemma graph_weighted_normal_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {φ : Cover → ℝ} (hφR : tsupport φ ⊆ Metric.closedBall a R) (z : BlowupNormalBundle) :
    Tendsto (fun i ↦ φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n
      (graphSmooth (graphMollifier i) g) z.1⟫) atTop
      (𝓝 (φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫)) := by
  by_cases hz : z.1 ∈ tsupport φ
  · have hcoord : normalPlaneCoordinates n (z.1-a) ∈ Metric.closedBall (0 : Plane) R := by
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (normalPlaneCoordinates_norm_le n _).trans (by simpa [Metric.mem_closedBall,dist_eq_norm] using hφR hz)
    exact ((show Tendsto (fun _ : ℕ ↦ (z.2 : Cover)) atTop (𝓝 (z.2 : Cover)) from
      tendsto_const_nhds).inner (graphUnitNormalExtension_tendsto a hn hg (hc _ hcoord))).const_mul _
  · simp only [image_eq_zero_of_notMem_tsupport hz,zero_mul]
    exact tendsto_const_nhds

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalCoverMap
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

lemma continuous_normalCoverMap : Continuous normalCoverMap := by
  exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

lemma normalCoverMeasure_integral {μ : FiniteMeasure NormalBundle} {f : BlowupNormalBundle → ℝ}
    (hf : Continuous f) :
    (∫ z, f z ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z, f (normalCoverMap z) ∂(μ : Measure NormalBundle) := by
  rw [normalCoverMeasure,FiniteMeasure.toMeasure_map,
    integral_map continuous_normalCoverMap.measurable.aemeasurable hf.aestronglyMeasurable]

lemma normalMeasure_cutoff_saturation {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (O : Set Cover) : HasCutoffSaturation (normalCoverMeasure μ) O := by
  intro φ hφ hsφ hs hb C hC
  have hemass : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1
      ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z, φ (z.1 : Cover) ∂(μ : Measure NormalBundle) := by
    have hz : ∀ z : BlowupNormalBundle, z ∉ {z : BlowupNormalBundle | z.1 ∈ O} → φ z.1=0 :=
      fun z hz ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    exact normalCoverMeasure_integral (hφ.continuous.comp continuous_fst)
  rw [hemass]
  apply normalMeasure_weighted_saturation hμ
    ⟨fun z ↦ φ (z.1 : Cover),hφ.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  intro F hF
  have hFc : Continuous F := hF.1.continuous
  have heflux : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z : NormalBundle, φ (z.1 : Cover)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun (z : BlowupNormalBundle) hz ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h)),zero_mul])]
    exact normalCoverMeasure_integral (by fun_prop)
  change (∫ z : NormalBundle, φ (z.1 : Cover)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ C
  rw [← heflux]
  exact hC F hF.1 hF.2.2

lemma normalCoverMeasure_local_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0<x i ∧ x i<1}) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ x in quotientMap ⁻¹' E, divergence F x := by
  rw [normalCoverMeasure_integral (by fun_prop)]
  change (∫ z : NormalBundle, ⟪(z.2 : Cover), F (z.1 : Cover)⟫ ∂(μ : Measure NormalBundle)) = _
  rw [normalMeasure_local_flux hE hμ hF hc hs,← integral_indicator (hE.preimage measurable_quotientMap)]
  congr 1
  funext x
  classical
  by_cases hx : quotientMap x∈E <;> simp [characteristic,hx]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_weighted_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  have hiArea := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hiF (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),F z.1⟫) μ := by
    simpa only [mul_comm] using hiφ.bdd_mul
      (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) from by fun_prop).aestronglyMeasurable
      (ae_of_all μ fun z ↦ blowup_test_inner_bound hnF z)
  have hfield (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) ≤
        ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
    rw [show (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) = _ from
      blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
      (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).inner
        (graph_trace_continuous a n hg.continuous hF.continuous).continuousAt)) hiArea
    intro y
    apply mul_le_mul_of_nonneg_left _ (hφb _).1
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hnF _))
  refine le_antisymm ?_ ?_
  · exact hsat φ hφ hsφ hφO hφb _ hfield
  · apply le_of_tendsto (graph_area_trace_mollified_normal_tendsto a hn hg hc
      hφ.continuous hsφ hφR (fun x ↦ (hφb x).1))
    apply Eventually.of_forall
    intro i
    let F := graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
    have hnF (x : Cover) : ‖F x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
    rw [← blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (hiF F hF hnF) hiφ
    intro z
    apply mul_le_of_le_one_right (hφb _).1
    exact (real_inner_le_norm (z.2 : Cover) (F z.1)).trans (by rw [z.2.property,one_mul]; exact hnF _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_normal_ae {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O},
      0 < φ z.1 → (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let F : ℕ → Cover → Cover := fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
  let f : ℕ → BlowupNormalBundle → ℝ := fun i z ↦ φ z.1*⟪(z.2 : Cover),F i z.1⟫
  let f₀ : BlowupNormalBundle → ℝ := fun z ↦ φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫
  have hF (i) : ContDiff ℝ (⊤ : ℕ∞) (F i) := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
  have hFn (i) (x) : ‖F i x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
  have hf (i) : AEStronglyMeasurable (f i) μ :=
    (show Continuous (f i) from (hφ.continuous.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd |>.inner ((hF i).continuous.comp continuous_fst))).aestronglyMeasurable
  have ht : ∀ᵐ z ∂μ, Tendsto (fun i ↦ f i z) atTop (𝓝 (f₀ z)) :=
    ae_of_all μ (graph_weighted_normal_tendsto a hn hg hc hφR)
  have hb (i) (z : BlowupNormalBundle) : ‖f i z‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound (hFn i) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb₀ (z : BlowupNormalBundle) : ‖f₀ z‖ ≤ 1 := by
    dsimp only [f₀]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound
      (fun x ↦ (graphUnitNormalExtension_unit a hn _ x).le) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hi₀ : Integrable f₀ μ := Integrable.of_bound
    (aestronglyMeasurable_of_tendsto_ae atTop hf ht) 1 (ae_of_all μ hb₀)
  have hilim : Tendsto (fun i ↦ ∫ z, f i z ∂μ) atTop (𝓝 (∫ z, f₀ z ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ)) hf
      (integrable_const 1) (fun i ↦ ae_of_all μ (hb i)) ht
  have heint : (∫ z, f₀ z ∂μ) = ∫ z, φ z.1 ∂μ := by
    apply tendsto_nhds_unique hilim
    rw [show (∫ z, φ z.1 ∂μ) = _ from
      cutoff_graph_patch_weighted_mass hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb]
    have hh := graph_area_trace_mollified_normal_tendsto a hn hg hc hφ.continuous hsφ hφR
      (fun x ↦ (hφb x).1)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    exact blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb (hF i) (hFn i)
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb _).1]; exact (hφb _).2)
  have hinon (z : BlowupNormalBundle) : 0 ≤ φ z.1-f₀ z := by
    have hh : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ ≤ 1 := by
      exact (real_inner_le_norm _ _).trans_eq (by rw [z.2.property,graphUnitNormalExtension_unit a hn,one_mul])
    exact sub_nonneg.mpr (mul_le_of_le_one_right (hφb _).1 hh)
  have hezero : (∫ z, (φ z.1-f₀ z) ∂μ)=0 := by rw [integral_sub hiφ hi₀,heint,sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ hinon) (hiφ.sub hi₀)).mp hezero
  filter_upwards [hae] with z hz
  intro hzφ
  have hi : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ = 1 := by
    have hh : φ z.1*(1-⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫)=0 := by
      simpa only [mul_sub,mul_one,f₀,Pi.zero_apply] using hz
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hzφ.ne')).symm
  exact (inner_eq_one_iff_of_norm_eq_one z.2.property (graphUnitNormalExtension_unit a hn g z.1)).mp hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverEssentialBoundary_eq_support (A : Set Cover) :
    coverEssentialBoundary A = (volume.restrict A).support ∩ (volume.restrict Aᶜ).support := by
  ext p
  simp only [coverEssentialBoundary,Set.mem_ofPred_eq,Set.mem_inter_iff,
    Metric.nhds_basis_ball.mem_measureSupport,
    Measure.restrict_apply Metric.isOpen_ball.measurableSet,inter_comm,forall_and]
  constructor
  · rintro ⟨ha,hc⟩
    exact ⟨fun r hr ↦ (ENNReal.toReal_pos_iff).mp (ha r hr) |>.1,
      fun r hr ↦ (ENNReal.toReal_pos_iff).mp (hc r hr) |>.1⟩
  · rintro ⟨ha,hc⟩
    refine ⟨fun r hr ↦ ?_,fun r hr ↦ ?_⟩
    · exact ENNReal.toReal_pos_iff.mpr ⟨ha r hr,
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top⟩
    · exact ENNReal.toReal_pos_iff.mpr ⟨hc r hr,
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top⟩

lemma cover_boundary_preimage_image {A : Set Cover} {f : Cover → Cover} {p : Cover}
    (hq : Measure.QuasiMeasurePreserving f volume volume) (hf : ContinuousAt f p)
    (hp : p ∈ coverEssentialBoundary (f ⁻¹' A)) : f p ∈ coverEssentialBoundary A := by
  rw [coverEssentialBoundary_eq_support] at hp ⊢
  exact ⟨measureSupport_preimage_image hq hf hp.1,measureSupport_preimage_image hq hf hp.2⟩

lemma cover_boundary_measurePreserving_homeomorph {A : Set Cover} (f : Cover ≃ₜ Cover)
    (hq : MeasurePreserving f) (p : Cover) :
    p ∈ coverEssentialBoundary (f ⁻¹' A) ↔ f p ∈ coverEssentialBoundary A := by
  constructor
  · exact cover_boundary_preimage_image hq.quasiMeasurePreserving f.continuous.continuousAt
  · intro hp
    have hi : MeasurePreserving f.symm := MeasurePreserving.symm f.toMeasurableEquiv hq
    have hh := cover_boundary_preimage_image hi.quasiMeasurePreserving f.symm.continuous.continuousAt
      (A := f ⁻¹' A) (p := f p)
    have he : f.symm ⁻¹' (f ⁻¹' A) = A := by ext x; simp
    rw [he] at hh
    simpa only [f.symm_apply_apply] using hh hp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ConeSlopeReciprocalArea
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

lemma graph_superlevel_compl_ae {A U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : Continuous g)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ graphHeightExtension a n g x < ⟪n,x-a⟫)) :
    ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ Aᶜ ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x) := by
  have hnz : ∀ᵐ x : Cover ∂volume, ⟪n,x-a⟫ ≠ graphHeightExtension a n g x := by
    rw [ae_iff]
    simpa only [not_not] using graph_trace_volume_zero a hn hg
  filter_upwards [hgraph,hnz] with x hx hne hU
  rw [mem_compl_iff,hx hU,not_lt]
  exact ⟨fun h ↦ lt_of_le_of_ne h hne,le_of_lt⟩

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

lemma torusVolume_lift_ball {E : Set Torus} (hE : MeasurableSet E)
    (x : Cover) (t : ℝ) (ht : Metric.ball x t ⊆ {y | ∀ i, 0<y i ∧ y i<1}) :
    torusVolume.real (E∩Metric.ball (quotientMap x) t)=
      volume.real ((quotientMap ⁻¹' E)∩Metric.ball x t) := by
  have hh := integral_blowupCharacteristic_ball_center hE (0 : Cover) x
    (by norm_num : (0 : ℝ)<1) t (by simpa only [one_smul,zero_add,one_mul] using ht)
  simp only [one_smul,zero_add,one_mul,one_pow] at hh
  rw [hh,← cover_integral_indicator_ball (hE.preimage measurable_quotientMap)]
  congr 1
  funext y
  classical
  by_cases hy : quotientMap y∈E <;>
    simp [blowupCharacteristic,characteristic,hy]

lemma coverEssentialBoundary_lift_iff {E : Set Torus} (hE : MeasurableSet E)
    {x : Cover} (hx : ∀ i, 0<x i ∧ x i<1) :
    x∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
      quotientMap x∈volumeSupport E ∩ volumeSupport Eᶜ := by
  have hO : IsOpen {y : Cover | ∀ i, 0<y i ∧ y i<1} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).inter
        (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hx)
  have hs (t : ℝ) : Metric.ball x (min r t) ⊆ {y | ∀ i, 0<y i ∧ y i<1} :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hsub
  rw [mem_inter_iff,mem_volumeSupport_iff,mem_volumeSupport_iff]
  constructor
  · intro h
    constructor
    · intro t ht
      have hh := (h (min r t) (lt_min hr ht)).1
      rw [← torusVolume_lift_ball hE x (min r t) (hs t)] at hh
      exact hh.trans_le (measureReal_mono (μ := torusVolume)
        (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_right _ _))))
    · intro t ht
      have hh := (h (min r t) (lt_min hr ht)).2
      rw [← preimage_compl,← torusVolume_lift_ball hE.compl x (min r t) (hs t)] at hh
      exact hh.trans_le (measureReal_mono (μ := torusVolume)
        (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_right _ _))))
  · intro h t ht
    have h₁ := h.1 (min r t) (lt_min hr ht)
    have h₂ := h.2 (min r t) (lt_min hr ht)
    rw [torusVolume_lift_ball hE x (min r t) (hs t)] at h₁
    rw [torusVolume_lift_ball hE.compl x (min r t) (hs t),preimage_compl] at h₂
    have hmono (A : Set Cover) : volume.real (A∩Metric.ball x (min r t)) ≤
        volume.real (A∩Metric.ball x t) :=
      measureReal_mono (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_right _ _)))
    exact ⟨h₁.trans_le (hmono _),h₂.trans_le (hmono _)⟩

lemma isMinimizerAt_lifted_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {x : Cover} (hx : ∀ i, 0<x i ∧ x i<1) :
    x∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
      quotientMap x∈frontier (openRepresentative E) := by
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
  exact coverEssentialBoundary_lift_iff hE hx

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

lemma contDiff_local_vector_cutoff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} {η : Plane → ℝ} {S : Set Plane} {n : WithTop ℕ∞}
    (hS : IsOpen S) (hf : ContDiffOn ℝ n f S) (hη : ContDiff ℝ n η)
    (hs : tsupport η⊆S) : ContDiff ℝ n (fun y ↦ η y • f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.contDiffAt.smul ((hf y (hs hy)).contDiffAt (hS.mem_nhds (hs hy)))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TranslateNormal
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

theorem normalMeasure_graph_normal_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {R : ℝ}
    (hc : ∀ y∈Metric.closedBall (0 : Plane) R,ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
      (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
  have hflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1})
      (_hb : ∀ x,‖F x‖≤1) := normalCoverMeasure_local_flux hE hμ hF hs hO
  have h := cutoff_graph_patch_normal_ae (hE.preimage measurable_quotientMap) a hn hg hc
    hgraph (normalMeasure_cutoff_saturation hμ _) hflux hφ hsφ hφU hφO hφR hφb
  have hO : MeasurableSet {z : BlowupNormalBundle | ∀ i,0<z.1 i ∧ z.1 i<1} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun z : BlowupNormalBundle ↦ z.1 i) := by fun_prop
    exact (measurableSet_lt measurable_const hm).inter
      (measurableSet_lt hm measurable_const)
  have h' : ∀ᵐ z ∂(normalCoverMeasure μ : Measure BlowupNormalBundle),
      0<φ z.1 → (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
    have hh := (ae_restrict_iff' hO).mp h
    filter_upwards [hh] with z hz hpos
    exact hz (hφO (subset_tsupport _ (show φ z.1≠0 from hpos.ne'))) hpos
  have hm : (normalCoverMeasure μ : Measure BlowupNormalBundle)=
      Measure.map normalCoverMap (μ : Measure NormalBundle) := FiniteMeasure.toMeasure_map μ normalCoverMap
  rw [hm] at h'
  exact ae_of_ae_map continuous_normalCoverMap.measurable.aemeasurable h'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma translateNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (a : Cover) (z : NormalBundle) :
    F (translateNormal a z).1=F ((z.1 : Cover)-a) := by
  change F (representative (quotientMap z.1-quotientMap a))=F ((z.1 : Cover)-a)
  rw [← quotientMap_sub]
  exact periodic_representative hp _

theorem isNormalMeasure_translation {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (a : Cover) :
    IsNormalMeasure ((fun z ↦ z+quotientMap a) ⁻¹' E) (μ.map (translateNormal a)) := by
  constructor
  · have hm : ((μ.map (translateNormal a)).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_translateNormal a)
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_translation_measurable hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (translateNormal a) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_translateNormal a).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_translation hF a hE]
    have hG : AdmissibleField (fun x ↦ F (x-a)) := by
      simpa only [sub_eq_add_neg] using admissible_translate hF (-a)
    rw [← hμ.2 _ hG]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      change ⟪(z.2 : Cover),F (translateNormal a z).1⟫=⟪(z.2 : Cover),F ((z.1 : Cover)-a)⟫
      rw [translateNormal_periodic_eval hF.2.1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_graph_extension {g : Plane → ℝ} {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ EqOn f g (Metric.ball 0 (R/2)) := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  refine ⟨fun y ↦ b y*g y,?_,?_⟩
  · exact contDiff_local_vector_cutoff Metric.isOpen_ball hg b.contDiff hs
  · intro y hy
    change b y*g y=g y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_GraphInverseMetric
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

theorem actual_centered_normal_graph_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (cubeCenter+normalGraph n f y)=
        σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,_,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,hf,hfg⟩ := smooth_graph_extension hr hgc
  have hcover' (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x ((Metric.ball_subset_ball (by linarith)) hx)
  obtain ⟨R,ρ,U,hRr,_,_,_,hR,hρ,hgC,hU,hρU,hUR,hUO,_,hphase⟩ :=
    actual_centered_graph_phase_patch hV hE hmin hcenter hn (by linarith : 0 < r/2)
      hg hg0 ((hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))) hcover'
  let φ := radialHeightCutoff cubeCenter ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hρU
  have hφO := hφU.trans hUO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  have hdc (y : Plane) (hy : y∈Metric.closedBall (0 : Plane) R) : ContinuousAt (fderiv ℝ g) y :=
    (hgC y hy).continuousAt_fderiv (by norm_num)
  have hNfg (x : Cover) (hx : x∈tsupport φ) :
      graphUnitNormalExtension cubeCenter n f x=graphUnitNormalExtension cubeCenter n g x := by
    have hpp : normalPlaneCoordinates n (x-cubeCenter)∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right]
      have hnorm : ‖x-cubeCenter‖<R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hUR (hφU hx)
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt (hnorm.trans hRr)
    have he : f=ᶠ[𝓝 (normalPlaneCoordinates n (x-cubeCenter))]g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hpp] with y hy
      exact hfg hy
    simp only [graphUnitNormalExtension,gradient,he.fderiv_eq]
  have hsign : ∃ σ : ℝ,(σ=1 ∨ σ= -1) ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
        σ • graphUnitNormalExtension cubeCenter n f z.1=(z.2 : Cover) := by
    rcases hphase with hphase|hphase
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (quotientMap x∈E ↔ ⟪n,x-cubeCenter⟫<graphHeightExtension cubeCenter n g x) := by
        simpa only [graphSignedHeight,sub_neg] using hphase
      refine ⟨1,Or.inl rfl,?_⟩
      filter_upwards [normalMeasure_graph_normal_ae hE hμ cubeCenter hn hg hdc hh
        hφ hsφ hφU hφO hφR hφb] with z hz hpos
      rw [one_smul,hNfg _ (subset_tsupport _ hpos.ne')]
      exact (hz hpos).symm
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (x∈quotientMap ⁻¹' E ↔ graphHeightExtension cubeCenter n g x<⟪n,x-cubeCenter⟫) := by
        simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
      have hh' := graph_superlevel_compl_ae cubeCenter hn hg.continuous hh
      have hh'' := normalMeasure_graph_normal_ae hE.compl (isNormalMeasure_compl hE hμ)
        cubeCenter hn hg hdc hh' hφ hsφ hφU hφO hφR hφb
      have hm : ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
          -(z.2 : Cover)=graphUnitNormalExtension cubeCenter n g z.1 :=
        ae_of_ae_map continuous_reverseNormal.measurable.aemeasurable hh''
      refine ⟨-1,Or.inr rfl,?_⟩
      filter_upwards [hm] with z hz hpos
      rw [neg_one_smul,hNfg _ (subset_tsupport _ hpos.ne'),← hz hpos,neg_neg]
  obtain ⟨σ,hσ,hσae⟩ := hsign
  let F : Cover → Cover := fun x ↦ φ x • (σ • graphUnitNormalExtension cubeCenter n f x)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hφ.smul
    ((graphUnitNormalExtension_contDiff _ hn hf).const_smul σ)
  have hsF : HasCompactSupport F := hsφ.smul_right
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    (tsupport_smul_subset_left _ _).trans hφO
  have he := latticePeriodize_eventuallyEq hsF hFO
    (show ∀ i,0 ≤ cubeCenter i ∧ cubeCenter i≤1 by intro i; norm_num [cubeCenter])
  have heφ := latticePeriodize_eventuallyEq hsφ hφO
    (show ∀ coordinate,0 ≤ cubeCenter coordinate ∧ cubeCenter coordinate≤1 by
      intro coordinate
      norm_num [cubeCenter])
  have hz : ∀ᵐ z ∂(μ : Measure NormalBundle),
      latticePeriodize φ z.1 • N z.1=latticePeriodize F z.1 := by
    filter_upwards [hae,hσae] with z hz hloc
    rw [(latticePeriodize_eventuallyEq hsφ hφO (compactCell_coordinates z.1)).eq_of_nhds,
      (latticePeriodize_eventuallyEq hsF hFO (compactCell_coordinates z.1)).eq_of_nhds]
    change φ z.1 • N z.1=φ z.1 • (σ • graphUnitNormalExtension cubeCenter n f z.1)
    by_cases hpos : 0<φ z.1
    · rw [hz,hloc hpos]
    · have hzφ : φ z.1=0 := le_antisymm (le_of_not_gt hpos) (hφb z.1).1
      simp only [hzφ,zero_smul]
  have hb (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      latticePeriodize φ x • N x=latticePeriodize F x :=
    isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      ((latticePeriodize_contDiff hφ hsφ).continuous.smul hN.continuous)
      (latticePeriodize_contDiff hF hsF).continuous
      (fun shift point ↦ congrArg₂ (· • ·)
        (latticePeriodize_periodic φ shift point) (hp shift point))
      (latticePeriodize_periodic F) hz x hx
  have hf0 : f 0=0 := (hfg (by simpa using (half_pos hr))).trans hg0
  have ht : Tendsto (fun y ↦ cubeCenter+normalGraph n f y) (𝓝 (0 : Plane)) (𝓝 cubeCenter) := by
    have hc : Continuous (fun y ↦ cubeCenter+normalGraph n f y) :=
      continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
        (hf.continuous.smul continuous_const))
    have hz : cubeCenter+normalGraph n f 0=cubeCenter := by
      simp only [normalGraph,hf0,zero_smul,add_zero]
      change cubeCenter+(normalPlaneLinearIsometry n) 0=cubeCenter
      rw [map_zero,add_zero]
    simpa only [ContinuousAt,hz] using hc.continuousAt (x := 0)
  have hone : ∀ᶠ x in 𝓝 cubeCenter,φ x=1 := by
    filter_upwards [Metric.ball_mem_nhds cubeCenter hρ] with x hx
    exact radialHeightCutoff_one hρ (Metric.ball_subset_closedBall hx)
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_⟩
  ·
    filter_upwards [ht.eventually he,ht.eventually heφ,ht.eventually hone,
      Metric.ball_mem_nhds (0 : Plane) (half_pos hr)] with y hey heφy hoy hy
    have hgraph : normalGraph n f y=normalGraph n g y := by simp only [normalGraph,hfg hy]
    have hby : quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E) := by
      rw [quotientMap_add,hgraph]
      exact hi y ((Metric.ball_subset_ball (by linarith)) hy)
    have hnormal := hb _ hby
    rw [heφy,hey] at hnormal
    change φ (cubeCenter+normalGraph n f y) • N (cubeCenter+normalGraph n f y)=
      φ (cubeCenter+normalGraph n f y) • (σ • graphUnitNormalExtension cubeCenter n f
        (cubeCenter+normalGraph n f y)) at hnormal
    simp only [hoy,one_smul,graphUnitNormalExtension_graph cubeCenter hn f f y] at hnormal
    exact ⟨hnormal,hby⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Cover) (half_pos hr)] with v hv
    have hpv : normalPlaneCoordinates n v∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right] at hv ⊢
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt hv
    rw [hcover' v hv]
    simp only [normalGraph,hfg hpv]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_graph_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (x+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [← quotientMap_add]
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [a]
    congr 1
    abel
  let N' : Cover → Cover := fun y ↦ N (y+a)
  have hN' : ContDiff ℝ (⊤ : ℕ∞) N' := hN.comp (contDiff_id.add contDiff_const)
  have hp' : ∀ m y,N' (y+latticeVector m)=N' y := by
    intro m y
    change N ((y+latticeVector m)+a)=N (y+a)
    rw [add_right_comm,hp]
  have hae' : ∀ᵐ z ∂((μ.map (translateNormal a)) : Measure NormalBundle),N' z.1=(z.2 : Cover) := by
    change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),N' z.1=(z.2 : Cover)
    apply (ae_map_iff (measurable_translateNormal a).aemeasurable
      (isClosed_eq (hN'.continuous.comp normalEmbedding_continuous.fst) continuous_normalUnit).measurableSet).mpr
    filter_upwards [hae] with z hz
    change N' (translateNormal a z).1=(z.2 : Cover)
    rw [translateNormal_periodic_eval hp']
    change N (((z.1 : Cover)-a)+a)=(z.2 : Cover)
    simpa only [sub_add_cancel] using hz
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm,hcov⟩ := actual_centered_normal_graph_chart hV hE' hmin' hc
    (isNormalMeasure_translation hE hμ a) hN' hp' hae'
  have ht (v : Cover) : (cubeCenter+v)+a=x+v := by dsimp [a]; abel
  have htrans (v : Cover) : quotientMap (cubeCenter+v)∈frontier (openRepresentative E') ↔
      quotientMap (x+v)∈frontier (openRepresentative E) := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap (cubeCenter+v)+quotientMap a∈frontier (openRepresentative E) ↔ _
    rw [← quotientMap_add,ht]
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_⟩
  · filter_upwards [hm] with y hy
    refine ⟨?_,(htrans _).mp hy.2⟩
    have hh := hy.1
    change N ((cubeCenter+normalGraph n f y)+a)=_ at hh
    rwa [ht] at hh
  · filter_upwards [hcov] with v hv
    exact (htrans v).symm.trans hv

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

theorem exists_periodic_smooth_separator {A B : Set Torus} (hA : IsCompact A)
    (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ φ : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ m x,φ (x+latticeVector m)=φ x) ∧
      (∀ x,φ x∈Icc 0 1) ∧
      (∀ x,quotientMap x∈A → ∀ᶠ y in 𝓝 x,φ y=1) ∧
      (∀ x,quotientMap x∈B → ∀ᶠ y in 𝓝 x,φ y=0) := by
  classical
  have hcut (a : A) := exists_periodic_local_cutoff a.1 hB.isOpen_compl
    (show a.1∈Bᶜ from fun hb ↦ Set.disjoint_left.mp hAB a.2 hb)
  choose φ hφ hp hb hW0 hzero using hcut
  choose W hW hWa hone using hW0
  obtain ⟨s,hs⟩ := hA.elim_finite_subcover W hW (fun a ha ↦ mem_iUnion.mpr ⟨⟨a,ha⟩,hWa ⟨a,ha⟩⟩)
  let ψ : Cover → ℝ := fun x ↦ 1-∏ a∈s,(1-φ a x)
  refine ⟨ψ,contDiff_const.sub (contDiff_prod (fun a _ ↦ contDiff_const.sub (hφ a))),?_,?_,?_,?_⟩
  · intro m x
    simp only [ψ,hp]
  · intro x
    have hn : 0≤∏ a∈s,(1-φ a x) := Finset.prod_nonneg fun a _ ↦ sub_nonneg.mpr (hb a x).2
    have hu : (∏ a∈s,(1-φ a x))≤1 := Finset.prod_le_one (fun a _ ↦ sub_nonneg.mpr (hb a x).2)
      (fun a _ ↦ by linarith [(hb a x).1])
    exact ⟨by dsimp [ψ]; linarith,by dsimp [ψ]; linarith⟩
  · intro x hx
    obtain ⟨a,has,hxa⟩ := mem_iUnion₂.mp (hs hx)
    filter_upwards [hone a x hxa] with y hy
    dsimp [ψ]
    rw [Finset.prod_eq_zero has (by rw [hy,sub_self]),sub_zero]
  · intro x hx
    have hn : ∀ᶠ y in 𝓝 x,∀ a∈s,φ a y=0 := by
      apply (eventually_all_finite s.finite_toSet).mpr
      intro a ha
      exact hzero a x (by simpa using hx)
    filter_upwards [hn] with y hy
    dsimp [ψ]
    have he : (∏ a∈s,(1-φ a y))=1 := Finset.prod_eq_one (fun a ha ↦ by rw [hy a ha,sub_zero])
    rw [he,sub_self]

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SurfaceJet
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

lemma surfaceJacobiB_symm (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ) :
    surfaceJacobiB μ q u v=surfaceJacobiB μ q v u := by
  have he : ⟪surfaceMultiplier μ q u.1,v.1⟫=⟪surfaceMultiplier μ q v.1,u.1⟫ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_lpSMul (r := 2) q u.1,Lp.coeFn_lpSMul (r := 2) q v.1] with z hu hv
    change (q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z = _ at hu
    change (q • v.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z = _ at hv
    change ⟪(q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z,v.1 z⟫ =
      ⟪(q • v.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z,u.1 z⟫
    rw [hu,hv]
    simp only [smul_eq_mul,Pi.mul_apply,RCLike.inner_apply,RCLike.conj_to_real]
    ring
  unfold surfaceJacobiB
  rw [he,real_inner_comm u.2 v.2]

lemma surfaceJacobiB_add_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v w : SurfaceJet μ) :
    surfaceJacobiB μ q (u+v) w=surfaceJacobiB μ q u w+surfaceJacobiB μ q v w := by
  simp only [surfaceJacobiB,Prod.fst_add,Prod.snd_add,map_add,inner_add_left]
  ring

lemma surfaceJacobiB_smul_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (c : ℝ) (u v : SurfaceJet μ) :
    surfaceJacobiB μ q (c • u) v=c*surfaceJacobiB μ q u v := by
  change ⟪c • u.2,v.2⟫-⟪surfaceMultiplier μ q (c • u.1),v.1⟫ =
    c*(⟪u.2,v.2⟫-⟪surfaceMultiplier μ q u.1,v.1⟫)
  simp only [map_smul,real_inner_smul_left]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceMean_of_smooth (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    surfaceMean μ (surfaceSmoothJet μ f)=(∫ z,f.val z.1 ∂(μ : Measure NormalBundle)) := by
  change ⟪(ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue smoothScalarOne),
    (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue f)⟫=_
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change f.val z.1 * (starRingEnd ℝ) 1=f.val z.1
  simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_gradient_mul {f g : Cover → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : Cover) :
    gradient (f*g) x=g x • gradient f x+f x • gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    inner_gradient_left,inner_gradient_left]
  rw [fderiv_mul (hf x) (hg x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma smoothScalarGradient_mul (f g : smoothPeriodicScalars) (z : NormalBundle) :
    smoothScalarGradient (smoothScalarMul f g) z=
      g.val z.1 • smoothScalarGradient f z+f.val z.1 • smoothScalarGradient g z := by
  change gradient (f.val*g.val) z.1-⟪(z.2 : Cover),gradient (f.val*g.val) z.1⟫ • (z.2 : Cover)=_
  rw [cover_gradient_mul (f.property.1.differentiable (by simp)) (g.property.1.differentiable (by simp)),
    inner_add_right,real_inner_smul_right,real_inner_smul_right,add_smul]
  change _=g.val z.1 • (gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))+
    f.val z.1 • (gradient g.val z.1-⟪(z.2 : Cover),gradient g.val z.1⟫ • (z.2 : Cover))
  simp only [smul_sub,smul_smul]
  abel

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalComponentScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) (x : Cover) :
    (normalComponentScalar N hN hp i).val x=N x i := by
  simp only [normalComponentScalar,EuclideanSpace.inner_single_left,conj_trivial,one_mul]

lemma normalComponentScalar_mean_zero {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3) :
    surfaceMean μ (surfaceSmoothJet μ (normalComponentScalar N hN hp i))=0 := by
  let e : Cover := EuclideanSpace.single i 1
  have he : ‖e‖=1 := by simp [e]
  have hF : AdmissibleField (fun _ : Cover ↦ e) := ⟨contDiff_const,fun _ _ ↦ rfl,fun _ ↦ he.le⟩
  have hflux := hμ.2 _ hF
  have hd : divergence (fun _ : Cover ↦ e)=fun _ ↦ 0 := by funext x; simp [divergence]
  rw [hd,integral_zero] at hflux
  rw [surfaceMean_of_smooth,← hflux]
  apply integral_congr_ae
  filter_upwards [hae] with z hz
  change ⟪e,N z.1⟫=⟪(z.2 : Cover),e⟫
  rw [hz,real_inner_comm]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_NormalCurvatureScalar
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

lemma smoothTransition_deriv_zero_neg {t : ℝ} (ht : t<0) : deriv Real.smoothTransition t=0 := by
  have he : Real.smoothTransition=ᶠ[𝓝 t] (fun _ ↦ (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos hs.le
  rw [he.deriv_eq]
  simp

lemma smoothTransition_deriv_zero_gt {t : ℝ} (ht : 1<t) : deriv Real.smoothTransition t=0 := by
  have he : Real.smoothTransition=ᶠ[𝓝 t] (fun _ ↦ (1:ℝ)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le hs.le
  rw [he.deriv_eq]
  simp

lemma positiveTruncCoeff_zero {t : ℝ} (ht : t≤0) : positiveTruncCoeff t=0 := by
  rcases ht.eq_or_lt with rfl|ht
  · simp [positiveTruncCoeff]
  · simp [positiveTruncCoeff,Real.smoothTransition.zero_of_nonpos ht.le,smoothTransition_deriv_zero_neg ht]

lemma positiveTruncCoeff_one {t : ℝ} (ht : 1<t) : positiveTruncCoeff t=1 := by
  simp [positiveTruncCoeff,Real.smoothTransition.one_of_one_le ht.le,smoothTransition_deriv_zero_gt ht]

lemma positiveTruncCoeff_bounded : ∃ K : ℝ,0≤K ∧ ∀ t,‖positiveTruncCoeff t‖≤K := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition).continuous_deriv (by simp)
  have hc : Continuous positiveTruncCoeff := Real.smoothTransition.continuous.add (continuous_id.mul hd)
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max (max M 1) 0,le_max_right _ _,?_⟩
  intro t
  by_cases ht : t∈Icc (-1:ℝ) 2
  · exact (hM t ht).trans ((le_max_left M 1).trans (le_max_left _ _))
  · rcases lt_or_gt_of_ne (show t≠(-1:ℝ) by intro he; subst t; exact ht (by norm_num)) with hlt|hgt
    · rw [positiveTruncCoeff_zero (by linarith),norm_zero]
      exact le_max_right _ _
    · have htwo : 2<t := lt_of_not_ge (fun h ↦ ht ⟨hgt.le,h⟩)
      rw [positiveTruncCoeff_one (by linarith),norm_one]
      exact (le_max_right M 1).trans (le_max_left _ _)

lemma positiveTrunc_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (positiveTrunc n) (positiveTruncCoeff (((n:ℝ)+1)*t)) t := by
  have hS := (Real.smoothTransition.contDiff : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition).differentiable (by simp)
  have h := (hasDerivAt_id t).mul ((hS _).hasDerivAt.comp t ((hasDerivAt_id t).const_mul ((n:ℝ)+1)))
  have he : 1*(Real.smoothTransition ∘ fun y : ℝ ↦ ((n:ℝ)+1)*id y) t+
      id t*(deriv Real.smoothTransition (((n:ℝ)+1)*id t)*(((n:ℝ)+1)*1))=
      positiveTruncCoeff (((n:ℝ)+1)*t) := by
    dsimp [positiveTruncCoeff]
    ring
  rw [he] at h
  exact h

lemma positiveTrunc_bound (n : ℕ) (t : ℝ) : ‖positiveTrunc n t‖≤‖t‖ := by
  rw [positiveTrunc,norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceL2_bounded_convergence {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    (μ : FiniteMeasure NormalBundle) (f : ℕ → NormalBundle → F)
    (g : NormalBundle → F) (hf : ∀ n,MemLp (f n) 2 (μ : Measure NormalBundle))
    (hg : MemLp g 2 (μ : Measure NormalBundle)) {M : ℝ} (hM : 0≤M)
    (hfb : ∀ n,∀ᵐ z ∂(μ : Measure NormalBundle),‖f n z‖≤M)
    (hgb : ∀ᵐ z ∂(μ : Measure NormalBundle),‖g z‖≤M)
    (ht : ∀ᵐ z ∂(μ : Measure NormalBundle),Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have he (n : ℕ) : ‖(hf n).toLp (f n)-hg.toLp g‖^2=
      ∫ z,‖f n z-g z‖^2 ∂(μ : Measure NormalBundle) := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp,hg.coeFn_toLp] with z hsub hfz hgz
    rw [hsub,Pi.sub_apply,hfz,hgz,real_inner_self_eq_norm_sq]
  have hi : Tendsto (fun n ↦ ∫ z,‖f n z-g z‖^2 ∂(μ : Measure NormalBundle)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ : NormalBundle ↦ (0:ℝ)) (fun _ : NormalBundle ↦ (2*M)^2)
      (fun n ↦ (((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2))
      (integrable_const _) ?_ ?_
    · simpa using h
    · intro n
      filter_upwards [hfb n,hgb] with z hfz hgz
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb : ‖f n z-g z‖≤2*M := (norm_sub_le _ _).trans (by linarith)
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hM)).2 hb
    · filter_upwards [ht] with z hz
      simpa using (((hz.sub (tendsto_const_nhds (x := g z))).norm).pow 2)
  have hn : Tendsto (fun n ↦ ‖(hf n).toLp (f n)-hg.toLp g‖) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n ↦ ‖(hf n).toLp (f n)-hg.toLp g‖^2) atTop (𝓝 0) := by
      simpa only [he] using hi
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma directionalNormalScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (v x : Cover) :
    (directionalNormalScalar N hN hp v).val x=⟪v,N x⟫ := by
  simp only [directionalNormalScalar,Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,normalComponentScalar_apply,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma surfaceJacobiB_sum_left {ι : Type*} (s : Finset ι)
    (μ : FiniteMeasure NormalBundle) (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (u : ι → SurfaceJet μ) (w : SurfaceJet μ) :
    surfaceJacobiB μ q (∑ i∈s,u i) w=∑ i∈s,surfaceJacobiB μ q (u i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [surfaceJacobiB]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,surfaceJacobiB_add_left,ih]

lemma directionalNormalScalar_global_jacobi (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,
      surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
        (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0) (v : Cover) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp v)) w=0 := by
  intro w hw
  simp only [directionalNormalScalar,map_sum,map_smul,surfaceJacobiB_sum_left,
    surfaceJacobiB_smul_left,hj _ w hw,mul_zero,Finset.sum_const_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma locallyConnected_of_quotient_graphs (S : Set Torus)
    (hchart : ∀ a∈S,∃ (x : Cover) (G : Plane → Cover) (P : Cover →L[ℝ] Plane),
      quotientMap x=a ∧ Continuous G ∧ G 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),quotientMap (x+G y)∈S) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v) :
    LocallyConnectedSpace S := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro a U hU
  obtain ⟨T,hT,hTU⟩ := (mem_nhds_subtype S a U).mp hU
  obtain ⟨x,G,P,hx,hG,hG0,hGS,hGP⟩ := hchart a a.property
  let F : Plane → Torus := fun y ↦ quotientMap (x+G y)
  have hF : Continuous F := continuous_quotientMap.comp (continuous_const.add hG)
  have hF0 : F 0=a := by simp [F,hG0,hx]
  have hFT : ∀ᶠ y in 𝓝 (0 : Plane),F y∈T := by
    have ht : Tendsto F (𝓝 (0 : Plane)) (𝓝 (a : Torus)) := by
      simpa only [hF0] using hF.tendsto (0 : Plane)
    exact ht.eventually hT
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hGS.and hFT)
  let B : Set Torus := F '' Metric.ball 0 r
  have hBS : B⊆S := by rintro b ⟨y,hy,rfl⟩; exact (hrsub hy).1
  have hBT : B⊆T := by rintro b ⟨y,hy,rfl⟩; exact (hrsub hy).2
  have hBc : IsPreconnected B := (convex_ball (0 : Plane) r).isPreconnected.image F hF.continuousOn
  refine ⟨Subtype.val ⁻¹' B,?_,?_,fun b hb ↦ hTU (hBT hb)⟩
  · have hP : ∀ᶠ v in 𝓝 (0 : Cover),P v∈Metric.ball 0 r := by
      have hp : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
        simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
      exact hp.eventually (Metric.ball_mem_nhds _ hr)
    obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (hGP.and hP)
    apply (mem_nhds_subtype S a _).mpr
    refine ⟨Metric.ball (a : Torus) δ,Metric.ball_mem_nhds _ hδ,?_⟩
    intro b hb
    have hb' : b.val∈Metric.ball (quotientMap x) δ := by change b.val∈Metric.ball (a : Torus) δ at hb; simpa only [hx] using hb
    rw [← quotientMap_image_ball x δ] at hb'
    obtain ⟨y,hy,hyb⟩ := hb'
    have hy' : y-x∈Metric.ball (0 : Cover) δ := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hy
    obtain ⟨hg,hp⟩ := hδsub hy'
    have hxs : quotientMap (x+(y-x))∈S := by simpa only [add_sub_cancel,hyb] using b.property
    have hid := hg hxs
    exact ⟨P (y-x),hp,by simp only [F,hid,add_sub_cancel,hyb]⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have he : (Subtype.val : S → Torus) '' (Subtype.val ⁻¹' B)=B := by
      ext b
      constructor
      · rintro ⟨c,hc,rfl⟩; exact hc
      · intro hb; exact ⟨⟨b,hBS hb⟩,hb,rfl⟩
    rwa [he]

theorem isMinimizerAt_boundary_locallyConnected {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    LocallyConnectedSpace (frontier (openRepresentative E)) := by
  obtain ⟨μ,H,N,hN,hp,hμ,hae,_⟩ := Periodic.isMinimizerAt_H1_translation_jacobi hV hE hmin
  apply locallyConnected_of_quotient_graphs
  intro a ha
  let x := representative a
  have hx : quotientMap x=a := quotientMap_representative a
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hgraph,hcover⟩ := isMinimizerAt_normal_graph_chart
    hV hE hmin hμ hN hp hae x (by rwa [hx])
  refine ⟨x,normalGraph n f,normalPlaneCoordinates n,hx,?_,?_,?_,?_⟩
  · unfold normalGraph
    exact (normalPlaneLinearIsometry n).continuous.add (hf.continuous.smul continuous_const)
  · change normalPlaneLinearIsometry n 0+f 0 • n=0
    simp [hf0]
  · exact hgraph.mono (fun y hy ↦ hy.2)
  · exact hcover.mono (fun v hv ↦ hv.mp)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma nodalEpsilon_pos (n : ℕ) : 0<nodalEpsilon n := by unfold nodalEpsilon; positivity

lemma separatedPositiveTrunc_zero (n : ℕ) {t : ℝ} (ht : t≤nodalEpsilon n) :
    separatedPositiveTrunc n t=0 ∧ positiveTruncCoeff (((n:ℝ)+1)*(t-nodalEpsilon n))=0 := by
  have hh : ((n:ℝ)+1)*(t-nodalEpsilon n)≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ht)
  exact ⟨by simp [separatedPositiveTrunc,positiveTrunc,Real.smoothTransition.zero_of_nonpos hh],
    positiveTruncCoeff_zero hh⟩

lemma separatedPositiveTrunc_bound (n : ℕ) (t : ℝ) : ‖separatedPositiveTrunc n t‖≤‖t‖ := by
  by_cases ht : t≤nodalEpsilon n
  · rw [(separatedPositiveTrunc_zero n ht).1,norm_zero]
    exact norm_nonneg _
  · have he := nodalEpsilon_pos n
    exact (positiveTrunc_bound n (t-nodalEpsilon n)).trans (by
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by linarith : 0<t-nodalEpsilon n),
        abs_of_pos (by linarith : 0<t)]
      linarith)

lemma separatedPositiveTrunc_tendsto (t : ℝ) :
    Tendsto (fun n ↦ separatedPositiveTrunc n t) atTop (𝓝 (max t 0)) ∧
    ∀ᶠ n : ℕ in atTop,positiveTruncCoeff (((n:ℝ)+1)*(t-nodalEpsilon n))=(if 0<t then 1 else 0) := by
  by_cases ht : 0<t
  · have hn : Tendsto (fun n : ℕ ↦ ((n:ℝ)+1)*t) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const ht
    have he (n : ℕ) : ((n:ℝ)+1)*(t-nodalEpsilon n)=((n:ℝ)+1)*t-1 := by
      rw [nodalEpsilon,mul_sub,mul_inv_cancel₀ (by positivity : (n:ℝ)+1≠0)]
    have hc : ∀ᶠ n : ℕ in atTop,1<((n:ℝ)+1)*(t-nodalEpsilon n) := by
      filter_upwards [hn.eventually (eventually_gt_atTop 2)] with n hn
      rw [he]
      linarith
    refine ⟨?_,?_⟩
    · have hε : Tendsto nodalEpsilon atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
      have hl : Tendsto (fun n ↦ t-nodalEpsilon n) atTop (𝓝 (max t 0)) := by
        simpa [max_eq_left ht.le] using tendsto_const_nhds.sub hε
      apply hl.congr'
      filter_upwards [hc] with n hn
      simp [separatedPositiveTrunc,positiveTrunc,Real.smoothTransition.one_of_one_le hn.le]
    · filter_upwards [hc] with n hn
      simp [positiveTruncCoeff_one hn,ht]
  · have hz (n : ℕ) := separatedPositiveTrunc_zero n (le_trans (not_lt.mp ht) (nodalEpsilon_pos n).le)
    refine ⟨?_,?_⟩
    · simpa only [(hz _).1,max_eq_right (not_lt.mp ht)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
    · filter_upwards [] with n
      simp only [(hz n).2,ite_eq_right ht]

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SmoothScalarSeparatedTrunc
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

lemma gradient_separatedPositiveTrunc (f : smoothPeriodicScalars) (n : ℕ) (x : Cover) :
    gradient (smoothScalarSeparatedTrunc f n).val x=
      positiveTruncCoeff (((n:ℝ)+1)*(f.val x-nodalEpsilon n)) • gradient f.val x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  have h := (positiveTrunc_hasDerivAt n (f.val x-nodalEpsilon n)).hasFDerivAt.comp x
    ((f.property.1.differentiable (by simp) x).hasFDerivAt.sub_const (nodalEpsilon n))
  change (fderiv ℝ (positiveTrunc n ∘ fun y ↦ f.val y-nodalEpsilon n) x) v=_
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,mul_comm]

lemma smoothScalarGradient_separatedPositiveTrunc (f : smoothPeriodicScalars) (n : ℕ) (z : NormalBundle) :
    smoothScalarGradient (smoothScalarSeparatedTrunc f n) z=
      positiveTruncCoeff (((n:ℝ)+1)*(f.val z.1-nodalEpsilon n)) • smoothScalarGradient f z := by
  change gradient (smoothScalarSeparatedTrunc f n).val z.1-
    ⟪(z.2 : Cover),gradient (smoothScalarSeparatedTrunc f n).val z.1⟫ • (z.2 : Cover)=_
  rw [gradient_separatedPositiveTrunc,real_inner_smul_right]
  change _=positiveTruncCoeff (((n:ℝ)+1)*(f.val z.1-nodalEpsilon n)) •
    (gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))
  rw [smul_sub,smul_smul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothScalarGradient_of_constant_germ (f : smoothPeriodicScalars) {x : Cover} {c : ℝ}
    (hf : ∀ᶠ y in 𝓝 x,f.val y=c) (ν : NormalSphere) :
    gradient f.val x-⟪(ν : Cover),gradient f.val x⟫ • (ν : Cover)=0 := by
  have he : f.val=ᶠ[𝓝 x] fun _ ↦ c := hf
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hg : gradient f.val x=0 := by simp [gradient,hd]
  simp [hg]

theorem nodal_restriction_smooth_approximants (f : smoothPeriodicScalars)
    (S D : Set Torus)
    (hA : ∀ n : ℕ,IsCompact {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)})
    (hB : ∀ n : ℕ,IsClosed {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}) :
    ∃ g : ℕ → smoothPeriodicScalars,∀ n (z : NormalBundle),normalProjection z∈S →
      (smoothScalarValue (g n) z=
        (normalProjection ⁻¹' D).indicator (fun w : NormalBundle ↦ separatedPositiveTrunc n (f.val w.1)) z) ∧
      (smoothScalarGradient (g n) z=
        (normalProjection ⁻¹' D).indicator (fun w : NormalBundle ↦
          positiveTruncCoeff (((n:ℝ)+1)*(f.val w.1-nodalEpsilon n)) • smoothScalarGradient f w) z) := by
  classical
  have hsep (n : ℕ) := exists_periodic_smooth_separator (hA n) (hB n)
    (show Disjoint {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)}
      {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)} from
        Set.disjoint_left.mpr (fun a ha hb ↦ hb.2.1 ha.2.1))
  choose φ hφ hp hb hone hzero using hsep
  let φs (n : ℕ) : smoothPeriodicScalars := ⟨φ n,hφ n,hp n⟩
  let g (n : ℕ) := smoothScalarMul (φs n) (smoothScalarSeparatedTrunc f n)
  refine ⟨g,?_⟩
  intro n z hz
  have hv : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 z.1
  have hgrad : smoothScalarGradient (g n) z=
      separatedPositiveTrunc n (f.val z.1) • smoothScalarGradient (φs n) z+
      φ n z.1 • (positiveTruncCoeff (((n:ℝ)+1)*(f.val z.1-nodalEpsilon n)) • smoothScalarGradient f z) := by
    rw [smoothScalarGradient_mul,smoothScalarGradient_separatedPositiveTrunc]
    rfl
  have hval : smoothScalarValue (g n) z=φ n z.1*separatedPositiveTrunc n (f.val z.1) := rfl
  by_cases hl : f.val z.1≤nodalEpsilon n
  · obtain ⟨ht,hc⟩ := separatedPositiveTrunc_zero n hl
    rw [hval,hgrad,ht,hc]
    constructor <;> by_cases hd : normalProjection z∈D <;> simp [hd,ht,hc]
  · have ha : nodalEpsilon n≤f.val (representative (normalProjection z)) := by rw [hv]; exact (not_le.mp hl).le
    by_cases hd : normalProjection z∈D
    · have hh := hone n (z.1 : Cover) ⟨hz,hd,ha⟩
      have hφv : φ n z.1=1 := hh.self_of_nhds
      have hφg : smoothScalarGradient (φs n) z=0 :=
        smoothScalarGradient_of_constant_germ (φs n) hh z.2
      rw [hval,hgrad,hφv,hφg]
      constructor <;> simp [hd]
    · have hh := hzero n (z.1 : Cover) ⟨hz,hd,ha⟩
      have hφv : φ n z.1=0 := hh.self_of_nhds
      have hφg : smoothScalarGradient (φs n) z=0 :=
        smoothScalarGradient_of_constant_germ (φs n) hh z.2
      rw [hval,hgrad,hφv,hφg]
      constructor <;> simp [hd]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceL2_continuous_bounded_convergence_ae {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    (μ : FiniteMeasure NormalBundle) (f : ℕ → C(NormalBundle,F))
    (g : NormalBundle → F) (hg : MemLp g 2 (μ : Measure NormalBundle))
    {M : ℝ} (hM : 0≤M) (hfb : ∀ n,∀ᵐ z ∂(μ : Measure NormalBundle),‖f n z‖≤M)
    (hgb : ∀ᵐ z ∂(μ : Measure NormalBundle),‖g z‖≤M)
    (ht : ∀ᵐ z ∂(μ : Measure NormalBundle),Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n ↦ ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (f n))
      atTop (𝓝 (hg.toLp g)) := by
  have hf (n : ℕ) : MemLp (f n) 2 (μ : Measure NormalBundle) :=
    (f n).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (n : ℕ) : ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (f n)=
      (hf n).toLp (f n) := by
    apply Lp.ext
    exact (f n).coeFn_toLp (μ : Measure NormalBundle) |>.trans (hf n).coeFn_toLp.symm
  simpa only [he] using surfaceL2_bounded_convergence μ (fun n ↦ f n) g hf hg hM hfb hgb ht

theorem nodalSurfaceJet_mem_surfaceH1 (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) (S D : Set Torus) (hD : MeasurableSet D)
    (hpos : ∀ a∈D,0<f.val (representative a))
    (hμ : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈S)
    (hA : ∀ n : ℕ,IsCompact {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)})
    (hB : ∀ n : ℕ,IsClosed {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}) :
    nodalSurfaceJet μ f D hD∈surfaceH1 μ := by
  classical
  obtain ⟨g,hg⟩ := nodal_restriction_smooth_approximants f S D hA hB
  have hv (z : NormalBundle) : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 z.1
  have htval : Tendsto (fun n ↦ (surfaceSmoothJet μ (g n)).1) atTop
      (𝓝 (nodalSurfaceJet μ f D hD).1) := by
    apply surfaceL2_continuous_bounded_convergence_ae μ (fun n ↦ smoothScalarValue (g n))
      (nodalSurfaceValue f D) (nodalSurfaceValue_memLp μ f D hD)
      (norm_nonneg (smoothScalarValue f))
    · intro n
      filter_upwards [hμ] with z hz
      rw [(hg n z hz).1]
      by_cases hd : normalProjection z∈D
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true]
        exact (separatedPositiveTrunc_bound n (f.val z.1)).trans ((smoothScalarValue f).norm_coe_le_norm z)
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        exact norm_nonneg _
    · apply ae_of_all
      intro z
      by_cases hd : normalProjection z∈D
      · simpa only [nodalSurfaceValue,Set.indicator_apply,Set.mem_preimage,hd,ite_true,ite_false] using
          (smoothScalarValue f).norm_coe_le_norm z
      · simp only [nodalSurfaceValue,Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        exact norm_nonneg _
    · filter_upwards [hμ] with z hz
      have he : (fun n ↦ smoothScalarValue (g n) z)=
          fun n ↦ (normalProjection ⁻¹' D).indicator (fun w : NormalBundle ↦ separatedPositiveTrunc n (f.val w.1)) z :=
        funext (fun n ↦ (hg n z hz).1)
      rw [he]
      by_cases hd : normalProjection z∈D
      · have hp : 0<f.val z.1 := by rw [← hv z]; exact hpos _ hd
        simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,nodalSurfaceValue]
        change Tendsto (fun n ↦ separatedPositiveTrunc n (f.val z.1)) atTop (𝓝 (f.val z.1))
        simpa only [max_eq_left hp.le] using
          (separatedPositiveTrunc_tendsto (f.val z.1)).1
      · simpa only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,ite_false,nodalSurfaceValue] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  obtain ⟨K,hK,hKb⟩ := positiveTruncCoeff_bounded
  have htgrad : Tendsto (fun n ↦ (surfaceSmoothJet μ (g n)).2) atTop
      (𝓝 (nodalSurfaceJet μ f D hD).2) := by
    apply surfaceL2_continuous_bounded_convergence_ae μ (fun n ↦ smoothScalarGradient (g n))
      (nodalSurfaceGradient f D) (nodalSurfaceGradient_memLp μ f D hD)
      (mul_nonneg (show 0≤K+1 by linarith) (norm_nonneg (smoothScalarGradient f)))
    · intro n
      filter_upwards [hμ] with z hz
      rw [(hg n z hz).2]
      by_cases hd : normalProjection z∈D
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,norm_smul]
        exact (mul_le_mul (hKb _) ((smoothScalarGradient f).norm_coe_le_norm z)
          (norm_nonneg _) hK).trans (by nlinarith [norm_nonneg (smoothScalarGradient f)])
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        positivity
    · apply ae_of_all
      intro z
      by_cases hd : normalProjection z∈D
      · simp only [nodalSurfaceGradient,Set.indicator_apply,Set.mem_preimage,hd,ite_true]
        exact ((smoothScalarGradient f).norm_coe_le_norm z).trans
          (by nlinarith [norm_nonneg (smoothScalarGradient f)])
      · simp only [nodalSurfaceGradient,Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        positivity
    · filter_upwards [hμ] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [(separatedPositiveTrunc_tendsto (f.val z.1)).2] with n hn
      rw [(hg n z hz).2]
      by_cases hd : normalProjection z∈D
      · have hp : 0<f.val z.1 := by rw [← hv z]; exact hpos _ hd
        simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,hn,ite_eq_left hp,one_smul,nodalSurfaceGradient]
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_false,nodalSurfaceGradient]
  apply (surfaceSmoothJet μ).range.isClosed_topologicalClosure.mem_of_tendsto
    (htval.prodMk_nhds htgrad)
  filter_upwards [] with n
  exact subset_closure ⟨g n,rfl⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveNodalPiece_superlevels (f : smoothPeriodicScalars) {S D : Set Torus}
    (hS : IsClosed S) (hD : IsPositiveNodalPiece f S D) :
    MeasurableSet D ∧ (∀ a∈D,0<f.val (representative a)) ∧
    (∀ n : ℕ,IsCompact {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)}) ∧
    (∀ n : ℕ,IsClosed {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}) := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  have hf : Continuous (fun a : Torus ↦ f.val (representative a)) :=
    continuous_periodic_descent f.property.1.continuous f.property.2
  have hP : MeasurableSet {a : Torus | a∈S ∧ 0<f.val (representative a)} :=
    hS.measurableSet.inter (isOpen_lt continuous_const hf).measurableSet
  refine ⟨by rw [hDU]; exact hP.inter hU.measurableSet,?_,?_,?_⟩
  · intro a ha
    rw [hDU] at ha
    exact ha.1.2
  · intro n
    have he : {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)}=
        S∩C∩{a | nodalEpsilon n≤f.val (representative a)} := by
      ext a
      constructor
      · rintro ⟨ha,hd,hv⟩
        rw [hDC] at hd
        exact ⟨⟨ha,hd.2⟩,hv⟩
      · rintro ⟨⟨ha,hc⟩,hv⟩
        refine ⟨ha,?_,hv⟩
        rw [hDC]
        exact ⟨⟨ha,(nodalEpsilon_pos n).trans_le hv⟩,hc⟩
    rw [he]
    exact ((hS.inter hC).inter (isClosed_le continuous_const hf)).isCompact
  · intro n
    have he : {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}=
        S∩Uᶜ∩{a | nodalEpsilon n≤f.val (representative a)} := by
      ext a
      constructor
      · rintro ⟨ha,hd,hv⟩
        refine ⟨⟨ha,?_⟩,hv⟩
        intro hu
        apply hd
        rw [hDU]
        exact ⟨⟨ha,(nodalEpsilon_pos n).trans_le hv⟩,hu⟩
      · rintro ⟨⟨ha,hu⟩,hv⟩
        refine ⟨ha,?_,hv⟩
        intro hd
        rw [hDU] at hd
        exact hu hd.2
    rw [he]
    exact (hS.inter hU.isClosed_compl).inter (isClosed_le continuous_const hf)

theorem isMinimizerAt_positive_nodal_piece_H1 {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) {D : Set Torus}
    (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D) :
    ∃ hDm : MeasurableSet D,nodalSurfaceJet μ f D hDm∈surfaceH1 μ := by
  obtain ⟨hDm,hpos,hA,hB⟩ := positiveNodalPiece_superlevels f isClosed_frontier hD
  refine ⟨hDm,nodalSurfaceJet_mem_surfaceH1 μ f (frontier (openRepresentative E)) D hDm hpos ?_ hA hB⟩
  exact normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceJacobiB_nodal_restriction (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) :
    surfaceJacobiB μ q (surfaceSmoothJet μ f) (nodalSurfaceJet μ f D hD)=
      surfaceJacobiB μ q (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ f D hD) := by
  classical
  have hv := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hg := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hpv := (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp
  have hpg := (nodalSurfaceGradient_memLp μ f D hD).coeFn_toLp
  unfold surfaceJacobiB
  congr 1
  · rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg,hpg] with z hgz hpgz
    change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hgz
    change (nodalSurfaceJet μ f D hD).2 z=nodalSurfaceGradient f D z at hpgz
    rw [hgz,hpgz]
    by_cases hd : normalProjection z∈D <;> simp [nodalSurfaceGradient,hd]
  · rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    have hmf := Lp.coeFn_lpSMul (r := 2) q (surfaceSmoothJet μ f).1
    have hmp := Lp.coeFn_lpSMul (r := 2) q (nodalSurfaceJet μ f D hD).1
    filter_upwards [hv,hpv,hmf,hmp] with z hvz hpvz hmfz hmpz
    change (surfaceSmoothJet μ f).1 z=f.val z.1 at hvz
    change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hpvz
    change (surfaceMultiplier μ q (surfaceSmoothJet μ f).1) z=_ at hmfz
    change (surfaceMultiplier μ q (nodalSurfaceJet μ f D hD).1) z=_ at hmpz
    rw [hmfz,hmpz]
    simp only [smul_eq_mul,Pi.mul_apply,hvz,hpvz]
    by_cases hd : normalProjection z∈D <;> simp [nodalSurfaceValue,smoothScalarValue,hd]

lemma surfaceJacobiB_disjoint_nodal (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f g : smoothPeriodicScalars)
    (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A) (hDA : Disjoint D A) :
    surfaceJacobiB μ q (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ g A hA)=0 := by
  classical
  have hdv := (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp
  have hdg := (nodalSurfaceGradient_memLp μ f D hD).coeFn_toLp
  have hav := (nodalSurfaceValue_memLp μ g A hA).coeFn_toLp
  have hag := (nodalSurfaceGradient_memLp μ g A hA).coeFn_toLp
  unfold surfaceJacobiB
  have hx : ⟪(nodalSurfaceJet μ f D hD).2,(nodalSurfaceJet μ g A hA).2⟫=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hdg,hag] with z hdz haz
    change (nodalSurfaceJet μ f D hD).2 z=nodalSurfaceGradient f D z at hdz
    change (nodalSurfaceJet μ g A hA).2 z=nodalSurfaceGradient g A z at haz
    rw [hdz,haz]
    by_cases hd : normalProjection z∈D
    · have ha : normalProjection z∉A := fun ha ↦ Set.disjoint_left.mp hDA hd ha
      simp [nodalSurfaceGradient,ha]
    · simp [nodalSurfaceGradient,hd]
  rw [hx,zero_sub,neg_eq_zero]
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hm := Lp.coeFn_lpSMul (r := 2) q (nodalSurfaceJet μ f D hD).1
  filter_upwards [hdv,hav,hm] with z hdz haz hmz
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hdz
  change (nodalSurfaceJet μ g A hA).1 z=nodalSurfaceValue g A z at haz
  change (surfaceMultiplier μ q (nodalSurfaceJet μ f D hD).1) z=_ at hmz
  rw [hmz]
  simp only [smul_eq_mul,Pi.mul_apply,hdz,haz]
  by_cases hd : normalProjection z∈D
  · have ha : normalProjection z∉A := fun ha ↦ Set.disjoint_left.mp hDA hd ha
    simp [nodalSurfaceValue,ha]
  · simp [nodalSurfaceValue,hd]

lemma nodalSurfaceJet_null (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) (hm : nodalSurfaceJet μ f D hD∈surfaceH1 μ)
    (hj : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) w=0) :
    surfaceJacobiB μ q (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ f D hD)=0 := by
  rw [← surfaceJacobiB_nodal_restriction]
  exact hj _ hm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceMean_nodal (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) :
    surfaceMean μ (nodalSurfaceJet μ f D hD)=∫ z,nodalSurfaceValue f D z ∂(μ : Measure NormalBundle) := by
  change ⟪(surfaceOne μ).1,(nodalSurfaceJet μ f D hD).1⟫=_
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv := (smoothScalarValue smoothScalarOne).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hd := (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp
  filter_upwards [hv,hd] with z hvz hdz
  change (surfaceOne μ).1 z=1 at hvz
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hdz
  rw [hvz,hdz]
  simp

theorem isMinimizerAt_nodal_mean_pos {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) {D : Set Torus} (hDm : MeasurableSet D)
    (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D) (hDn : D.Nonempty) :
    0 < surfaceMean μ (nodalSurfaceJet μ f D hDm) := by
  classical
  have hv (z : NormalBundle) : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 z.1
  have hpos := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1
  have hp (z : NormalBundle) : 0≤nodalSurfaceValue f D z := by
    by_cases hd : normalProjection z∈D
    · have hh := hpos _ hd
      rw [hv z] at hh
      simpa [nodalSurfaceValue,hd,smoothScalarValue] using hh.le
    · simp [nodalSurfaceValue,hd]
  rw [surfaceMean_nodal]
  by_contra! h
  have hz : (∫ z,nodalSurfaceValue f D z ∂(μ : Measure NormalBundle))=0 :=
    le_antisymm h (integral_nonneg hp)
  have hae := (integral_eq_zero_iff_of_nonneg hp
    ((nodalSurfaceValue_memLp μ f D hDm).integrable (by norm_num))).mp hz
  obtain ⟨U,hU,hDU⟩ := hD.1
  obtain ⟨a,ha⟩ := hDn
  have ha' := ha
  rw [hDU] at ha'
  have hf : Continuous (fun a : Torus ↦ f.val (representative a)) :=
    continuous_periodic_descent f.property.1.continuous f.property.2
  let W : Set Torus := U∩{a : Torus | 0<f.val (representative a)}
  have hW : IsOpen W := hU.inter (isOpen_lt continuous_const hf)
  have haW : a∈W := ⟨ha'.2,ha'.1.2⟩
  obtain ⟨φ,hφ,hper,hb,⟨T,hT,haT,hone⟩,hzero⟩ := exists_periodic_local_cutoff a hW haW
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hφae : ∀ᵐ z ∂(μ : Measure NormalBundle),φ z.1=0 := by
    filter_upwards [hbd,hae] with z hzbd hz0
    by_cases hzW : normalProjection z∈W
    · have hzD : normalProjection z∈D := by
        rw [hDU]
        exact ⟨⟨hzbd,hzW.2⟩,hzW.1⟩
      have hfz : 0<f.val z.1 := by
        have hh : 0<f.val (representative (normalProjection z)) := hzW.2
        rw [hv z] at hh
        exact hh
      have hf0 : f.val z.1=0 := by simpa [nodalSurfaceValue,hzD,smoothScalarValue] using hz0
      exact False.elim (hfz.ne' hf0)
    · exact (hzero z.1 hzW).self_of_nhds
  have he := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hφ.continuous
    (continuous_const (y := (0 : ℝ))) hper (fun _ _ ↦ rfl) hφae (representative a)
    (by simpa only [quotientMap_representative] using ha'.1.1)
  have hh := (hone (representative a) (by simpa only [quotientMap_representative] using haT)).self_of_nhds
  change φ (representative a)=(0 : ℝ) at he
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceNodalBalance_mean (μ : FiniteMeasure NormalBundle) (u v : SurfaceJet μ) :
    surfaceMean μ (surfaceNodalBalance μ u v)=0 := by
  simp only [surfaceNodalBalance,map_add,map_smul,smul_eq_mul]
  ring

lemma surfaceNodalBalance_mem (μ : FiniteMeasure NormalBundle) {u v : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) (hv : v∈surfaceH1 μ) : surfaceNodalBalance μ u v∈surfaceH1 μ :=
  (surfaceH1 μ).add_mem ((surfaceH1 μ).smul_mem _ hu) ((surfaceH1 μ).smul_mem _ hv)

lemma surfaceNodalBalance_null (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u v : SurfaceJet μ}
    (hu : surfaceJacobiB μ q u u=0) (hv : surfaceJacobiB μ q v v=0)
    (huv : surfaceJacobiB μ q u v=0) :
    surfaceJacobiB μ q (surfaceNodalBalance μ u v) (surfaceNodalBalance μ u v)=0 := by
  have hvu : surfaceJacobiB μ q v u=0 := by rw [surfaceJacobiB_symm]; exact huv
  unfold surfaceNodalBalance
  rw [surfaceJacobiB_add_left,surfaceJacobiB_smul_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_symm μ q u,surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_smul_left,hu,hvu,
    surfaceJacobiB_symm μ q v,surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_smul_left,huv,hv]
  ring

lemma nodalSurfaceJet_zero_outside (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) (D U : Set Torus) (hD : MeasurableSet D) (hUD : Disjoint U D) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U →
      (nodalSurfaceJet μ f D hD).1 z=0 ∧ (nodalSurfaceJet μ f D hD).2 z=0 := by
  classical
  filter_upwards [(nodalSurfaceValue_memLp μ f D hD).coeFn_toLp,
    (nodalSurfaceGradient_memLp μ f D hD).coeFn_toLp] with z hvz hgz hz
  have hd : normalProjection z∉D := fun hd ↦ Set.disjoint_left.mp hUD hz hd
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hvz
  change (nodalSurfaceJet μ f D hD).2 z=nodalSurfaceGradient f D z at hgz
  rw [hvz,hgz]
  simp [nodalSurfaceValue,nodalSurfaceGradient,hd]

lemma surfaceNodalBalance_zero_patch (μ : FiniteMeasure NormalBundle)
    {u v : SurfaceJet μ} {U : Set Torus}
    (hu : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0)
    (hv : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → v.1 z=0 ∧ v.2 z=0) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U →
      (surfaceNodalBalance μ u v).1 z=0 ∧ (surfaceNodalBalance μ u v).2 z=0 := by
  have h1 := Lp.coeFn_add (surfaceMean μ v • u.1) ((-surfaceMean μ u) • v.1)
  have h2 := Lp.coeFn_add (surfaceMean μ v • u.2) ((-surfaceMean μ u) • v.2)
  filter_upwards [hu,hv,h1,h2,Lp.coeFn_smul (surfaceMean μ v) u.1,
    Lp.coeFn_smul (-surfaceMean μ u) v.1,Lp.coeFn_smul (surfaceMean μ v) u.2,
    Lp.coeFn_smul (-surfaceMean μ u) v.2] with z huz hvz h1z h2z h3z h4z h5z h6z hz
  obtain ⟨huv,hug⟩ := huz hz
  obtain ⟨hvv,hvg⟩ := hvz hz
  constructor
  · change (surfaceMean μ v • u.1+(-surfaceMean μ u) • v.1) z=0
    rw [h1z]
    simp only [Pi.add_apply,h3z,h4z,Pi.smul_apply,huv,hvv,smul_zero,add_zero]
  · change (surfaceMean μ v • u.2+(-surfaceMean μ u) • v.2) z=0
    rw [h2z]
    simp only [Pi.add_apply,h5z,h6z,Pi.smul_apply,hug,hvg,smul_zero,add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isOpen_positiveBoundaryLocus (f : smoothPeriodicScalars) (S : Set Torus) :
    IsOpen (positiveBoundaryLocus f S) := by
  apply isOpen_lt continuous_const
  exact (continuous_periodic_descent f.property.1.continuous f.property.2).comp continuous_subtype_val

lemma positiveBoundaryDomain_nonempty (f : smoothPeriodicScalars) (S : Set Torus)
    (a : positiveBoundaryLocus f S) : (positiveBoundaryDomain f S a).Nonempty :=
  ⟨a.val.val,a,mem_connectedComponent,rfl⟩

lemma positiveBoundaryDomain_isPositiveNodalPiece (f : smoothPeriodicScalars) (S : Set Torus)
    [LocallyConnectedSpace S] (a : positiveBoundaryLocus f S) :
    IsPositiveNodalPiece f S (positiveBoundaryDomain f S a) := by
  let : LocallyConnectedSpace (positiveBoundaryLocus f S) :=
    (isOpen_positiveBoundaryLocus f S).locallyConnectedSpace
  let g : positiveBoundaryLocus f S → Torus := fun b ↦ b.val.val
  have hg : Topology.IsInducing g :=
    (Topology.IsInducing.subtypeVal (t := S)).comp
      (Topology.IsInducing.subtypeVal (t := positiveBoundaryLocus f S))
  have hr : Set.range g={b : Torus | b∈S ∧ 0<f.val (representative b)} := by
    ext b
    constructor
    · rintro ⟨c,rfl⟩; exact ⟨c.val.property,c.property⟩
    · rintro ⟨hS,hp⟩; exact ⟨⟨⟨b,hS⟩,hp⟩,rfl⟩
  obtain ⟨U,hU,hUeq⟩ := hg.isOpen_iff.mp (isOpen_connectedComponent (x := a))
  obtain ⟨C,hC,hCeq⟩ := hg.isClosed_iff.mp (isClosed_connectedComponent (x := a))
  constructor
  · refine ⟨U,hU,?_⟩
    change g '' connectedComponent a=_
    rw [← hUeq,image_preimage_eq_inter_range,hr,inter_comm]
  · refine ⟨C,hC,?_⟩
    change g '' connectedComponent a=_
    rw [← hCeq,image_preimage_eq_inter_range,hr,inter_comm]

theorem isMinimizerAt_actual_nodal_piece {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (f : smoothPeriodicScalars)
    (a : positiveBoundaryLocus f (frontier (openRepresentative E))) :
    IsPositiveNodalPiece f (frontier (openRepresentative E))
      (positiveBoundaryDomain f (frontier (openRepresentative E)) a) := by
  let := isMinimizerAt_boundary_locallyConnected hV hE hmin
  exact positiveBoundaryDomain_isPositiveNodalPiece f _ a

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveNodalPiece_open_patch (f : smoothPeriodicScalars) (S C : Set Torus)
    (hC : IsPositiveNodalPiece f S C) (hCn : C.Nonempty) :
    ∃ U : Set Torus,IsOpen U ∧ U∩S=C ∧ (U∩S).Nonempty := by
  obtain ⟨U,hU,hCU⟩ := hC.1
  have hf : Continuous (fun a : Torus ↦ f.val (representative a)) :=
    continuous_periodic_descent f.property.1.continuous f.property.2
  refine ⟨U∩{a | 0<f.val (representative a)},hU.inter (isOpen_lt continuous_const hf),?_,?_⟩
  · rw [hCU]
    ext a
    simp only [mem_inter_iff,mem_ofPred_eq]
    tauto
  · obtain ⟨a,ha⟩ := hCn
    rw [hCU] at ha
    exact ⟨a,⟨ha.2,ha.1.2⟩,ha.1.1⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateReflection2
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

lemma firstReflection_symm : firstReflection.symm=firstReflection := by
  apply LinearIsometryEquiv.ext
  intro x
  apply firstReflection.injective
  rw [LinearIsometryEquiv.apply_symm_apply,firstReflection_involutive]

lemma torusFirstReflection_measurePreserving :
    MeasurePreserving torusFirstReflection torusVolume torusVolume := by
  let f : ProductTorus → ProductTorus := fun x i ↦ if i=0 then -x i else x i
  have hf : MeasurePreserving f volume volume := by
    rw [volume_pi]
    apply measurePreserving_pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle (1 : ℝ)) ))
      (fun _ : Fin 3 ↦ (volume : Measure (AddCircle (1 : ℝ))))
      (f := fun i x ↦ if i=0 then -x else x)
    intro i
    by_cases hi : i=0
    · simp only [hi,ite_true]
      exact Measure.measurePreserving_neg (volume : Measure (AddCircle (1 : ℝ)))
    · simp only [hi,ite_false]
      exact MeasurePreserving.id _
  exact product_to_torus_measurePreserving.comp (hf.comp torus_to_product_measurePreserving)

lemma firstReflection_lattice (n : Fin 3 → ℤ) :
    firstReflection (latticeVector n)=
      latticeVector (fun i ↦ if i=0 then -n i else n i) := by
  ext i
  simp only [firstReflection_apply,latticeVector,WithLp.ofLp_toLp]
  split_ifs <;> simp

lemma reflectionPullback_contDiff {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (reflectionPullback F) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ firstReflection (F (firstReflection x)))
  simpa only [reflectionPullback,firstReflection_symm] using isometry_pullback_contDiff firstReflection hF

lemma reflectionPullback_periodic {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,reflectionPullback F (x+latticeVector n)=reflectionPullback F x := by
  intro n x
  simp only [reflectionPullback,map_add,firstReflection_lattice,hp]

lemma reflectionPullback_admissible {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (reflectionPullback F) :=
  ⟨reflectionPullback_contDiff hF.1,reflectionPullback_periodic hF.2.1,
    fun x ↦ by simpa only [reflectionPullback,LinearIsometryEquiv.norm_map] using hF.2.2 (firstReflection x)⟩

lemma divergence_reflectionPullback {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (reflectionPullback F) x=divergence F (firstReflection x) := by
  change divergence (fun y ↦ firstReflection (F (firstReflection y))) x=_
  simpa only [reflectionPullback,firstReflection_symm] using
    divergence_isometry_pullback firstReflection (hF.differentiable (by simp)) x

lemma flux_firstReflection {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' (torusFirstReflection ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence (reflectionPullback F) x := by
  have hG := reflectionPullback_admissible hF
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1)
    (hE.preimage torusFirstReflection.continuous.measurable),
    ← setIntegral_lift (continuous_divergence hG.1) (divergence_periodic hG.2.1) hE]
  have he : (fun z : Torus ↦ divergence F (representative z))=
      fun z ↦ divergence (reflectionPullback F) (representative (torusFirstReflection z)) := by
    funext z
    rw [divergence_reflectionPullback hF.1]
    have hq : quotientMap (firstReflection (representative (torusFirstReflection z)))=
        quotientMap (representative z) := by
      rw [firstReflection_quotient,quotientMap_representative,
        torusFirstReflection_involutive,quotientMap_representative]
    obtain ⟨n,hn⟩ := same_quotient_lattice hq
    rw [hn,divergence_periodic hF.2.1]
  rw [he]
  exact torusFirstReflection_measurePreserving.setIntegral_preimage_emb
    torusFirstReflection.toHomeomorph.measurableEmbedding
      (fun z ↦ divergence (reflectionPullback F) (representative z)) E

lemma perimeter_firstReflection {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusFirstReflection ⁻¹' E)=perimeter E := by
  have hle {A : Set Torus} (hA : MeasurableSet A) :
      perimeter (torusFirstReflection ⁻¹' A)≤perimeter A := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    rw [flux_firstReflection hF hA]
    exact le_iSup₂_of_le (reflectionPullback F) (reflectionPullback_admissible hF) le_rfl
  apply le_antisymm (hle hE)
  have hh := hle (hE.preimage torusFirstReflection.continuous.measurable)
  simpa only [preimage_preimage,Function.comp_def,torusFirstReflection_involutive,preimage_id'] using hh

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarWeakGradient
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

lemma sibling_continuous_indicator_positive_piece {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} (hf : Continuous f) {D : Set α}
    (hDo : ∃ U : Set α,IsOpen U ∧ D={x | 0<f x}∩U)
    (hDc : ∃ C : Set α,IsClosed C ∧ D={x | 0<f x}∩C) :
    Continuous (D.indicator f) := by
  obtain ⟨U,hU,hDU⟩ := hDo
  obtain ⟨C,hC,hDC⟩ := hDc
  have hD : IsOpen D := by rw [hDU]; exact (isOpen_lt continuous_const hf).inter hU
  have hpos : closure D⊆{x | 0≤f x} :=
    (isClosed_le continuous_const hf).closure_subset_iff.mpr (by
      intro x hx
      rw [hDU] at hx
      exact (show 0<f x from hx.1).le)
  have hcls : closure D⊆C := hC.closure_subset_iff.mpr (by
    intro x hx
    rw [hDC] at hx
    exact hx.2)
  apply continuous_indicator _ hf.continuousOn
  intro x hx
  have hf0 := hpos hx.1
  apply le_antisymm _ hf0
  by_contra hh
  have hxD : x∈D := by rw [hDC]; exact ⟨lt_of_not_ge hh,hcls hx.1⟩
  exact hx.2 (by simpa only [hD.interior_eq] using hxD)

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NodalTorusScalar
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

theorem positiveNodalPiece_continuousOn (f : smoothPeriodicScalars) {S D : Set Torus}
    (hD : IsPositiveNodalPiece f S D) :
    ContinuousOn (D.indicator (fun a ↦ f.val (representative a))) S := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  have hf : Continuous (fun a : S ↦ f.val (representative a.val)) :=
    (continuous_periodic_descent f.property.1.continuous f.property.2).comp continuous_subtype_val
  let D' : Set S := Subtype.val ⁻¹' D
  have hDo : ∃ U' : Set S,IsOpen U' ∧ D'={a | 0<f.val (representative a.val)}∩U' := by
    refine ⟨Subtype.val ⁻¹' U,hU.preimage continuous_subtype_val,?_⟩
    ext a
    simp [D',hDU]
  have hDc : ∃ C' : Set S,IsClosed C' ∧ D'={a | 0<f.val (representative a.val)}∩C' := by
    refine ⟨Subtype.val ⁻¹' C,hC.preimage continuous_subtype_val,?_⟩
    ext a
    simp [D',hDC]
  rw [continuousOn_iff_continuous_domRestrict]
  convert sibling_continuous_indicator_positive_piece hf hDo hDc using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  change D.indicator _ a.val = D'.indicator _ a
  by_cases ha : a.val∈D
  · rw [Set.indicator_of_mem ha,Set.indicator_of_mem (show a∈D' from ha)]
  · rw [Set.indicator_of_notMem ha,Set.indicator_of_notMem (show a∉D' from ha)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma nodalTorusScalar_measurable (f : smoothPeriodicScalars) {D : Set Torus}
    (hD : MeasurableSet D) : Measurable (nodalTorusScalar f D) :=
  (continuous_periodic_descent f.property.1.continuous f.property.2).measurable.indicator hD

lemma nodalSurfaceJet_scalar_ae (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),(nodalSurfaceJet μ f D hD).1 z=
      nodalTorusScalar f D (normalProjection z) := by
  filter_upwards [(nodalSurfaceValue_memLp μ f D hD).coeFn_toLp] with z hz
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hz
  rw [hz]
  by_cases hd : normalProjection z∈D
  · simp only [nodalSurfaceValue,nodalTorusScalar,
      Set.indicator_of_mem hd,Set.indicator_of_mem (show z∈normalProjection ⁻¹' D from hd)]
    exact (periodic_representative f.property.2 z.1).symm
  · simp only [nodalSurfaceValue,nodalTorusScalar,
      Set.indicator_of_notMem hd,Set.indicator_of_notMem (show z∉normalProjection ⁻¹' D from hd)]

lemma surfaceNodalBalance_scalar_ae (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A) :
    let d := nodalSurfaceJet μ f D hD
    let a := nodalSurfaceJet μ g A hA
    ∀ᵐ z ∂(μ : Measure NormalBundle),(surfaceNodalBalance μ d a).1 z=
      surfaceMean μ a*nodalTorusScalar f D (normalProjection z)-
        surfaceMean μ d*nodalTorusScalar g A (normalProjection z) := by
  dsimp only
  let d := nodalSurfaceJet μ f D hD
  let a := nodalSurfaceJet μ g A hA
  filter_upwards [nodalSurfaceJet_scalar_ae μ f D hD,nodalSurfaceJet_scalar_ae μ g A hA,
    Lp.coeFn_add (surfaceMean μ a • d.1) ((-surfaceMean μ d) • a.1),
    Lp.coeFn_smul (surfaceMean μ a) d.1,Lp.coeFn_smul (-surfaceMean μ d) a.1] with
    z hd ha hadd hsm hsa
  change ((surfaceMean μ a • d.1+(-surfaceMean μ d) • a.1 : Lp ℝ 2 _) : NormalBundle → ℝ) z=_
  rw [hadd,Pi.add_apply,hsm,hsa]
  change surfaceMean μ a*d.1 z+(-surfaceMean μ d)*a.1 z=_
  rw [hd,ha]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveNodalPiece_subset (f : smoothPeriodicScalars) {S D : Set Torus}
    (hD : IsPositiveNodalPiece f S D) : D⊆S := by
  intro a ha
  rw [hD.1.choose_spec.2] at ha
  exact ha.1.1

lemma positiveNodalPiece_boundary_nonempty (f : smoothPeriodicScalars) {S D : Set Torus}
    (hS : IsPreconnected S) (hD : IsPositiveNodalPiece f S D)
    (hDn : D.Nonempty) (hother : (S\D).Nonempty) : (closure D\D).Nonempty := by
  by_contra hh
  have hclosed : IsClosed D := isClosed_of_closure_subset (by
    intro a ha
    by_contra hn
    exact hh ⟨a,ha,hn⟩)
  obtain ⟨U,hU,hDU,_⟩ := positiveNodalPiece_open_patch f S D hD hDn
  obtain ⟨a,ha⟩ := hDn
  obtain ⟨b,hbS,hbD⟩ := hother
  have hab := hS U Dᶜ hU hclosed.isOpen_compl (by
      intro x hx
      by_cases hxD : x∈D
      · left; have h := hxD; rw [← hDU] at h; exact h.1
      · exact Or.inr hxD)
    ⟨a,positiveNodalPiece_subset f hD ha,(by rw [← hDU] at ha; exact ha.1)⟩ ⟨b,hbS,hbD⟩
  obtain ⟨x,hxS,hxU,hxD⟩ := hab
  exact hxD (by rw [← hDU]; exact ⟨hxU,hxS⟩)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_SiblingReflectNormal
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

theorem isMinimizerAt_normal_unique {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ w : Cover,∀ (μ : FiniteMeasure NormalBundle),IsNormalMeasure E μ →
      ∀ (N : Cover → Cover),ContDiff ℝ (⊤ : ℕ∞) N →
      (∀ m x,N (x+latticeVector m)=N x) →
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) → N x=w := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [←quotientMap_add,show cubeCenter+a=x by dsimp [a]; abel]
    exact hx
  obtain ⟨w,hw⟩ := isMinimizerAt_center_normal_unique hV hE' hmin' hc
  refine ⟨w,?_⟩
  intro μ hμ N hN hp hae
  let N' : Cover → Cover := fun y ↦ N (y+a)
  have hN' : ContDiff ℝ (⊤ : ℕ∞) N' := hN.comp (contDiff_id.add contDiff_const)
  have hp' : ∀ m y,N' (y+latticeVector m)=N' y := by
    intro m y
    change N ((y+latticeVector m)+a)=N (y+a)
    rw [add_right_comm,hp]
  have hae' : ∀ᵐ z ∂((μ.map (translateNormal a)) : Measure NormalBundle),N' z.1=(z.2 : Cover) := by
    change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),N' z.1=(z.2 : Cover)
    apply (ae_map_iff (measurable_translateNormal a).aemeasurable
      (isClosed_eq (hN'.continuous.comp normalEmbedding_continuous.fst) continuous_normalUnit).measurableSet).mpr
    filter_upwards [hae] with z hz
    change N' (translateNormal a z).1=(z.2 : Cover)
    rw [translateNormal_periodic_eval hp']
    change N (((z.1 : Cover)-a)+a)=(z.2 : Cover)
    simpa only [sub_add_cancel] using hz
  have hh := hw (μ.map (translateNormal a)) (isNormalMeasure_translation hE hμ a)
    N' hN' hp' hae'
  change N (cubeCenter+a)=w at hh
  simpa only [show cubeCenter+a=x by dsimp [a]; abel] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_measurable_reflectNormal : Measurable sibling_reflectNormal := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp (torusFirstReflection.continuous.measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact (firstReflection.continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma sibling_reflectNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (z : NormalBundle) :
    F (sibling_reflectNormal z).1=F (firstReflection z.1) := by
  change F (representative (torusFirstReflection (quotientMap z.1)))=_
  rw [←firstReflection_quotient,periodic_representative hp]

theorem isNormalMeasure_firstReflection {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsNormalMeasure (torusFirstReflection ⁻¹' E) (μ.map sibling_reflectNormal) := by
  constructor
  · have hm : ((μ.map sibling_reflectNormal).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply sibling_measurable_reflectNormal
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_firstReflection hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map sibling_reflectNormal (μ : Measure NormalBundle))=_
    rw [integral_map sibling_measurable_reflectNormal.aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_firstReflection hF hE,←hμ.2 _ (reflectionPullback_admissible hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      change ⟪firstReflection (z.2 : Cover),F (sibling_reflectNormal z).1⟫=
        ⟪(z.2 : Cover),firstReflection (F (firstReflection z.1))⟫
      rw [sibling_reflectNormal_periodic_eval hF.2.1]
      simpa only [firstReflection_involutive] using
        (firstReflection.inner_map_map (z.2 : Cover) (firstReflection (F (firstReflection z.1))))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_lifted_boundary_global {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) (a : Cover) :
    a∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
      quotientMap a∈frontier (openRepresentative E) := by
  let b := a-cubeCenter
  let F := (fun z : Torus ↦ z+quotientMap b) ⁻¹' E
  have hF : MeasurableSet F := hE.preimage (continuous_id.add continuous_const).measurable
  have hminF := isMinimizerAt_translation hmin (quotientMap b)
  have hcent := isMinimizerAt_lifted_boundary hV hF hminF (x := cubeCenter) (by intro i; norm_num [cubeCenter])
  have he : quotientMap ⁻¹' F=(Homeomorph.addRight b) ⁻¹' (quotientMap ⁻¹' E) := by
    ext x
    change quotientMap x+quotientMap b∈E ↔ quotientMap (x+b)∈E
    rw [quotientMap_add]
  rw [he,cover_boundary_measurePreserving_homeomorph (Homeomorph.addRight b)
    (measurePreserving_add_right volume b),frontier_openRepresentative_translation hE] at hcent
  have hb : cubeCenter+b=a := by dsimp [b]; abel
  change cubeCenter+b∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
    quotientMap cubeCenter+quotientMap b∈frontier (openRepresentative E) at hcent
  rw [←quotientMap_add,hb] at hcent
  exact hcent

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FirstSeamFunction
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

lemma firstSeamFunction_contDiff : ContDiff ℝ (⊤ : ℕ∞) firstSeamFunction := by
  unfold firstSeamFunction
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ x 0) := (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ).contDiff
  exact ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Cover ↦ 2*Real.pi)).mul hc).sin

lemma firstSeamFunction_periodic :
    ∀ n x,firstSeamFunction (x+latticeVector n)=firstSeamFunction x := by
  intro n x
  unfold firstSeamFunction
  simp only [PiLp.add_apply,latticeVector]
  convert Real.sin_add_int_mul_two_pi (2*Real.pi*x 0) (n 0) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma firstSeamFunction_reflection (x : Cover) :
    firstSeamFunction (firstReflection x)= -firstSeamFunction x := by
  simp only [firstSeamFunction,firstReflection_apply,ite_true,mul_neg,Real.sin_neg]

lemma firstSeam_distance_bound (t : ℝ) :
    4*|t-(round (2*t):ℝ)/2|≤|Real.sin (2*Real.pi*t)| := by
  let n := round (2*t)
  let d := t-(n:ℝ)/2
  have hd : |d|≤1/4 := by
    have hh := abs_sub_round (2*t)
    have he : 2*t-(n:ℝ)=2*d := by dsimp [d]; ring
    rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
    linarith
  have ha : |2*Real.pi*d|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.pi_pos]
  have hh := Real.mul_abs_le_abs_sin ha
  have hleft : 2/Real.pi*|2*Real.pi*d|=4*|d| := by
    rw [abs_mul,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    field_simp
    ring
  rw [hleft] at hh
  have he : 2*Real.pi*t=2*Real.pi*d+(n:ℝ)*Real.pi := by dsimp [d]; ring
  rw [he,Real.sin_add_int_mul_pi,abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul]
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma firstSeam_representative_reflection (z : Torus) :
    firstSeamFunction (representative (torusFirstReflection z))=
      -firstSeamFunction (representative z) := by
  rw [← quotientMap_representative z,← firstReflection_quotient,
    periodic_representative firstSeamFunction_periodic,
    firstSeamFunction_reflection,periodic_representative firstSeamFunction_periodic]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FirstAxisShift
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

lemma reflectionPullback_normal_ae {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∀ᵐ z ∂((μ.map sibling_reflectNormal) : Measure NormalBundle),
      reflectionPullback N z.1=(z.2 : Cover) := by
  rw [FiniteMeasure.toMeasure_map]
  have hc : Continuous (fun z : NormalBundle ↦ reflectionPullback N z.1) :=
    (reflectionPullback_contDiff hN).continuous.comp normalEmbedding_continuous.fst
  apply (ae_map_iff sibling_measurable_reflectNormal.aemeasurable
    (isClosed_eq hc continuous_normalUnit).measurableSet).mpr
  filter_upwards [hae] with z hz
  change reflectionPullback N (sibling_reflectNormal z).1=firstReflection (z.2 : Cover)
  rw [sibling_reflectNormal_periodic_eval (reflectionPullback_periodic hp)]
  change firstReflection (N (firstReflection (firstReflection z.1)))=_
  rw [firstReflection_involutive,hz]

theorem isMinimizerAt_reflection_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    N (firstReflection x)=firstReflection (N x) := by
  let M := reflectionPullback N
  have hM : ContDiff ℝ (⊤ : ℕ∞) M := reflectionPullback_contDiff hN
  have hpM : ∀ m x,M (x+latticeVector m)=M x := reflectionPullback_periodic hp
  have hμR : IsNormalMeasure E (μ.map sibling_reflectNormal) :=
    (isNormalMeasure_firstReflection hE hμ).congr_ae hR.symm
  have haeM := reflectionPullback_normal_ae hN hp hae
  obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique hV hE hmin x hx
  have he := (hw μ hμ N hN hp hae).trans (hw (μ.map sibling_reflectNormal) hμR M hM hpM haeM).symm
  change N x=firstReflection (N (firstReflection x)) at he
  have hh := congrArg firstReflection he
  simpa only [firstReflection_involutive] using hh.symm

theorem isMinimizerAt_reflection_seam_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (hfix : torusFirstReflection (quotientMap x)=quotientMap x) : N x 0=0 := by
  have he := isMinimizerAt_reflection_normal hV hE hmin hR hμ hN hp hae x hx
  have hq : quotientMap (firstReflection x)=quotientMap x := by rw [firstReflection_quotient,hfix]
  obtain ⟨m,hm⟩ := same_quotient_lattice hq
  rw [hm,hp] at he
  have hc := congrArg (fun v : Cover ↦ v 0) he
  simp only [firstReflection_apply,ite_true] at hc
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma firstSeam_zero_fixed (x : Cover) (hx : firstSeamFunction x=0) :
    torusFirstReflection (quotientMap x)=quotientMap x := by
  let n := round (2*x 0)
  have hb := firstSeam_distance_bound (x 0)
  change 4*|x 0-(n:ℝ)/2|≤|firstSeamFunction x| at hb
  rw [hx,abs_zero] at hb
  have he : x 0=(n:ℝ)/2 := by
    have hh : |x 0-(n:ℝ)/2|=0 := le_antisymm (by linarith) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hh)
  have hr : firstReflection x=x+latticeVector (Pi.single 0 (-n)) := by
    ext i
    by_cases hi : i=0
    · subst i
      simp only [firstReflection_apply,ite_true,PiLp.add_apply,latticeVector,
        Pi.single_eq_same,Int.cast_neg,he]
      ring
    · simp [firstReflection_apply,hi,latticeVector,Pi.single_apply]
  rw [←firstReflection_quotient,hr,quotientMap_add,quotientMap_latticeVector,add_zero]

theorem isMinimizerAt_reflection_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E)) (x : Torus) :
    torusFirstReflection x∈frontier (openRepresentative E) ↔
      x∈frontier (openRepresentative E) := by
  let F := torusFirstReflection ⁻¹' E
  have hF : MeasurableSet F := hE.preimage torusFirstReflection.continuous.measurable
  have hminF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hR).mp hmin
  have he : quotientMap ⁻¹' F=firstReflection ⁻¹' (quotientMap ⁻¹' E) := by
    ext y
    simp only [mem_preimage,firstReflection_quotient,F]
  have hh := isMinimizerAt_lifted_boundary_global hV hF hminF (representative x)
  rw [he] at hh
  have hcover : representative x∈coverEssentialBoundary
      (firstReflection ⁻¹' (quotientMap ⁻¹' E)) ↔
      firstReflection (representative x)∈coverEssentialBoundary (quotientMap ⁻¹' E) :=
    cover_boundary_measurePreserving_homeomorph firstReflection.toHomeomorph
      firstReflection.measurePreserving _
  rw [hcover] at hh
  rw [isMinimizerAt_lifted_boundary_global hV hE hmin,
    firstReflection_quotient,quotientMap_representative] at hh
  rw [←openRepresentative_congr_ae hR] at hh
  exact hh

lemma isMinimizerAt_reflection_normal_scalar {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Torus) (hx : x∈frontier (openRepresentative E)) :
    N (representative (torusFirstReflection x)) 0= -N (representative x) 0 := by
  have hh := isMinimizerAt_reflection_normal hV hE hmin hR hμ hN hp hae
    (representative x) (by simpa only [quotientMap_representative] using hx)
  have hc := congrArg (fun v : Cover ↦ v 0) hh
  simp only [firstReflection_apply,ite_true] at hc
  have hr : N (representative (torusFirstReflection x))=N (firstReflection (representative x)) := by
    have hq : torusFirstReflection x=quotientMap (firstReflection (representative x)) := by
      rw [firstReflection_quotient,quotientMap_representative]
    rw [hq,periodic_representative hp]
  rw [hr]
  exact hc

lemma isMinimizerAt_firstSeam_normal_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Torus) (hx : x∈frontier (openRepresentative E))
    (hz : firstSeamFunction (representative x)=0) : N (representative x) 0=0 := by
  exact isMinimizerAt_reflection_seam_normal hV hE hmin hR hμ hN hp hae
    (representative x) (by simpa only [quotientMap_representative] using hx)
    (firstSeam_zero_fixed _ hz)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_directionalNormalScalar_mean_zero {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover) :
    surfaceMean μ (surfaceSmoothJet μ (directionalNormalScalar N hN hp v))=0 := by
  simp only [directionalNormalScalar,map_sum,map_smul,
    normalComponentScalar_mean_zero hμ hN hp hae,smul_zero,Finset.sum_const_zero]

lemma isMinimizerAt_trace_has_negative {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) (hm : surfaceMean μ (surfaceSmoothJet μ f)=0)
    (hpos : ∃ x∈frontier (openRepresentative E),0<f.val (representative x)) :
    ∃ x∈frontier (openRepresentative E),f.val (representative x)<0 := by
  by_contra! hn
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hnonneg : ∀ᵐ z ∂(μ : Measure NormalBundle),0≤f.val z.1 := by
    filter_upwards [hbd] with z hz
    have hh := hn (normalProjection z) hz
    change 0≤f.val (representative (quotientMap z.1)) at hh
    rwa [periodic_representative f.property.2] at hh
  have hi : Integrable (fun z : NormalBundle ↦ f.val z.1) (μ : Measure NormalBundle) :=
    (smoothScalarValue f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [surfaceMean_of_smooth] at hm
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hm
  obtain ⟨x,hx,hxp⟩ := hpos
  have hx0 := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ f.property.1.continuous
    continuous_const f.property.2 (fun _ _ ↦ rfl) hae (representative x)
    (by simpa only [quotientMap_representative] using hx)
  exact hxp.ne' hx0

lemma isMinimizerAt_negative_unused_patch {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) (hm : surfaceMean μ (surfaceSmoothJet μ f)=0)
    {D A : Set Torus}
    (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D)
    (hA : IsPositiveNodalPiece f (frontier (openRepresentative E)) A) (hDn : D.Nonempty) :
    ∃ U : Set Torus,IsOpen U ∧ (U∩frontier (openRepresentative E)).Nonempty ∧
      Disjoint U D ∧ Disjoint U A := by
  have hdp := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1
  have hap := (positiveNodalPiece_superlevels f isClosed_frontier hA).2.1
  obtain ⟨x,hx⟩ := hDn
  have hxS : x∈frontier (openRepresentative E) := by
    rw [hD.1.choose_spec.2] at hx
    exact hx.1.1
  obtain ⟨y,hy,hyneg⟩ := isMinimizerAt_trace_has_negative hV hE hmin hμ f hm ⟨x,hxS,hdp x hx⟩
  refine ⟨{a | f.val (representative a)<0},
    isOpen_lt (continuous_periodic_descent f.property.1.continuous f.property.2) continuous_const,
    ⟨y,hyneg,hy⟩,?_,?_⟩
  · exact Set.disjoint_left.mpr (fun z hz hd ↦ (hdp z hd).not_gt hz)
  · exact Set.disjoint_left.mpr (fun z hz ha ↦ (hap z ha).not_gt hz)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_SiblingAxialProjection
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

theorem isMinimizerAt_selected_nodal_irreducible {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ (v : Cover) (D A : Set Torus),
        IsPositiveNodalPiece (directionalNormalScalar N hN hp v) (frontier (openRepresentative E)) D →
        IsPositiveNodalPiece (directionalNormalScalar N hN hp v) (frontier (openRepresentative E)) A →
        D.Nonempty → A.Nonempty → ¬Disjoint D A := by
  obtain ⟨μ,H,N,hN,hp,hμ,hae,hb,hs,hj,hunused⟩ := isMinimizerAt_H1_translation_jacobi hV hE hmin
  refine ⟨μ,N,hN,hp,hμ,hae,?_⟩
  intro v D A hD hA hDn hAn hDA
  let f := directionalNormalScalar N hN hp v
  have hjN := directionalNormalScalar_global_jacobi μ N hN hp (fun i ↦ (hj i).2)
  have hjf := hjN v
  obtain ⟨hDm,hdmem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hD
  obtain ⟨hAm,hamem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hA
  let d := nodalSurfaceJet μ f D hDm
  let a := nodalSurfaceJet μ f A hAm
  let u := surfaceNodalBalance μ d a
  have hdnull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f D hDm hdmem hjf
  have hanull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f A hAm hamem hjf
  have horth := surfaceJacobiB_disjoint_nodal μ (surfaceCurvatureLp μ N hN) f f D A hDm hAm hDA
  have humem : u∈surfaceH1 μ := surfaceNodalBalance_mem μ hdmem hamem
  have hunull : surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 :=
    surfaceNodalBalance_null μ _ hdnull hanull horth
  obtain ⟨U,hU,hUn,hUD,hUA⟩ := isMinimizerAt_negative_unused_patch hV hE hmin hμ f
    (sibling_directionalNormalScalar_mean_zero hμ hN hp hae v) hD hA hDn
  have hju : ∀ t∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u t=0 :=
    hunused u humem (surfaceNodalBalance_mean μ d a) hunull U hU hUn
      (surfaceNodalBalance_zero_patch μ (nodalSurfaceJet_zero_outside μ f D U hDm hUD)
        (nodalSurfaceJet_zero_outside μ f A U hAm hUA))
  let F : Torus → ℝ := fun x ↦ surfaceMean μ a*nodalTorusScalar f D x-
    surfaceMean μ d*nodalTorusScalar f A x
  have hFm : Measurable F :=
    (measurable_const.mul (nodalTorusScalar_measurable f hDm)).sub
      (measurable_const.mul (nodalTorusScalar_measurable f hAm))
  have hFc : ContinuousOn F (frontier (openRepresentative E)) :=
    (continuousOn_const.mul (positiveNodalPiece_continuousOn f hD)).sub
      (continuousOn_const.mul (positiveNodalPiece_continuousOn f hA))
  have hFa : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z) :=
    surfaceNodalBalance_scalar_ae μ f f D A hDm hAm
  have hother : (frontier (openRepresentative E)\D).Nonempty := by
    obtain ⟨x,hx⟩ := hAn
    exact ⟨x,positiveNodalPiece_subset f hA hx,fun hd ↦ Set.disjoint_left.mp hDA hd hx⟩
  obtain ⟨x,hcl,hnot⟩ := positiveNodalPiece_boundary_nonempty f hc hD hDn hother
  have hk : surfaceMean μ a≠0 := (isMinimizerAt_nodal_mean_pos hV hE hmin hμ f hAm hA hAn).ne'
  apply isMinimizerAt_nodal_truncation_impossible hV hE hmin hμ hN hp hae hjN f hjf
    humem hju hFm hFc hFa hD hcl hnot hk
  · intro x hx
    have hxA : x∉A := fun ha ↦ Set.disjoint_left.mp hDA hx ha
    simp only [F,nodalTorusScalar,Set.indicator_of_mem hx,Set.indicator_of_notMem hxA,
      mul_zero,sub_zero]
  · intro x hx hle
    have hxD : x∉D := fun hd ↦ ((positiveNodalPiece_superlevels f isClosed_frontier hD).2.1 x hd).not_ge hle
    have hxA : x∉A := fun ha ↦ ((positiveNodalPiece_superlevels f isClosed_frontier hA).2.1 x ha).not_ge hle
    simp only [F,nodalTorusScalar,Set.indicator_of_notMem hxD,Set.indicator_of_notMem hxA,
      mul_zero,sub_zero]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveNodalPiece_relative_compl (f : smoothPeriodicScalars) {S D : Set Torus}
    (hD : IsPositiveNodalPiece f S D) :
    IsPositiveNodalPiece f S ({x | x∈S ∧ 0<f.val (representative x)}\D) := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  constructor
  · refine ⟨Cᶜ,hC.isOpen_compl,?_⟩
    rw [hDC]
    ext x
    simp only [Set.mem_sdiff,mem_inter_iff,mem_ofPred_eq,mem_compl_iff]
    tauto
  · refine ⟨Uᶜ,hU.isClosed_compl,?_⟩
    rw [hDU]
    ext x
    simp only [Set.mem_sdiff,mem_inter_iff,mem_ofPred_eq,mem_compl_iff]
    tauto

lemma positiveBoundaryDomain_preconnected (f : smoothPeriodicScalars) (S : Set Torus)
    (a : positiveBoundaryLocus f S) : IsPreconnected (positiveBoundaryDomain f S a) :=
  isPreconnected_connectedComponent.image _
    (continuous_subtype_val.comp continuous_subtype_val).continuousOn

lemma positiveNodalPiece_eq_positive_locus (f : smoothPeriodicScalars) {S D : Set Torus}
    (hD : IsPositiveNodalPiece f S D) (_hDn : D.Nonempty)
    (hirr : ∀ A : Set Torus,IsPositiveNodalPiece f S A → A.Nonempty → ¬Disjoint D A) :
    D={x | x∈S ∧ 0<f.val (representative x)} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [hD.1.choose_spec.2] at hx
    exact hx.1
  · intro x hx
    by_contra hxD
    apply hirr _ (positiveNodalPiece_relative_compl f hD) ⟨x,hx,hxD⟩
    exact Set.disjoint_left.mpr (fun y hy hA ↦ hA.2 hy)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_translation_signs_preconnected {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ v : Cover,
        IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
          0<⟪v,N (representative x)⟫} ∧
        IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
          ⟪v,N (representative x)⟫<0} := by
  obtain ⟨μ,N,hN,hp,hμ,hae,hirr⟩ :=
    isMinimizerAt_selected_nodal_irreducible hV hE hmin hc
  have hpos (v : Cover) :
      IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
        0<⟪v,N (representative x)⟫} := by
    let f := directionalNormalScalar N hN hp v
    by_cases hn : ({x : Torus | x∈frontier (openRepresentative E) ∧
        0<f.val (representative x)} : Set Torus).Nonempty
    · obtain ⟨x,hxS,hxp⟩ := hn
      let a : positiveBoundaryLocus f (frontier (openRepresentative E)) := ⟨⟨x,hxS⟩,hxp⟩
      let D := positiveBoundaryDomain f (frontier (openRepresentative E)) a
      have hD := isMinimizerAt_actual_nodal_piece hV hE hmin f a
      have hDn := positiveBoundaryDomain_nonempty f (frontier (openRepresentative E)) a
      have heq := positiveNodalPiece_eq_positive_locus f hD hDn (fun A hA hAn ↦
        hirr v D A hD hA hDn hAn)
      have hpD := positiveBoundaryDomain_preconnected f (frontier (openRepresentative E)) a
      rw [heq] at hpD
      simpa only [f,directionalNormalScalar_apply] using hpD
    · have he := Set.not_nonempty_iff_eq_empty.mp hn
      have hem : IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
        0<f.val (representative x)} := he ▸ isPreconnected_empty
      simpa only [f,directionalNormalScalar_apply] using hem
  refine ⟨μ,N,hN,hp,hμ,hae,fun v ↦ ⟨hpos v,?_⟩⟩
  simpa only [inner_neg_left,neg_pos] using hpos (-v)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma odd_preconnected_sign_half {X : Type*} [TopologicalSpace X]
    {S : Set X} {R : X → X} {s u : X → ℝ} (hs : Continuous s)
    (hR : ∀ x∈S,R x∈S) (hsR : ∀ x,s (R x)= -s x)
    (huR : ∀ x∈S,u (R x)= -u x)
    (hz : ∀ x∈S,s x=0 → u x=0)
    (hc : IsPreconnected {x | x∈S ∧ 0<u x}) :
    (∀ x∈S,s x<0 → u x≤0) ∨ (∀ x∈S,s x<0 → 0≤u x) := by
  classical
  by_cases hn : ∃ x∈S,s x<0 ∧ 0<u x
  · right
    obtain ⟨a,ha,has,hau⟩ := hn
    have hP : {x | x∈S ∧ 0<u x}⊆{x | s x<0}∪{x | 0 < s x} := by
      rintro x ⟨hx,hu⟩
      have hne : s x≠0 := fun h ↦ hu.ne' (hz x hx h)
      rcases lt_or_gt_of_ne hne with h|h
      · exact Or.inl h
      · exact Or.inr h
    have hsep : Disjoint {x | s x<0} {x | 0 < s x} := by
      rw [Set.disjoint_left]
      intro x hx hy
      exact (show s x<0 from hx).not_gt (show 0 < s x from hy)
    have hsub := hc.subset_left_of_subset_union (isOpen_lt hs continuous_const)
      (isOpen_lt continuous_const hs) hsep hP ⟨a,⟨ha,hau⟩,has⟩
    intro x hx hxs
    by_contra hneg
    have hu : u x<0 := lt_of_not_ge hneg
    have hh := hsub (show R x∈{x | x∈S ∧ 0<u x} from
      ⟨hR x hx,by rw [huR x hx]; exact neg_pos.mpr hu⟩)
    change s (R x)<0 at hh
    rw [hsR] at hh
    linarith
  · left
    intro x hx hxs
    exact le_of_not_gt (fun hu ↦ hn ⟨x,hx,hxs,hu⟩)

theorem isMinimizerAt_any_normal_signs {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover) :
    IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
      0<⟪v,N (representative x)⟫} ∧
    IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
      ⟪v,N (representative x)⟫<0} := by
  obtain ⟨ν,M,hM,hpM,hν,haM,hs⟩ :=
    Periodic.isMinimizerAt_translation_signs_preconnected hV hE hmin hc
  have he : ∀ x∈frontier (openRepresentative E),N (representative x)=M (representative x) := by
    intro x hx
    obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique hV hE hmin (representative x)
      (by simpa only [quotientMap_representative] using hx)
    exact (hw μ hμ N hN hp hae).trans (hw ν hν M hM hpM haM).symm
  have hpos : {x : Torus | x∈frontier (openRepresentative E) ∧ 0<⟪v,N (representative x)⟫}=
      {x : Torus | x∈frontier (openRepresentative E) ∧ 0<⟪v,M (representative x)⟫} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    by_cases hx : x∈frontier (openRepresentative E)
    · simp only [hx,true_and,he x hx]
    · simp only [hx,false_and]
  have hneg : {x : Torus | x∈frontier (openRepresentative E) ∧ ⟪v,N (representative x)⟫<0}=
      {x : Torus | x∈frontier (openRepresentative E) ∧ ⟪v,M (representative x)⟫<0} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    by_cases hx : x∈frontier (openRepresentative E)
    · simp only [hx,true_and,he x hx]
    · simp only [hx,false_and]
  rw [hpos,hneg]
  exact hs v

theorem isMinimizerAt_reflection_weak_normal_sign_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      N (representative x) 0≤0) ∨
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      0≤N (representative x) 0) := by
  have hsign := (isMinimizerAt_any_normal_signs hV hE hmin hc hμ hN hp hae
    (EuclideanSpace.single 0 1)).1
  have hsign' : IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
      0<N (representative x) 0} := by
    simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hsign
  exact odd_preconnected_sign_half
    (continuous_periodic_descent firstSeamFunction_contDiff.continuous firstSeamFunction_periodic)
    (fun x hx ↦ (isMinimizerAt_reflection_boundary hV hE hmin hR x).mpr hx)
    firstSeam_representative_reflection
    (isMinimizerAt_reflection_normal_scalar hV hE hmin hR hμ hN hp hae)
    (isMinimizerAt_firstSeam_normal_zero hV hE hmin hR hμ hN hp hae) hsign'

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign_oai := @OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign_oai
