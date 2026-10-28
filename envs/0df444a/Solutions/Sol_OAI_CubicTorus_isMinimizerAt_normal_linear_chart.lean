-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_normal_linear_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:58:02.17299+00:00
-- url     : https://prove2.me/submissions/85a84874-ee5e-484c-9a8f-883c639349e9

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_actual_centered_graph_phase_patch
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

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma sublevelCutoff_contDiff {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (t ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelCutoff q t ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const ε)

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

lemma mem_volumeSupport_iff (E : Set Torus) (a : Torus) :
    a ∈ volumeSupport E ↔ ∀ r : ℝ, 0 < r →
      0 < torusVolume.real (E ∩ Metric.ball a r) := by
  rw [volumeSupport, Metric.nhds_basis_ball.mem_measureSupport]
  simp only [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_comm]
  exact forall_congr' fun r ↦ imp_congr_right fun _ ↦
    (ENNReal.toReal_pos_iff.trans (and_iff_left (measure_lt_top _ _))).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma sublevelCutoff_eq_zero {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : t ≤ q x) : sublevelCutoff q t ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

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

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRadialVariation
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
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
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

lemma integral_mul_eq_restrict_of_tsupport {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} {K : Set X} (hK : MeasurableSet K)
    (f q : X → ℝ) (hq : tsupport q ⊆ K) :
    (∫ x, f x * q x ∂μ) = ∫ x in K, f x * q x ∂μ := by
  rw [← integral_indicator hK]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      change f x * q x = 0
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hq h)), mul_zero]

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

lemma graphSmooth_affine (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (m e : ℝ) (x : Plane) :
    m+e*graphSmooth b f x = ∫ y, (m+e*f (x-y)) ∂graphSmoothingMeasure b := by
  rw [integral_add (integrable_const _) ((graphSmooth_integrable b hf x).const_mul e),
    integral_const_mul]
  simp [graphSmooth]

lemma graphSmooth_affine_abs_le (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (m e H : ℝ)
    (hH : ∀ y, |m+e*f y| ≤ H) (x : Plane) : |m+e*graphSmooth b f x| ≤ H := by
  rw [graphSmooth_affine b hf]
  calc
    _ ≤ ∫ y, |m+e*f (x-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, H ∂graphSmoothingMeasure b := by
      apply integral_mono ((integrable_const m).add ((graphSmooth_integrable b hf x).const_mul e)).norm
        (integrable_const _)
      exact fun y ↦ hH _
    _ = _ := by simp

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

lemma cmcWeight_ge_one (p : Plane) : 1 ≤ cmcWeight p := by
  have hp := cmcWeight_sq p
  have hh := cmcWeight_pos p
  nlinarith [sq_nonneg ‖p‖]
lemma cmcWeight_le_two {p : Plane} (hp : ‖p‖≤1) : cmcWeight p≤2 := by
  have hh := cmcWeight_sq p
  nlinarith [sq_nonneg (cmcWeight p),norm_nonneg p]

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

lemma cmcJacobian_coercive {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    (1/8)*‖v‖^2≤⟪v,cmcJacobian p v⟫ := by
  have hs := cmcWeight_pos p
  have hsq := cmcWeight_sq p
  have hcs := real_inner_mul_inner_self_le p v
  simp only [real_inner_self_eq_norm_sq] at hcs
  have h8 : (cmcWeight p)^3≤8 := by
    have hh := cmcWeight_le_two hp
    nlinarith [sq_nonneg (cmcWeight p-2)]
  rw [cmcJacobian_self,le_div_iff₀ (by positivity : 0<(cmcWeight p)^3)]
  have hh := mul_le_mul_of_nonneg_right h8 (sq_nonneg ‖v‖)
  nlinarith [sq_nonneg ⟪p,v⟫]

lemma cmcJacobian_norm_le {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcJacobian p v‖≤2*‖v‖ := by
  have hs := cmcWeight_ge_one p
  have hs0 := cmcWeight_pos p
  have hsi : (cmcWeight p)⁻¹≤1 := inv_le_one₀ hs0 |>.mpr hs
  have hs3 : ((cmcWeight p)^3)⁻¹≤1 := by
    apply (inv_le_one₀ (by positivity : 0<(cmcWeight p)^3)).mpr
    nlinarith [sq_nonneg (cmcWeight p-1)]
  rw [cmcJacobian_apply]
  calc
    _ ≤ ‖(cmcWeight p)⁻¹ • v‖ + ‖(((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p‖ := norm_sub_le _ _
    _ = (cmcWeight p)⁻¹*‖v‖+((cmcWeight p)^3)⁻¹*|⟪p,v⟫| *‖p‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr hs0.le),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs0.le 3))]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add
      · exact mul_le_of_le_one_left (norm_nonneg _) hsi
      · apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hs3) (norm_nonneg _)).trans
        apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
        exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
          (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

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

lemma exists_plane_test_cutoff {R : ℝ} (hR : 0<R) {ψ : Plane → ℝ}
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    ∃ b : ContDiffBump (0 : Plane), b.rOut<R ∧ ∀ y, b y*ψ y=ψ y := by
  obtain ⟨s,hsR,hsb⟩ := exists_lt_subset_ball isClosed_closure hs
  let t := max (R/2) s
  have ht : 0<t := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have htR : t<R := max_lt (by linarith) hsR
  let b : ContDiffBump (0 : Plane) := ⟨t,(t+R)/2,ht,by linarith⟩
  refine ⟨b,by change (t+R)/2<R; linarith,fun y ↦ ?_⟩
  by_cases hy : ψ y=0
  · rw [hy,mul_zero]
  · have hym : y∈Metric.closedBall (0 : Plane) b.rIn :=
      Metric.ball_subset_closedBall ((Metric.ball_subset_ball (le_max_right _ _))
        (hsb (subset_tsupport ψ hy)))
    rw [b.one_of_mem_closedBall hym,one_mul]

theorem exists_C1_test_approximants {R : ℝ} (hR : 0<R) {ψ : Plane → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    ∃ (f : ℕ → Plane → ℝ) (K : Set Plane) (M : ℝ), IsCompact K ∧
      K⊆Metric.ball 0 R ∧ 0≤M ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i) ∧ tsupport (f i)⊆K) ∧
      (∀ i y, ‖f i y‖≤M ∧ ‖fderiv ℝ (f i) y‖≤M) ∧
      (∀ y, Tendsto (fun i ↦ f i y) atTop (𝓝 (ψ y))) ∧
      (∀ y, Tendsto (fun i ↦ fderiv ℝ (f i) y) atTop (𝓝 (fderiv ℝ ψ y))) := by
  obtain ⟨b,hbR,hbψ⟩ := exists_plane_test_cutoff hR hs
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hbc : ContDiff ℝ (⊤ : ℕ∞) b := b.contDiff
  obtain ⟨Lb,hLb⟩ := hbc.lipschitzWith_of_hasCompactSupport b.hasCompactSupport (by simp)
  obtain ⟨C,hC⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hCb (y : Plane) : ‖ψ y‖≤C := hC (mem_range_self y)
  have hC0 : 0≤C := (norm_nonneg (ψ 0)).trans (hCb 0)
  let f (i : ℕ) : Plane → ℝ := fun y ↦ b y*graphSmooth (graphMollifier i) ψ y
  have hfs (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f i) := b.contDiff.mul (graphSmooth_contDiff _ hL)
  have hsm (i : ℕ) (y : Plane) : ‖graphSmooth (graphMollifier i) ψ y‖≤C := by
    simpa only [zero_add,one_mul,Real.norm_eq_abs] using
      graphSmooth_affine_abs_le (graphMollifier i) hL 0 1 C (by simpa only [zero_add,one_mul,Real.norm_eq_abs] using hCb) y
  have hb1 (y : Plane) : ‖b y‖≤1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg b.nonneg] using b.le_one (x := y)
  have hdf (i : ℕ) (y : Plane) : fderiv ℝ (f i) y =
      b y • fderiv ℝ (graphSmooth (graphMollifier i) ψ) y +
      graphSmooth (graphMollifier i) ψ y • fderiv ℝ b y := by
    exact fderiv_fun_mul (hbc.differentiable (by simp)).differentiableAt
      ((graphSmooth_contDiff _ hL).differentiable (by simp)).differentiableAt
  refine ⟨f,tsupport b,C+(L:ℝ)+C*(Lb:ℝ),b.hasCompactSupport,?_,by positivity,
    fun i ↦ ⟨hfs i,tsupport_mul_subset_left⟩,?_,?_,?_⟩
  · rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball hbR
  · intro i y
    constructor
    · have hh : ‖f i y‖≤C := by
        change ‖b y*graphSmooth (graphMollifier i) ψ y‖≤C
        rw [norm_mul]
        exact (mul_le_mul (hb1 y) (hsm i y) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      nlinarith [Lb.coe_nonneg,L.coe_nonneg]
    · rw [hdf]
      calc
        _ ≤ ‖b y • fderiv ℝ (graphSmooth (graphMollifier i) ψ) y‖+
            ‖graphSmooth (graphMollifier i) ψ y • fderiv ℝ b y‖ := norm_add_le _ _
        _ ≤ (L:ℝ)+C*(Lb:ℝ) := by
          simp only [norm_smul]
          apply add_le_add
          · exact (mul_le_mul (hb1 y) (norm_fderiv_le_of_lipschitz ℝ (graphSmooth_lipschitz _ hL))
              (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
          · exact mul_le_mul (hsm i y) (norm_fderiv_le_of_lipschitz ℝ hLb) (norm_nonneg _) hC0
        _ ≤ _ := by linarith
  · intro y
    simpa only [hbψ y] using (graphSmooth_tendsto hL y).const_mul (b y)
  · intro y
    have he : (fun y ↦ b y*ψ y)=ψ := funext hbψ
    have hdp : fderiv ℝ ψ y=b y • fderiv ℝ ψ y+ψ y • fderiv ℝ b y := by
      conv_lhs => rw [← he]
      exact fderiv_fun_mul (hbc.differentiable (by simp)).differentiableAt
        (hψ.differentiable (by simp)).differentiableAt
    rw [hdp]
    simpa only [hdf] using
      ((graphSmooth_fderiv_tendsto hL (hψ.continuous_fderiv (by simp)).continuousAt).const_smul (b y)).add
        ((graphSmooth_tendsto hL y).smul_const (fderiv ℝ b y))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcFlux_norm_le (p : Plane) : ‖cmcFlux p‖≤‖p‖ := by
  change ‖(cmcWeight p)⁻¹ • p‖≤‖p‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (cmcWeight_pos p).le)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ (cmcWeight_pos p)).mpr (cmcWeight_ge_one p))

lemma cmcFlux_difference_bound {p q : Plane} (hp : ‖p‖≤1) (hq : ‖q‖≤1) :
    ‖cmcFlux q-cmcFlux p‖≤2*‖q-p‖ := by
  apply (convex_closedBall (0 : Plane) (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ ↦ (cmcFlux_hasFDerivAt x).differentiableAt) ?_
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hq)
  intro x hx
  rw [(cmcFlux_hasFDerivAt x).fderiv]
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (cmcJacobian_norm_le (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx))

lemma cmcFlux_line_deriv (p q : Plane) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ⟪q-p,cmcFlux (p+s • (q-p))⟫)
      ⟪q-p,cmcJacobian (p+t • (q-p)) (q-p)⟫ t := by
  have hl : HasDerivAt (fun s : ℝ ↦ p+s • (q-p)) (q-p) t := by
    simpa using ((hasDerivAt_id t).smul_const (q-p)).const_add p
  have hh := (hasDerivAt_const t (q-p)).inner ℝ ((cmcFlux_hasFDerivAt _).comp_hasDerivAt t hl)
  simpa [Function.comp_def] using hh

lemma cmcFlux_strong_monotone {p q : Plane} (hp : ‖p‖≤1) (hq : ‖q‖≤1) :
    (1/8)*‖q-p‖^2≤⟪q-p,cmcFlux q-cmcFlux p⟫ := by
  let f : ℝ → ℝ := fun t ↦ ⟪q-p,cmcFlux (p+t • (q-p))⟫
  have hf : Differentiable ℝ f := fun t ↦ (cmcFlux_line_deriv p q t).differentiableAt
  have hb (t : ℝ) (ht : t∈interior (Icc (0:ℝ) 1)) :
      (1/8)*‖q-p‖^2≤deriv f t := by
    rw [(cmcFlux_line_deriv p q t).deriv]
    apply cmcJacobian_coercive
    have htt := interior_subset ht
    have he : p+(q-p)=q := by abel
    have hh := (convex_closedBall (0 : Plane) (1 : ℝ)).add_smul_mem (x := p) (y := q-p)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)
      (by simpa only [he,Metric.mem_closedBall,dist_zero_right] using hq) htt
    simpa only [Metric.mem_closedBall,dist_zero_right] using hh
  have hh := (convex_Icc (0:ℝ) 1).mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn
    hf.differentiableOn hb 0 (by norm_num) 1 (by norm_num) (by norm_num)
  have he : p+(q-p)=q := by abel
  simpa only [f,sub_zero,mul_one,one_smul,zero_smul,add_zero,he,inner_sub_right] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_cmc_gradient (g : Plane → ℝ) : Measurable (fun y ↦ cmcFlux (gradient g y)) :=
  cmcFlux_contDiff.continuous.measurable.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g))

lemma measurable_differential_apply {F : Plane → Plane} (hF : Measurable F) (ψ : Plane → ℝ) :
    Measurable (fun y ↦ fderiv ℝ ψ y (F y)) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp
    ((measurable_fderiv ℝ ψ).prodMk hF)

theorem weak_flux_C1_test {R : ℝ} (hR : 0<R) {F : Plane → Plane}
    (hF : Measurable F) {N : ℝ} (hN : ∀ y, ‖F y‖≤N) (A : ℝ)
    (hw : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ⊆Metric.ball 0 R → (∫ y, fderiv ℝ φ y (F y))=A*(∫ y, φ y))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    (∫ y, fderiv ℝ ψ y (F y))=A*(∫ y, ψ y) := by
  obtain ⟨f,K,M,hK,hKR,hM,hf,hb,ht,hdt⟩ := exists_C1_test_approximants hR hψ hc hs
  have hN0 : 0≤N := (norm_nonneg (F 0)).trans (hN 0)
  let B : Plane → ℝ := K.indicator (fun _ ↦ M*N)
  let C : Plane → ℝ := K.indicator (fun _ ↦ M)
  have hBi : Integrable B := (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hCi : Integrable C := (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have htd : Tendsto (fun i ↦ ∫ y, fderiv ℝ (f i) y (F y)) atTop
      (𝓝 (∫ y, fderiv ℝ ψ y (F y))) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun _ ↦ (measurable_differential_apply hF _).aestronglyMeasurable) hBi
    · intro i
      filter_upwards [] with y
      by_cases hy : y∈K
      · rw [show B y=M*N from indicator_of_mem hy _]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hb i y).2 (hN y) (norm_nonneg _) hM)
      · have hz := fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy ((hf i).2 hy'))
        rw [hz,zero_apply,norm_zero,show B y=0 from indicator_of_notMem hy _]
    · apply Eventually.of_forall
      intro y
      exact ((show Continuous (fun L : Plane →L[ℝ] ℝ ↦ L (F y)) from
        continuous_id.clm_apply continuous_const).tendsto _).comp (hdt y)
  have htv : Tendsto (fun i ↦ ∫ y, f i y) atTop (𝓝 (∫ y, ψ y)) := by
    apply tendsto_integral_of_dominated_convergence C
      (fun i ↦ (hf i).1.continuous.aestronglyMeasurable) hCi
    · intro i
      filter_upwards [] with y
      by_cases hy : y∈K
      · rw [show C y=M from indicator_of_mem hy _]
        exact (hb i y).1
      · have hz : f i y=0 := image_eq_zero_of_notMem_tsupport (fun hy' ↦ hy ((hf i).2 hy'))
        rw [hz,norm_zero,show C y=0 from indicator_of_notMem hy _]
    · exact Eventually.of_forall ht
  have he (i : ℕ) : (∫ y, fderiv ℝ (f i) y (F y))=A*(∫ y, f i y) :=
    hw (f i) (hf i).1 (hK.of_isClosed_subset isClosed_closure (hf i).2) ((hf i).2.trans hKR)
  exact tendsto_nhds_unique htd (by simpa only [he] using htv.const_mul A)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_differential_apply_of_bounded {F : Plane → Plane} (hF : Measurable F)
    {N : ℝ} (hN : ∀ y, ‖F y‖≤N) {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) : Integrable (fun y ↦ fderiv ℝ ψ y (F y)) := by
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hi := (integrableOn_const (μ := (volume : Measure Plane)) (C := (L:ℝ)*N) hc.measure_lt_top.ne).integrable_indicator
    isClosed_closure.measurableSet
  apply hi.mono' (measurable_differential_apply hF ψ).aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : y∈tsupport ψ
  · rw [indicator_of_mem hy]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hN y) (norm_nonneg _) L.coe_nonneg)
  · rw [indicator_of_notMem hy,fderiv_of_notMem_tsupport ℝ hy,zero_apply,norm_zero]

lemma translated_test_support {R r : ℝ} {ψ : Plane → ℝ} {a : Plane}
    (hs : tsupport ψ⊆Metric.ball 0 r) (ha : r+‖a‖≤R) :
    tsupport (fun y ↦ ψ (y-a))⊆Metric.ball 0 R := by
  intro y hy
  have hys := hs (tsupport_comp_subset_preimage ψ (by fun_prop : Continuous (fun y : Plane ↦ y-a)) hy)
  have hh : ‖y-a‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hys
  rw [Metric.mem_ball,dist_zero_right]
  calc
    ‖y‖ = ‖(y-a)+a‖ := by rw [sub_add_cancel]
    _ ≤ ‖y-a‖+‖a‖ := norm_add_le _ _
    _ < r+‖a‖ := by linarith
    _ ≤ R := ha

lemma WeakCMCGraph.translated_test {g : Plane → ℝ} {H R r : ℝ}
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y, fderiv ℝ ψ y (cmcFlux (gradient g (y+a))))=H*(∫ y, ψ y) := by
  let φ : Plane → ℝ := fun y ↦ ψ (y-a)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.sub contDiff_const)
  have hφs := translated_test_support hs ha
  have hφc : HasCompactSupport φ := (isCompact_closedBall (0 : Plane) R).of_isClosed_subset
    isClosed_closure (hφs.trans Metric.ball_subset_closedBall)
  have he := hw φ hφ hφc hφs
  have hd := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ fderiv ℝ φ y (cmcFlux (gradient g y))) a
  have hv := integral_add_right_eq_self (μ := (volume : Measure Plane)) φ a
  simp only [φ,fderiv_comp_sub,add_sub_cancel_right] at hd hv
  simp only [φ,fderiv_comp_sub] at he
  rw [hd,he,← hv]

theorem WeakCMCGraph.difference_test {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {H R r : ℝ} (hr : 0 < r)
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y, fderiv ℝ ψ y (cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)))=0 := by
  have hF := measurable_cmc_gradient g
  have hb (y : Plane) : ‖cmcFlux (gradient g y)‖≤(K:ℝ) := by
    exact (cmcFlux_norm_le _).trans (by rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg)
  have hFm : Measurable (fun y ↦ cmcFlux (gradient g (y+a))) :=
    hF.comp (measurable_id.add_const a)
  have hDb (y : Plane) : ‖cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)‖≤2*(K:ℝ) :=
    (norm_sub_le _ _).trans (by linarith [hb (y+a),hb y])
  apply weak_flux_C1_test hr (hFm.sub hF) hDb 0 ?_ hψ hc hs |>.trans (by simp)
  intro φ hφ hφc hφs
  change (∫ y, fderiv ℝ φ y (cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)))=0*(∫ y, φ y)
  simp_rw [map_sub]
  rw [integral_sub
    (integrable_differential_apply_of_bounded hFm (fun y ↦ hb (y+a)) (hφ.of_le (by simp)) hφc)
    (integrable_differential_apply_of_bounded hF hb (hφ.of_le (by simp)) hφc)]
  rw [hw.translated_test ha hφ hφs,hw φ hφ hφc (hφs.trans (Metric.ball_subset_ball ?_))]
  · simp
  · linarith [norm_nonneg a]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_C1_cutoff_product {U : Set Plane} (hU : IsOpen U)
    {η w : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hw : ContDiffOn ℝ 1 w U)
    (hs : tsupport η⊆U) : ContDiff ℝ 1 (fun y ↦ η y^2*w y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact (hη.contDiffAt.pow 2).mul ((hw y (hs hy)).contDiffAt (hU.mem_nhds (hs hy)))
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma energyTest_tsupport {η w : Plane → ℝ} : tsupport (fun y ↦ η y^2*w y)⊆tsupport η := by
  apply closure_mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support,not_not] at hy ⊢
  simp [hy]

lemma integrable_bounded_compact {f : Plane → ℝ} (hf : Measurable f)
    {K : Set Plane} (hK : IsCompact K) {M : ℝ} (hb : ∀ y, ‖f y‖≤M)
    (hz : ∀ y, y∉K → f y=0) : Integrable f := by
  have hi : Integrable (K.indicator (fun _ : Plane ↦ M)) :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  apply hi.mono' hf.aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : y∈K
  · rw [indicator_of_mem hy]; exact hb y
  · rw [indicator_of_notMem hy,hz y hy,norm_zero]

lemma cmc_energy_absorption {p q : Plane} (hp : ‖p‖≤1) (hq : ‖q‖≤1)
    (a w : ℝ) (L : Plane →L[ℝ] ℝ) :
    (1/16)*a^2*‖q-p‖^2-64*w^2*‖L‖^2 ≤
      a^2*⟪q-p,cmcFlux q-cmcFlux p⟫+2*a*w*L (cmcFlux q-cmcFlux p) := by
  let d := ‖q-p‖
  let F := cmcFlux q-cmcFlux p
  have hc : (1/8)*d^2 ≤ ⟪q-p,F⟫ := cmcFlux_strong_monotone hp hq
  have hF : ‖F‖≤2*d := cmcFlux_difference_bound hp hq
  have hL : |L F|≤2*‖L‖*d := by
    exact (ContinuousLinearMap.le_opNorm L F).trans (by nlinarith [norm_nonneg L])
  have he : |2*a*w*L F|≤4*|a| *|w| *‖L‖*d := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := mul_le_mul_of_nonneg_left hL (show 0≤2*|a| *|w| by positivity)
    nlinarith
  have hn : -(4*|a| *|w| *‖L‖*d)≤2*a*w*L F := (neg_le_neg he).trans (neg_abs_le _)
  have hca := mul_le_mul_of_nonneg_left hc (sq_nonneg a)
  have hs := sq_nonneg (|a| *d/4-8*|w| *‖L‖)
  have ha2 := sq_abs a
  have hw2 := sq_abs w
  change (1/16)*a^2*d^2-64*w^2*‖L‖^2 ≤ a^2*⟪q-p,F⟫+2*a*w*L F
  nlinarith

lemma translated_difference_contDiffOn {g : Plane → ℝ} {R r : ℝ} {a : Plane}
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (ha : r+‖a‖≤R) :
    ContDiffOn ℝ 1 (fun y ↦ g (y+a)-g y) (Metric.ball 0 r) := by
  apply (hg.comp (contDiff_id.add contDiff_const).contDiffOn ?_).sub
    (hg.mono (Metric.ball_subset_ball (by linarith [norm_nonneg a])))
  intro y hy
  rw [Metric.mem_ball,dist_zero_right]
  have hy' : ‖y‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
  change ‖y+a‖<R
  exact (norm_add_le _ _).trans_lt (by linarith)

lemma translated_difference_fderiv {g : Plane → ℝ} {R r : ℝ} {a y : Plane}
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (ha : r+‖a‖≤R)
    (hy : y∈Metric.ball 0 r) (v : Plane) :
    fderiv ℝ (fun y ↦ g (y+a)-g y) y v=⟪gradient g (y+a)-gradient g y,v⟫ := by
  have hy0 : y∈Metric.ball (0 : Plane) R := Metric.ball_subset_ball (by linarith [norm_nonneg a]) hy
  have hya : y+a∈Metric.ball (0 : Plane) R := by
    rw [Metric.mem_ball,dist_zero_right]
    have hh : ‖y‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hd := ((hg y hy0).contDiffAt (Metric.isOpen_ball.mem_nhds hy0)).differentiableAt (by simp)
  have hda := ((hg (y+a) hya).contDiffAt (Metric.isOpen_ball.mem_nhds hya)).differentiableAt (by simp)
  have hdc : DifferentiableAt ℝ (fun y ↦ g (y+a)) y :=
    hda.comp y (differentiableAt_id.add_const a)
  change fderiv ℝ ((fun y ↦ g (y+a))-g) y v=_
  rw [fderiv_sub hdc hd,fderiv_comp_add_right,
    sub_apply,inner_sub_left,inner_gradient_left,inner_gradient_left]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma gradient_difference_norm_le {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (y a : Plane) :
    ‖gradient g (y+a)-gradient g y‖≤2*(K:ℝ) := by
  have hb (x : Plane) : ‖gradient g x‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  exact (norm_sub_le _ _).trans (by linarith [hb (y+a),hb y])

lemma height_difference_norm_le {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (y a : Plane) : ‖g (y+a)-g y‖≤(K:ℝ)*‖a‖ := by
  simpa only [dist_eq_norm,add_sub_cancel_left] using hg.dist_le_mul (y+a) y

lemma measurable_plane_gradient (g : Plane → ℝ) : Measurable (gradient g) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)

lemma cmc_cutoff_energies_integrable {g η : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (a : Plane) :
    Integrable (fun y ↦ η y^2*‖gradient g (y+a)-gradient g y‖^2) ∧
    Integrable (fun y ↦ (g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) := by
  obtain ⟨M,hMb⟩ := hη.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hM (y : Plane) : ‖η y‖≤M := hMb (mem_range_self y)
  have hM0 : 0≤M := (norm_nonneg (η 0)).trans (hM 0)
  obtain ⟨D,hD⟩ := hη.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hDη (y : Plane) := norm_fderiv_le_of_lipschitz ℝ hD (x₀ := y)
  have hgrad := measurable_plane_gradient g
  have hgrad' : Measurable (fun y ↦ gradient g (y+a)-gradient g y) :=
    (hgrad.comp (measurable_id.add_const a)).sub hgrad
  constructor
  · apply integrable_bounded_compact (hη.continuous.measurable.pow_const 2 |>.mul (hgrad'.norm.pow_const 2)) hc
      (M := M^2*(2*(K:ℝ))^2)
    · intro y
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh : η y^2≤M^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (hM y) 2)
      exact mul_le_mul hh (pow_le_pow_left₀ (norm_nonneg _) (gradient_difference_norm_le hg y a) 2)
        (sq_nonneg _) (sq_nonneg M)
    · intro y hy
      dsimp only [Pi.mul_apply]
      rw [image_eq_zero_of_notMem_tsupport hy,zero_pow (by norm_num : 2≠0),zero_mul]
  · have hm : Measurable (fun y ↦ g (y+a)-g y) :=
      (hg.continuous.measurable.comp (measurable_id.add_const a)).sub hg.continuous.measurable
    apply integrable_bounded_compact ((hm.pow_const 2).mul ((measurable_fderiv ℝ η).norm.pow_const 2)) hc
      (M := ((K:ℝ)*‖a‖)^2*(D:ℝ)^2)
    · intro y
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh : (g (y+a)-g y)^2≤((K:ℝ)*‖a‖)^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (height_difference_norm_le hg y a) 2)
      exact mul_le_mul hh (pow_le_pow_left₀ (norm_nonneg _) (hDη y) 2)
        (sq_nonneg _) (sq_nonneg _)
    · intro y hy
      dsimp only [Pi.mul_apply]
      rw [fderiv_of_notMem_tsupport ℝ hy,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero]

theorem WeakCMCGraph.caccioppoli {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R r : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hr : 0 < r)
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : tsupport η⊆Metric.ball 0 r) :
    (∫ y, η y^2*‖gradient g (y+a)-gradient g y‖^2) ≤
      1024*(∫ y, (g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) := by
  let w : Plane → ℝ := fun y ↦ g (y+a)-g y
  let F : Plane → Plane := fun y ↦ cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)
  let ψ : Plane → ℝ := fun y ↦ η y^2*w y
  have hwc := translated_difference_contDiffOn hgc ha
  have hψ : ContDiff ℝ 1 ψ := local_C1_cutoff_product Metric.isOpen_ball hη hwc hs
  have hψs : tsupport ψ⊆tsupport η := energyTest_tsupport
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset isClosed_closure hψs
  have heq : (∫ y, fderiv ℝ ψ y (F y))=0 := hw.difference_test hg hr ha hψ hψc (hψs.trans hs)
  have hb (y : Plane) : ‖gradient g y‖≤1 := by
    rw [plane_gradient_norm]; exact (norm_fderiv_le_of_lipschitz ℝ hg).trans hK
  have hFm : Measurable F :=
    ((measurable_cmc_gradient g).comp (measurable_id.add_const a)).sub (measurable_cmc_gradient g)
  have hFb (y : Plane) : ‖F y‖≤4 := by
    exact (cmcFlux_difference_bound (hb y) (hb (y+a))).trans
      (by nlinarith [gradient_difference_norm_le hg y a])
  have hFi := integrable_differential_apply_of_bounded hFm hFb hψ hψc
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg hη hc a
  have hpoint (y : Plane) :
      (1/16)*(η y^2*‖gradient g (y+a)-gradient g y‖^2)-
        64*((g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) ≤ fderiv ℝ ψ y (F y) := by
    by_cases hy : y∈tsupport η
    · have hdη := hη.differentiable (by simp) y
      have hdw := ((hwc y (hs hy)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hy))).differentiableAt (by simp)
      have hd : fderiv ℝ ψ y (F y) =
          η y^2*⟪gradient g (y+a)-gradient g y,F y⟫+2*η y*w y*fderiv ℝ η y (F y) := by
        change fderiv ℝ (fun z ↦ (η^2) z*(g (z+a)-g z)) y (F y)=_
        rw [fderiv_fun_mul (hdη.pow 2) hdw,fderiv_pow 2 hdη]
        change (η y^2 • fderiv ℝ (fun z ↦ g (z+a)-g z) y + (g (y+a)-g y) •
          ((2 • η y^(2-1)) • fderiv ℝ η y)) (F y)=_
        simp only [add_apply,smul_apply,smul_eq_mul,Nat.reduceSub,pow_one,two_smul]
        rw [translated_difference_fderiv hgc ha (hs hy)]
        ring
      rw [hd]
      convert cmc_energy_absorption (hb y) (hb (y+a)) (η y) (w y) (fderiv ℝ η y) using 1
      all_goals try with_reducible_and_instances rfl
      dsimp only [w,F]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hy,fderiv_of_notMem_tsupport ℝ hy,
        fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hψs h)),zero_apply,norm_zero]
      norm_num
  have hInt := integral_mono ((hAi.const_mul (1/16)).sub (hBi.const_mul 64)) hFi hpoint
  simp only [Pi.sub_apply] at hInt
  rw [integral_sub (hAi.const_mul (1/16)) (hBi.const_mul 64),integral_const_mul,
    integral_const_mul,heq] at hInt
  linarith

end CubicTorus

end
end

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

lemma cmcFlux_quadratic_remainder : ∃ L : ℝ, 0≤L ∧ ∀ p q : Plane,
    ‖p‖≤1 → ‖q‖≤1 →
    ‖cmcFlux q-cmcFlux p-cmcJacobian p (q-p)‖≤L*‖q-p‖^2 := by
  obtain ⟨L,hL⟩ := cmcJacobian_contDiff.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Plane) (1 : ℝ)) (isCompact_closedBall (0 : Plane) (1 : ℝ))
  refine ⟨L,L.coe_nonneg,fun p q hp hq ↦ ?_⟩
  have hp' : p∈Metric.closedBall (0 : Plane) (1 : ℝ) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp
  have hq' : q∈Metric.closedBall (0 : Plane) (1 : ℝ) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hq
  have hs := (convex_closedBall (0 : Plane) (1 : ℝ)).segment_subset hp' hq'
  let F : Plane → Plane := fun x ↦ cmcFlux x-cmcFlux p-cmcJacobian p (x-p)
  have hd (x : Plane) : HasFDerivAt F (cmcJacobian x-cmcJacobian p) x := by
    exact ((cmcFlux_hasFDerivAt x).sub_const (cmcFlux p)).sub
      ((cmcJacobian p).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p)) |>.congr_fderiv
        (by simp)
  have hb (x : Plane) (hx : x∈segment ℝ p q) :
      ‖cmcJacobian x-cmcJacobian p‖≤(L:ℝ)*‖q-p‖ := by
    exact (hL.norm_sub_le (hs hx) hp').trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hx) L.coe_nonneg)
  have hh := (convex_segment p q).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ ↦ (hd x).hasFDerivWithinAt) hb (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  simpa only [F,sub_self,map_zero,sub_zero,mul_assoc,← pow_two] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_derivative_square_integrable {η : Plane → ℝ}
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    Integrable (fun y ↦ ‖fderiv ℝ η y‖^2) := by
  have hd : Continuous (fderiv ℝ η) := hη.continuous_fderiv (by simp)
  have hdc : HasCompactSupport (fderiv ℝ η) := hc.fderiv ℝ
  have hsc : HasCompactSupport (fun y ↦ ‖fderiv ℝ η y‖^2) := by
    apply hdc.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro y hy
    contrapose! hy
    simp only [Function.mem_support,not_not] at hy ⊢
    simp [hy]
  exact (hd.norm.pow 2).integrable_of_hasCompactSupport hsc

theorem WeakCMCGraph.local_gradient_energy {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R r s : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hs : 0 < s) (hsr : s < r)
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ C : ℝ, 0≤C ∧ ∀ a : Plane, r+‖a‖≤R →
      (∫ y in Metric.ball 0 s, ‖gradient g (y+a)-gradient g y‖^2)≤C*‖a‖^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨s,(s+r)/2,hs,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 r := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hi := compact_derivative_square_integrable (b.contDiff (n := 1)) b.hasCompactSupport
  let C : ℝ := 1024*(K:ℝ)^2*(∫ y, ‖fderiv ℝ b y‖^2)
  have hC : 0≤C := by
    dsimp only [C]
    exact mul_nonneg (by positivity) (integral_nonneg (fun _ ↦ sq_nonneg _))
  refine ⟨C,hC,fun a ha ↦ ?_⟩
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg (b.contDiff (n := 1)) b.hasCompactSupport a
  have hbound : (∫ y, (g (y+a)-g y)^2*‖fderiv ℝ b y‖^2)≤
      ((K:ℝ)*‖a‖)^2*(∫ y, ‖fderiv ℝ b y‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono hBi (hi.const_mul _)
    intro y
    have hh : (g (y+a)-g y)^2≤((K:ℝ)*‖a‖)^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using
        (pow_le_pow_left₀ (norm_nonneg _) (height_difference_norm_le hg y a) 2)
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖fderiv ℝ b y‖)]
  calc
    (∫ y in Metric.ball 0 s, ‖gradient g (y+a)-gradient g y‖^2) =
        ∫ y in Metric.ball 0 s, b y^2*‖gradient g (y+a)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      dsimp only
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
      simp
    _ ≤ ∫ y, b y^2*‖gradient g (y+a)-gradient g y‖^2 :=
      setIntegral_le_integral hAi (ae_of_all _ (fun _ ↦ by positivity))
    _ ≤ 1024*(∫ y, (g (y+a)-g y)^2*‖fderiv ℝ b y‖^2) :=
      hw.caccioppoli hg hK hgc (by linarith) ha b.contDiff b.hasCompactSupport hbs
    _ ≤ 1024*(((K:ℝ)*‖a‖)^2*(∫ y, ‖fderiv ℝ b y‖^2)) := by linarith
    _ = C*‖a‖^2 := by dsimp only [C]; ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_DifferenceStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace CubicTorus
universe uHilbert

theorem hilbert_bounded_weak_subsequence {E : Type uHilbert}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (f : ℕ → E) {M : ℝ}
    (hb : ∀ i, ‖f i‖≤M) :
    ∃ (u : E) (φ : ℕ → ℕ), ‖u‖≤M ∧ StrictMono φ ∧
      ∀ v : E, Tendsto (fun i ↦ ⟪f (φ i),v⟫) atTop (𝓝 ⟪u,v⟫) := by
  let F : ℕ → WeakDual ℝ E := fun i ↦ StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ E) (f i))
  have hm (i : ℕ) : F i∈WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) M := by
    simp only [mem_preimage,Metric.mem_closedBall,dist_zero_right]
    change ‖(InnerProductSpace.toDual ℝ E) (f i)‖≤M
    rw [(InnerProductSpace.toDual ℝ E).norm_map]
    exact hb i
  obtain ⟨L,hL,φ,hφ,hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) M) hm
  let u : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L)
  refine ⟨u,φ,?_,hφ,fun v ↦ ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ E).symm _‖≤M
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hL
  · have hh := ((WeakDual.eval_continuous v).tendsto L).comp hlim
    simpa only [F,Function.comp_def,StrongDual.toWeakDual_apply,InnerProductSpace.toDual_apply_apply,
      u,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_difference_quotient_pairing {f ψ : Plane → ℝ}
    (hf : Continuous f) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (v : Plane) :
    (∫ y, (t⁻¹*(f (y+t • v)-f y))*ψ y)=
      ∫ y, (t⁻¹*(ψ (y+t • (-v))-ψ y))*f y := by
  have h₁ : Integrable (fun y ↦ f (y+t • v)*ψ y) :=
    ((hf.comp (continuous_id.add continuous_const)).mul hψ).integrable_of_hasCompactSupport hc.mul_left
  have h₂ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.mul hψ).integrable_of_hasCompactSupport hc.mul_left
  have h₃ : Integrable (fun y ↦ f y*ψ (y+t • (-v))) :=
    (hf.mul (hψ.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.addRight (t • (-v)))).mul_left
  have he : (∫ y, f (y+t • v)*ψ y)=(∫ y, f y*ψ (y+t • (-v))) := by
    rw [← integral_add_right_eq_self _ (t • (-v))]
    simp
  simp_rw [mul_assoc,← mul_comm (f _),sub_mul,mul_sub]
  rw [integral_sub (h₁.const_mul _) (h₂.const_mul _),
    integral_sub (h₃.const_mul _) (h₂.const_mul _),integral_const_mul,integral_const_mul,
    integral_const_mul,he]

theorem continuous_difference_quotient_test_limit {f ψ : Plane → ℝ}
    (hf : Continuous f) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (v : Plane) :
    Tendsto (fun t : ℝ ↦ ∫ y, (t⁻¹*(f (y+t • v)-f y))*ψ y) (𝓝[>] 0)
      (𝓝 (-(∫ y, f y*fderiv ℝ ψ y v))) := by
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hh := LipschitzWith.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
    (μ := (volume : Measure Plane)) hL hc hf (-v)
  have he : (∫ y, lineDeriv ℝ ψ y (-v)*f y)= -(∫ y, f y*fderiv ℝ ψ y v) := by
    simp_rw [(hψ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
      map_neg,neg_mul,integral_neg,mul_comm _ (f _)]
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  exact continuous_difference_quotient_pairing hf hψ.continuous hc t v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_gradient_continuousOn {g : Plane → ℝ} {U : Set Plane}
    (hg : ContDiffOn ℝ 1 g U) (hU : IsOpen U) : ContinuousOn (gradient g) U :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    (hg.continuousOn_fderiv_of_isOpen hU le_rfl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma differenceStep_mem {δ : ℝ} (hδ : 0<δ) (i : ℕ) : differenceStep δ i∈Ioc 0 δ := by
  have hn : (1:ℝ)≤(i:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
  constructor
  · dsimp only [differenceStep]; positivity
  · dsimp only [differenceStep]
    exact mul_le_of_le_one_right hδ.le (by rw [div_le_one (by linarith : (0:ℝ)<(i:ℝ)+1)]; exact hn)

lemma differenceStep_tendsto {δ : ℝ} (hδ : 0<δ) : Tendsto (differenceStep δ) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,Eventually.of_forall (fun i ↦ (differenceStep_mem hδ i).1)⟩
  change Tendsto (fun i : ℕ ↦ δ*(1/((i:ℝ)+1))) atTop (𝓝 0)
  simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ

lemma L2_vector_norm_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Lp Plane 2 μ) : ‖u‖^2=∫ x, ‖u x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem vector_L2_difference_subsequence {f : Plane → Plane}
    (hf : Continuous f) {M : ℝ} (hb : ∀ y, ‖f y‖≤M)
    {r δ C : ℝ} (hδ : 0<δ) (hC : 0≤C) (v : Plane)
    (he : ∀ t∈Ioc 0 δ, (∫ y in Metric.ball 0 r, ‖f (y+t • v)-f y‖^2)≤C*t^2) :
    ∃ (u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))) (φ : ℕ → ℕ),
      ‖u‖≤Real.sqrt C ∧ StrictMono φ ∧
      ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
        Tendsto (fun i ↦ ⟪(vectorDifference_memLp hf hb r (differenceStep δ (φ i)) v).toLp
          (vectorDifference f v (differenceStep δ (φ i))),V⟫) atTop (𝓝 ⟪u,V⟫) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : Fact ((2 : ℝ≥0∞)≠⊤) := ⟨by norm_num⟩
  let Q : ℕ → Lp Plane 2 μ := fun i ↦ (vectorDifference_memLp hf hb r (differenceStep δ i) v).toLp
    (vectorDifference f v (differenceStep δ i))
  have hQ (i : ℕ) : ‖Q i‖≤Real.sqrt C := by
    have heq : ‖Q i‖^2=(differenceStep δ i)⁻¹^2*
        (∫ y in Metric.ball 0 r, ‖f (y+differenceStep δ i • v)-f y‖^2) := by
      rw [L2_vector_norm_sq_integral]
      calc
        _ = ∫ y, ‖vectorDifference f v (differenceStep δ i) y‖^2 ∂μ := integral_congr_ae
          ((vectorDifference_memLp hf hb r (differenceStep δ i) v).coeFn_toLp.mono (fun y hy ↦ by rw [hy]))
        _ = _ := by simp only [vectorDifference,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul,μ]
    have hh := mul_le_mul_of_nonneg_left (he _ (differenceStep_mem hδ i)) (sq_nonneg (differenceStep δ i)⁻¹)
    have htne := (differenceStep_mem hδ i).1.ne'
    have hsq := Real.sq_sqrt hC
    have hre : (differenceStep δ i)⁻¹^2*(C*(differenceStep δ i)^2)=C := by field_simp
    rw [hre,← heq] at hh
    nlinarith [norm_nonneg (Q i),Real.sqrt_nonneg C]
  exact hilbert_bounded_weak_subsequence Q hQ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_vector_cutoff {f : Plane → Plane} {η : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hη : Continuous η)
    (hs : tsupport η⊆U) : Continuous (fun y ↦ η y • f y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.continuousAt.smul ((hf y (hs hy)).continuousAt (hU.mem_nhds (hs hy)))
  · apply (continuousAt_const (y := (0:Plane))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

theorem WeakCMCGraph.gradient_difference_data {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ (G : Plane → Plane) (C : ℝ), Continuous G ∧ (∀ y, ‖G y‖≤1) ∧ 0≤C ∧
      (∀ y, ‖y‖≤R/2 → G y=gradient g y) ∧
      ∀ v : Plane, ‖v‖≤1 → ∀ t∈Ioc 0 (R/4),
        (∫ y in Metric.ball 0 (R/4), ‖G (y+t • v)-G y‖^2)≤C*t^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let G : Plane → Plane := fun y ↦ b y • gradient g y
  have hGc : Continuous G := continuous_local_vector_cutoff Metric.isOpen_ball
    (C1_gradient_continuousOn hgc Metric.isOpen_ball) b.continuous hbs
  have hgrad (y : Plane) : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hGb (y : Plane) : ‖G y‖≤1 := by
    dsimp only [G]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg b.nonneg]
    exact ((mul_le_mul_of_nonneg_left (hgrad y) b.nonneg).trans
      (mul_le_of_le_one_left K.coe_nonneg b.le_one)).trans hK
  have hGeq {y : Plane} (hy : ‖y‖≤R/2) : G y=gradient g y := by
    dsimp only [G]
    rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy),one_smul]
  obtain ⟨C,hC,henergy⟩ := hw.local_gradient_energy hg hK hgc
    (show 0<R/4 by linarith) (show R/4<R/2 by linarith)
  refine ⟨G,C,hGc,hGb,hC,fun _ hy ↦ hGeq hy,fun v hv t ht ↦ ?_⟩
  have ha : ‖t • v‖≤t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact mul_le_of_le_one_right ht.1.le hv
  calc
    _ = ∫ y in Metric.ball 0 (R/4), ‖gradient g (y+t • v)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      have hy' : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      dsimp only
      rw [hGeq ((norm_add_le y (t • v)).trans (by linarith [ht.2])),hGeq (by linarith)]
    _ ≤ C*‖t • v‖^2 := henergy (t • v) (by linarith [ht.2])
    _ ≤ C*t^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha 2) hC

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem vector_weak_quotient_derivative {f : Plane → Plane} (hf : Continuous f)
    {r : ℝ} {t : ℕ → ℝ} (htlim : Tendsto t atTop (𝓝[>] 0)) (v w : Plane)
    {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i, (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y in Metric.ball 0 r, ⟪u y,w⟫*ψ y)= -(∫ y, ⟪f y,w⟫*fderiv ℝ ψ y v) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let W : Plane → Plane := fun y ↦ ψ y • w
  have hWc : Continuous W := hψ.continuous.smul continuous_const
  have hWs : HasCompactSupport W := hc.smul_right
  have hWm : MemLp W 2 μ := hWc.memLp_of_hasCompactSupport hWs
  let V : Lp Plane 2 μ := hWm.toLp W
  have hp (i : ℕ) : ⟪Q i,V⟫=(∫ y, ((t i)⁻¹*(⟪f (y+t i • v),w⟫-⟪f y,w⟫))*ψ y) := by
    rw [L2.inner_def,integral_mul_eq_restrict_of_tsupport measurableSet_ball _ ψ hs]
    apply integral_congr_ae
    filter_upwards [hQ i,hWm.coeFn_toLp] with y hy hy'
    rw [hy,hy']
    simp only [W,vectorDifference,inner_smul_right,inner_smul_left,inner_sub_left,RCLike.conj_to_real]
    ring
  have hup : ⟪u,V⟫=(∫ y in Metric.ball 0 r, ⟪u y,w⟫*ψ y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWm.coeFn_toLp] with y hy
    rw [hy]
    simp only [W,inner_smul_right]
    ring
  have hlim₁ := hw V
  simp_rw [hp,hup] at hlim₁
  have hlim₂ := (continuous_difference_quotient_test_limit (hf.inner (continuous_const (y := w))) hψ hc v).comp htlim
  exact tendsto_nhds_unique hlim₁ hlim₂

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem weak_L2_cmc_chain {f : Plane → Plane} (hf : Continuous f)
    (hb : ∀ y, ‖f y‖≤1) {r C : ℝ} (hC : 0≤C) {t : ℕ → ℝ}
    (ht : ∀ i, 0<t i) (htlim : Tendsto t atTop (𝓝 0))
    (v : Plane)
    (henergy : ∀ i, (∫ y in Metric.ball 0 r, ‖f (y+t i • v)-f y‖^2)≤C*(t i)^2)
    {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i, (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ y in Metric.ball 0 r,
      fderiv ℝ ψ y ((t i)⁻¹ • (cmcFlux (f (y+t i • v))-cmcFlux (f y)))) atTop
      (𝓝 (∫ y in Metric.ball 0 r, fderiv ℝ ψ y (cmcJacobian (f y) (u y)))) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  obtain ⟨B,hB,hrem⟩ := cmcFlux_quadratic_remainder
  have hgrad (y : Plane) : ‖gradient ψ y‖≤(L:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hL
  let W : Plane → Plane := fun y ↦ cmcJacobian (f y) (gradient ψ y)
  have hWcont : Continuous W := (cmcJacobian_contDiff.continuous.comp hf).clm_apply
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ.continuous_fderiv (by simp)))
  have hWb (y : Plane) : ‖W y‖≤2*(L:ℝ) :=
    (cmcJacobian_norm_le (hb y) _).trans (by gcongr; exact hgrad y)
  have hW : MemLp W 2 μ := MemLp.of_bound hWcont.aestronglyMeasurable (C := 2*(L:ℝ)) (Eventually.of_forall hWb)
  let V : Lp Plane 2 μ := hW.toLp W
  have hid (y z : Plane) : ⟪z,W y⟫=fderiv ℝ ψ y (cmcJacobian (f y) z) := by
    dsimp only [W]
    rw [cmcJacobian_symmetric,real_inner_comm,inner_gradient_left]
  have hp (i : ℕ) : ⟪Q i,V⟫=(∫ y, fderiv ℝ ψ y (cmcJacobian (f y) (vectorDifference f v (t i) y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQ i,hW.coeFn_toLp] with y hy hy'
    rw [hy,hy',hid]
  have hup : ⟪u,V⟫=(∫ y, fderiv ℝ ψ y (cmcJacobian (f y) (u y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hW.coeFn_toLp] with y hy
    rw [hy,hid]
  have hlim := hw V
  rw [hup] at hlim
  simp_rw [hp] at hlim
  let Err : ℕ → Plane → ℝ := fun i y ↦ fderiv ℝ ψ y ((t i)⁻¹ •
    (cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)))
  have herr (i : ℕ) : ‖∫ y, Err i y ∂μ‖≤((L:ℝ)*B*C)*t i := by
    have hti : 0<(t i)⁻¹ := inv_pos.mpr (ht i)
    have hei : Integrable (fun y ↦ ‖f (y+t i • v)-f y‖^2) μ := by
      apply (integrable_const (4:ℝ)).mono' (by fun_prop)
      filter_upwards [] with y
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hh : ‖f (y+t i • v)-f y‖≤2 := (norm_sub_le _ _).trans (by linarith [hb (y+t i • v),hb y])
      nlinarith [norm_nonneg (f (y+t i • v)-f y)]
    calc
      _ ≤ ∫ y, ((L:ℝ)*B*(t i)⁻¹)*‖f (y+t i • v)-f y‖^2 ∂μ := by
        apply norm_integral_le_of_norm_le (hei.const_mul _)
        filter_upwards [] with y
        dsimp only [Err]
        calc
          _ ≤ (L:ℝ)*‖(t i)⁻¹ • (cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y))‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
              (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))
          _ = (L:ℝ)*((t i)⁻¹*‖cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)‖) := by
            rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (ht i))]
          _ ≤ (L:ℝ)*((t i)⁻¹*(B*‖f (y+t i • v)-f y‖^2)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (hrem _ _ (hb y) (hb (y+t i • v))) hti.le) L.coe_nonneg
          _ = _ := by ring
      _ = ((L:ℝ)*B*(t i)⁻¹)*(∫ y, ‖f (y+t i • v)-f y‖^2 ∂μ) := integral_const_mul _ _
      _ ≤ ((L:ℝ)*B*(t i)⁻¹)*(C*(t i)^2) := by
        simpa only [mul_comm] using mul_le_mul (henergy i)
          (le_refl ((L:ℝ)*B*(t i)⁻¹)) (by positivity) (mul_nonneg hC (sq_nonneg (t i)))
      _ = _ := by field_simp
  have herrlim : Tendsto (fun i ↦ ∫ y, Err i y ∂μ) atTop (𝓝 0) :=
    squeeze_zero_norm herr (by simpa using htlim.const_mul ((L:ℝ)*B*C))
  have hsum := hlim.add herrlim
  simp only [add_zero] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  have hEi : Integrable (Err i) μ := by
    apply (integrable_const ((L:ℝ)*(t i)⁻¹*8)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      dsimp only [Err]
      have hD := hψ.continuous_fderiv (by simp)
      have hF := cmcFlux_contDiff.continuous
      have hJ := cmcJacobian_contDiff.continuous
      fun_prop
    · filter_upwards [] with y
      dsimp only [Err]
      have hrem8 : ‖cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)‖≤8 := by
        have hd : ‖f (y+t i • v)-f y‖≤2 := (norm_sub_le _ _).trans (by linarith [hb (y+t i • v),hb y])
        have h₁ := cmcFlux_difference_bound (hb y) (hb (y+t i • v))
        have h₂ := cmcJacobian_norm_le (hb y) (f (y+t i • v)-f y)
        exact (norm_sub_le _ _).trans (by linarith)
      calc
        _ ≤ (L:ℝ)*‖(t i)⁻¹ • (cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y))‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
            (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))
        _ = (L:ℝ)*((t i)⁻¹*‖cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)‖) := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (ht i))]
        _ ≤ (L:ℝ)*((t i)⁻¹*8) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrem8 (inv_pos.mpr (ht i)).le) L.coe_nonneg
        _ = _ := by ring
  have hJi : Integrable (fun y ↦ fderiv ℝ ψ y (cmcJacobian (f y) (vectorDifference f v (t i) y))) μ := by
    have hi := L2.integrable_inner (𝕜 := ℝ) (Q i) V
    apply hi.congr
    filter_upwards [hQ i,hW.coeFn_toLp] with y hy hy'
    rw [hy,hy',hid]
  rw [← integral_add hJi hEi]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp only [Err,vectorDifference]
  simp only [map_sub,map_smul,smul_eq_mul]
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

lemma differential_integral_restrict {ψ : Plane → ℝ} {S : Set Plane}
    (hs : tsupport ψ⊆S) (F : Plane → Plane) :
    (∫ y in S, fderiv ℝ ψ y (F y))=(∫ y, fderiv ℝ ψ y (F y)) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy (hs hy')),zero_apply]

theorem WeakCMCGraph.linearized_equation {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hcmc : WeakCMCGraph g H (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      (∀ (w : Plane) (ψ : Plane → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), ⟪u y,w⟫*ψ y)=
          -(∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v)) ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (gradient g y) (u y)))=0) := by
  obtain ⟨G,C,hGc,hGb,hC,hGeq,henergy⟩ := hcmc.gradient_difference_data hg hK hR hgc
  have hδ : 0<R/4 := by linarith
  obtain ⟨u,φ,_hu,hφ,hw⟩ := vector_L2_difference_subsequence hGc hGb hδ hC v (henergy v hv)
  let t : ℕ → ℝ := fun i ↦ differenceStep (R/4) (φ i)
  let Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))) := fun i ↦
    (vectorDifference_memLp hGc hGb (R/4) (t i) v).toLp (vectorDifference G v (t i))
  have ht (i : ℕ) : t i∈Ioc 0 (R/4) := differenceStep_mem hδ (φ i)
  have htlim : Tendsto t atTop (𝓝[>] 0) := (differenceStep_tendsto hδ).comp hφ.tendsto_atTop
  have hQ (i : ℕ) : (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) (R/4))]
      vectorDifference G v (t i) := (vectorDifference_memLp hGc hGb (R/4) (t i) v).coeFn_toLp
  have hweak : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫) := hw
  have hty (i : ℕ) : ‖t i • v‖≤t i := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (ht i).1]
    exact mul_le_of_le_one_right (ht i).1.le hv
  have hGy (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) : G y=gradient g y := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    linarith
  have hGyt (i : ℕ) (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) :
      G (y+t i • v)=gradient g (y+t i • v) := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact (norm_add_le _ _).trans (by linarith [hty i,(ht i).2])
  refine ⟨u,?_,?_⟩
  · intro w ψ hψ hc hs
    rw [vector_weak_quotient_derivative hGc htlim v w hQ hweak hψ hc hs]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈tsupport ψ
    · rw [hGy y (hs hy)]
    · rw [fderiv_of_notMem_tsupport ℝ hy,zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    have hlim := weak_L2_cmc_chain hGc hGb hC (fun i ↦ (ht i).1)
      (tendsto_nhds_of_tendsto_nhdsWithin htlim) v (fun i ↦ henergy v hv (t i) (ht i)) hQ hweak hψ hc
    have hzero (i : ℕ) : (∫ y in Metric.ball 0 (R/4),
        fderiv ℝ ψ y ((t i)⁻¹ • (cmcFlux (G (y+t i • v))-cmcFlux (G y))))=0 := by
      calc
        _ = ∫ y in Metric.ball 0 (R/4),
            fderiv ℝ ψ y ((t i)⁻¹ • (cmcFlux (gradient g (y+t i • v))-cmcFlux (gradient g y))) := by
          apply setIntegral_congr_fun measurableSet_ball
          intro y hy
          dsimp only
          rw [hGy y hy,hGyt i y hy]
        _ = ∫ y, fderiv ℝ ψ y ((t i)⁻¹ •
            (cmcFlux (gradient g (y+t i • v))-cmcFlux (gradient g y))) := differential_integral_restrict hs _
        _ = (t i)⁻¹*(∫ y, fderiv ℝ ψ y
            (cmcFlux (gradient g (y+t i • v))-cmcFlux (gradient g y))) := by
          simp only [map_smul,smul_eq_mul,integral_const_mul]
        _ = 0 := by
          rw [hcmc.difference_test hg hδ (by linarith [hty i,(ht i).2]) hψ hc hs,mul_zero]
    have he : (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (G y) (u y)))=0 :=
      tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)
    rw [← he]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    dsimp only
    rw [hGy y hy]

end CubicTorus

end
end

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

lemma C1_mixed_test_identity {g ψ : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hg : Continuous g) (hgc : ContDiffOn ℝ 1 g S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S)
    (v w : Plane) :
    (∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v)=
      (∫ y, ⟪gradient g y,v⟫*fderiv ℝ ψ y w) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ ψ y w) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  simp only [inner_gradient_left]
  rw [C1_local_integration_by_parts hS hg hgc (hv.of_le (by simp))
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset (f := ψ) ℝ v).trans hs) w,
    C1_local_integration_by_parts hS hg hgc (hw.of_le (by simp))
    (hc.fderiv_apply ℝ w) ((tsupport_fderiv_apply_subset (f := ψ) ℝ w).trans hs) v]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  rw [fderiv_fderiv_apply hψ,fderiv_fderiv_apply hψ]
  exact (hψ.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) w v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma indicator_inner_test_integral {S : Set Plane} (hS : MeasurableSet S)
    (U : Plane → Plane) (v : Plane) (ψ : Plane → ℝ) :
    (∫ y,⟪S.indicator U y,v⟫*ψ y)=(∫ y in S,⟪U y,v⟫*ψ y) := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈S <;> simp [hy]

lemma indicator_differential_integral {S : Set Plane} (hS : MeasurableSet S)
    (U : Plane → Plane) (A : Plane → Plane →L[ℝ] Plane) (ψ : Plane → ℝ) :
    (∫ y,fderiv ℝ ψ y (A y (S.indicator U y)))=
      (∫ y in S,fderiv ℝ ψ y (A y (U y))) := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈S <;> simp [hy]

theorem WeakCMCGraph.scalar_linearized_equation {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hcmc : WeakCMCGraph g H (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ (u : Lp ℝ 2 (volume : Measure Plane)) (U : Lp Plane 2 (volume : Measure Plane)),
      (u : Plane → ℝ)=ᵐ[volume.restrict (Metric.ball 0 (R/4))]
        (fun y ↦ fderiv ℝ g y v) ∧
      PlaneWeakGradient (Metric.ball 0 (R/4)) u U ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y,fderiv ℝ ψ y (cmcJacobian (gradient g y) (U y)))=0) := by
  let S : Set Plane := Metric.ball 0 (R/4)
  obtain ⟨F,hF,hlin⟩ := hcmc.linearized_equation hg hK hR hgc v hv
  have hFmem : MemLp (S.indicator (F : Plane → Plane)) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp F)
  let U := hFmem.toLp (S.indicator (F : Plane → Plane))
  let b : ContDiffBump (0 : Plane) := ⟨R/4,R/2,by linarith,by linarith⟩
  let f : Plane → ℝ := fun y ↦ fderiv ℝ g y v*b y
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hfc : Continuous f := continuous_local_scalar_product Metric.isOpen_ball
    ((hgc.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply continuousOn_const)
    b.continuous hbs
  have hfs : HasCompactSupport f := b.hasCompactSupport.mul_left
  have hfmem : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport hfs
  let u := hfmem.toLp f
  have hfe (y : Plane) (hy : y∈S) : f y=fderiv ℝ g y v := by
    dsimp only [f]
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),mul_one]
  refine ⟨u,U,?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hfmem.coeFn_toLp,ae_restrict_mem (measurableSet_ball : MeasurableSet S)] with y hy hs
    exact hy.trans (hfe y hs)
  · intro w ψ hψ hc hs
    have hψs : tsupport ψ⊆Metric.ball 0 R := hs.trans (Metric.ball_subset_ball (by linarith))
    calc
      _ = ∫ y,⟪S.indicator (F : Plane → Plane) y,w⟫*ψ y := by
        apply integral_congr_ae
        filter_upwards [hFmem.coeFn_toLp] with y hy
        rw [hy]
      _ = ∫ y in S,⟪F y,w⟫*ψ y := indicator_inner_test_integral measurableSet_ball _ _ _
      _ = -(∫ y,⟪gradient g y,w⟫*fderiv ℝ ψ y v) := hF w ψ (hψ.of_le (by simp)) hc hs
      _ = -(∫ y,⟪gradient g y,v⟫*fderiv ℝ ψ y w) := by
        rw [C1_mixed_test_identity Metric.isOpen_ball hg.continuous hgc hψ hc hψs v w]
      _ = -(∫ y,u y*fderiv ℝ ψ y w) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hfmem.coeFn_toLp] with y hy
        rw [hy,inner_gradient_left]
        by_cases hyS : y∈S
        · rw [hfe y hyS]
        · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hyS (hs h)),zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    calc
      _ = ∫ y,fderiv ℝ ψ y (cmcJacobian (gradient g y) (S.indicator (F : Plane → Plane) y)) := by
        apply integral_congr_ae
        filter_upwards [hFmem.coeFn_toLp] with y hy
        rw [hy]
      _ = ∫ y in S,fderiv ℝ ψ y (cmcJacobian (gradient g y) (F y)) :=
        indicator_differential_integral measurableSet_ball _ _ _
      _ = 0 := hlin ψ (hψ.of_le (by simp)) hc hs

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CmcStretch
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

lemma cmcJacobian_uniform_lipschitz : ∃ L : ℝ,0≤L ∧ ∀ p q : Plane,
    ‖p‖≤1 → ‖q‖≤1 → ‖cmcJacobian p-cmcJacobian q‖≤L*‖p-q‖ := by
  obtain ⟨L,hL⟩ := cmcJacobian_contDiff.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Plane) (1 : ℝ)) (isCompact_closedBall (0 : Plane) (1 : ℝ))
  refine ⟨L,L.coe_nonneg,fun p q hp hq ↦ ?_⟩
  exact hL.norm_sub_le (by simpa using hp) (by simpa using hq)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_weak_gradient {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (S : Set Plane) : PlaneWeakGradient S f (gradient f) := by
  intro v ψ hψ hc _hs
  have hi₁ : Integrable (fun y ↦ fderiv ℝ f y v*ψ y) :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hi₂ : Integrable (fun y ↦ f y*fderiv ℝ ψ y v) :=
    (hf.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun _ _ ↦ (hf.differentiable (by simp)).differentiableAt)
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [inner_gradient_left,neg_neg] using congrArg Neg.neg hh.symm

lemma PlaneWeakGradient.local_congr {S : Set Plane} (hS : MeasurableSet S)
    {u u' : Plane → ℝ} {G G' : Plane → Plane} (h : PlaneWeakGradient S u G)
    (hu : u'=ᵐ[volume.restrict S] u) (hG : G'=ᵐ[volume.restrict S] G) :
    PlaneWeakGradient S u' G' := by
  have hu' := (ae_restrict_iff' hS).mp hu
  have hG' := (ae_restrict_iff' hS).mp hG
  intro v ψ hψ hc hs
  have hleft : (∫ y,⟪G' y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) := by
    apply integral_congr_ae
    filter_upwards [hG'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hys (hs hh)),mul_zero,mul_zero]
  have hright : (∫ y,u' y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) := by
    apply integral_congr_ae
    filter_upwards [hu'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hys (hs hh)),zero_apply,mul_zero,mul_zero]
  rw [hleft,hright]
  exact h v ψ hψ hc hs

lemma PlaneWeakGradient.unique {S : Set Plane} (hS : IsOpen S)
    {u : Plane → ℝ} {G H : Plane → Plane}
    (hG : LocallyIntegrable G volume) (hH : LocallyIntegrable H volume)
    (huG : PlaneWeakGradient S u G) (huH : PlaneWeakGradient S u H) :
    G=ᵐ[volume.restrict S] H := by
  have hz := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hG.sub hH).locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · change ∀ᵐ y ∂volume.restrict S, G y = H y
    rw [ae_restrict_iff' hS.measurableSet]
    filter_upwards [hz] with y hy hys
    exact sub_eq_zero.mp (hy hys)
  · have hiG := hG.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    have hiH := hH.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    simp only [Pi.sub_apply,smul_sub,integral_sub hiG hiH]
    apply sub_eq_zero.mpr
    apply ext_inner_left ℝ
    intro v
    rw [← integral_inner hiG v,← integral_inner hiH v]
    simp only [inner_smul_right]
    simp_rw [real_inner_comm (G _) v,real_inner_comm (H _) v]
    simpa only [mul_comm] using (huG v ψ hψ hc hs).trans (huH v ψ hψ hc hs).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma PlaneWeakGradient.mono {S T : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hTS : T⊆S) : PlaneWeakGradient T u G := by
  intro v ψ hψ hc hs
  exact h v ψ hψ hc (hs.trans hTS)

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

lemma LinearCMCEquation.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane} {U : Set Plane}
    (hU : IsOpen U) (hw : LinearCMCEquation g p B U)
    (hg : EqOn g' g U) (hp : EqOn p' p U) (hB : EqOn B' B U) : LinearCMCEquation g' p' B' U := by
  intro ψ hψ hc hs
  rw [← hw ψ hψ hc hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ by
    dsimp only
    by_cases hy : y∈U
    · have he : g'=ᶠ[𝓝 y]g := by
        filter_upwards [hU.mem_nhds hy] with z hz
        exact hg hz
      have hG : gradient g' y=gradient g y := congrArg
        (fun L : Plane →L[ℝ] ℝ ↦ (InnerProductSpace.toDual ℝ Plane).symm L) he.fderiv_eq
      rw [hG,hp hy,hB hy]
    · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hs h))]; rfl

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.continuousAt [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : HolderNear f x) : ContinuousAt f x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  have hd : Tendsto (fun y : E ↦ dist y x) (𝓝 x) (𝓝 0) := by
    simpa only [id_eq,dist_self] using ((continuous_id : Continuous (fun y : E ↦ y)).dist (continuous_const (y := x))).tendsto x
  have hlim : Tendsto (fun y : E ↦ C*(dist y x)^α) (𝓝 x) (𝓝 0) := by
    simpa only [Real.zero_rpow hα.ne',mul_zero] using (hd.rpow_const (Or.inr hα.le)).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hlim
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  exact hH y hy x (Metric.mem_ball_self hr)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.eventually [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : HolderNear f x) : ∀ᶠ y in 𝓝 x,HolderNear f y := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  filter_upwards [Metric.ball_mem_nhds x (by linarith : 0 < r/2)] with y hy
  have hsub : Metric.ball y (r/2)⊆Metric.ball x r := by
    intro z hz
    have hz' := Metric.mem_ball.mp hz
    have hy' := Metric.mem_ball.mp hy
    have ht := dist_triangle z y x
    exact Metric.mem_ball.mpr (by linarith)
  exact ⟨r/2,α,C,by linarith,hα,hα1,hC,fun z hz w hw ↦ hH z (hsub hz) w (hsub hw)⟩

lemma HolderNear.contDiffAt_zero {f : E → F} {x : E} (hf : HolderNear f x) : ContDiffAt ℝ 0 f x := by
  obtain ⟨s,hS,hsc,hs⟩ := eventually_nhds_iff.mp hf.eventually
  exact _root_.contDiffAt_zero.mpr ⟨s,hsc.mem_nhds hs,fun y hy ↦ (hS y hy).continuousAt.continuousWithinAt⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.congr [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (hf : HolderNear f x) (he : f=ᶠ[𝓝 x]g) : HolderNear g x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,hs,hsE⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min r s,α,C,lt_min hr hs,hα,hα1,hC,?_⟩
  intro y hy z hz
  have hyR := (Metric.ball_subset_ball (min_le_left r s)) hy
  have hzR := (Metric.ball_subset_ball (min_le_left r s)) hz
  rw [← hsE ((Metric.ball_subset_ball (min_le_right r s)) hy),
    ← hsE ((Metric.ball_subset_ball (min_le_right r s)) hz)]
  exact hH y hyR z hzR

lemma ContDiffAt.holderNear {f : E → F} {x : E} (hf : ContDiffAt ℝ 1 f x) : HolderNear f x := by
  obtain ⟨C,S,hS,hLip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨r,1,C,hr,by norm_num,le_rfl,C.coe_nonneg,?_⟩
  intro y hy z hz
  simpa only [Real.rpow_one] using hLip.dist_le_mul y (hrS hy) z (hrS hz)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
lemma HolderNear.prodMk [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E}
    (hf : HolderNear f x) (hg : HolderNear g x) : HolderNear (fun y ↦ (f y,g y)) x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,β,D,hs,hβ,hβ1,hD,hJ⟩ := hg
  let ρ := min (min r s) (1/2)
  have hρ : 0<ρ := lt_min (lt_min hr hs) (by norm_num)
  have hρr : ρ ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hρs : ρ≤ s := (min_le_left _ _).trans (min_le_right _ _)
  have hρα : ρ≤1/2 := min_le_right _ _
  refine ⟨ρ,min α β,C+D,hρ,lt_min hα hβ,(min_le_left _ _).trans hα1,add_nonneg hC hD,?_⟩
  intro y hy z hz
  have hd : dist y z≤1 := by
    have hy' := Metric.mem_ball.mp hy
    have hz' := Metric.mem_ball.mp hz
    have ht := dist_triangle_right y z x
    linarith
  have hhα : (dist y z)^α≤(dist y z)^(min α β) :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd (le_min hα.le hβ.le) (min_le_left _ _)
  have hhβ : (dist y z)^β≤(dist y z)^(min α β) :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd (le_min hα.le hβ.le) (min_le_right _ _)
  rw [Prod.dist_eq]
  apply max_le
  · exact ((hH y ((Metric.ball_subset_ball hρr) hy) z ((Metric.ball_subset_ball hρr) hz)).trans
      (mul_le_mul_of_nonneg_left hhα hC)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))
  · exact ((hJ y ((Metric.ball_subset_ball hρs) hy) z ((Metric.ball_subset_ball hρs) hz)).trans
      (mul_le_mul_of_nonneg_left hhβ hD)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))

lemma ContDiffAt.comp_holderNear {f : E → F} {g : F → G} {x : E}
    (hg : ContDiffAt ℝ 1 g (f x)) (hf : HolderNear f x) : HolderNear (g ∘ f) x := by
  obtain ⟨K,S,hS,hLip⟩ := hg.exists_lipschitzOnWith
  have hfcont := hf.continuousAt
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,hs,hsS⟩ := Metric.mem_nhds_iff.mp (hfcont hS)
  refine ⟨min r s,α,(K:ℝ)*C,lt_min hr hs,hα,hα1,mul_nonneg K.coe_nonneg hC,?_⟩
  intro y hy z hz
  calc
    _ ≤ (K:ℝ)*dist (f y) (f z) := hLip.dist_le_mul (f y)
      (hsS ((Metric.ball_subset_ball (min_le_right r s)) hy)) (f z)
      (hsS ((Metric.ball_subset_ball (min_le_right r s)) hz))
    _ ≤ (K:ℝ)*(C*(dist y z)^α) := mul_le_mul_of_nonneg_left
      (hH y ((Metric.ball_subset_ball (min_le_left r s)) hy)
        z ((Metric.ball_subset_ball (min_le_left r s)) hz)) K.coe_nonneg
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HolderJet.congr {n : ℕ} {f g : E → F} {x : E} (hf : HolderJet n f x)
    (he : f=ᶠ[𝓝 x]g) : HolderJet n g x := by
  induction n generalizing F with
  | zero => exact hf.congr he
  | succ n ih =>
    exact ⟨hf.1.congr_of_eventuallyEq he.symm,ih hf.2 he.fderiv⟩

lemma HolderJet.pred {n : ℕ} {f : E → F} {x : E} (hf : HolderJet (n+1) f x) : HolderJet n f x := by
  induction n generalizing F with
  | zero => exact ContDiffAt.holderNear hf.1
  | succ n ih => exact ⟨hf.1,ih hf.2⟩

lemma HolderJet.contDiffAt {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) : ContDiffAt ℝ n f x := by
  induction n generalizing F with
  | zero => exact HolderNear.contDiffAt_zero hf
  | succ n ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fderiv ℝ f,?_,ih hf.2⟩
    have hdiff : ∀ᶠ y in 𝓝 x,DifferentiableAt ℝ f y :=
      (hf.1.eventually (by simp)).mono fun _ hy ↦ hy.differentiableAt_one
    exact ⟨{y|DifferentiableAt ℝ f y},hdiff,fun y hy ↦ hy.hasFDerivAt⟩

lemma ContDiffAt.holderJet {n : ℕ} {f : E → F} {x : E} (hf : ContDiffAt ℝ (n+1) f x) : HolderJet n f x := by
  induction n generalizing F with
  | zero => exact ContDiffAt.holderNear hf
  | succ n ih =>
    refine ⟨hf.of_le (by norm_cast; omega),?_⟩
    exact ih (hf.fderiv_right (by norm_cast))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HolderJet.eventually {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) :
    ∀ᶠ y in 𝓝 x,HolderJet n f y := by
  induction n generalizing F with
  | zero => exact HolderNear.eventually hf
  | succ n ih => exact (hf.1.eventually (by simp)).and (ih hf.2)

lemma HolderJet.clm_comp {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x)
    (L : F →L[ℝ] G) : HolderJet n (L ∘ f) x := by
  induction n generalizing F G with
  | zero => exact ContDiffAt.comp_holderNear L.contDiff.contDiffAt hf
  | succ n ih =>
    refine ⟨L.contDiff.contDiffAt.comp x hf.1,?_⟩
    apply (ih hf.2 (ContinuousLinearMap.compL ℝ E F G L)).congr
    filter_upwards [hf.1.eventually (by simp)] with y hy
    exact ((L.hasFDerivAt).comp y hy.differentiableAt_one.hasFDerivAt).fderiv.symm

lemma HolderJet.prodMk {n : ℕ} {f : E → F} {g : E → G} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ (f y,g y)) x := by
  induction n generalizing F G with
  | zero => exact HolderNear.prodMk hf hg
  | succ n ih =>
    refine ⟨hf.1.prodMk hg.1,?_⟩
    have hh := (ih hf.2 hg.2).clm_comp
      (ContinuousLinearMap.prodₗᵢ ℝ (E := E) (F := F) (G := G)).toContinuousLinearEquiv.toContinuousLinearMap
    apply hh.congr
    filter_upwards [hf.1.eventually (by simp),hg.1.eventually (by simp)] with y hy hz
    exact (hy.differentiableAt_one.fderiv_prodMk hz.differentiableAt_one).symm

lemma HolderJet.smooth_comp {n : ℕ} {f : E → F} {g : F → G} {x : E}
    (hf : HolderJet n f x) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : HolderJet n (g ∘ f) x := by
  induction n generalizing E F G with
  | zero => exact ContDiffAt.comp_holderNear (hg.of_le (by simp)).contDiffAt hf
  | succ n ih =>
    refine ⟨(hg.of_le (by simp)).contDiffAt.comp x hf.1,?_⟩
    have hDg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hpair := (ih hf.pred hDg).prodMk hf.2
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (F →L[ℝ] G)×(E →L[ℝ] F) ↦ p.1.comp p.2) := contDiff_fst.clm_comp contDiff_snd
    apply (ih hpair hcomp).congr
    filter_upwards [hf.1.eventually (by simp)] with y hy
    exact (fderiv_comp y (hg.differentiable (by simp) (f y)) hy.differentiableAt_one).symm

lemma HolderJet.const {n : ℕ} {x : E} (c : F) : HolderJet n (fun _ : E ↦ c) x :=
  ContDiffAt.holderJet contDiffAt_const

lemma HolderJet.clm_apply {n : ℕ} {f : E → F →L[ℝ] G} {g : E → F} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ f y (g y)) x :=
  (hf.prodMk hg).smooth_comp (contDiff_fst.clm_apply contDiff_snd)

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

section

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HolderJet.directional {n : ℕ} {f : Plane → ℝ} {x : Plane}
    (hf : HolderJet (n+1) f x) (v : Plane) : HolderJet n (fun y ↦ fderiv ℝ f y v) x :=
  hf.2.clm_apply (HolderJet.const v)

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

section

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace CubicTorus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_C1_lipschitz {f : E → F} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ K : ℝ≥0,LipschitzWith K f := by
  obtain ⟨C,hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  refine ⟨Real.toNNReal C,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) fun x ↦ ?_⟩
  apply NNReal.coe_le_coe.mp
  exact (hC x).trans (Real.le_coe_toNNReal C)

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace CubicTorus

lemma HolderJet.extension {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : Plane → F} (hf : HolderJet (n+1) f 0) :
    ∃ (f' : Plane → F) (K : ℝ≥0) (M : ℝ),
      ContDiff ℝ (n+1) f' ∧ HasCompactSupport f' ∧ LipschitzWith K f' ∧
      (∀ y,‖f' y‖≤M) ∧ (∀ y,‖f' y‖≤‖f y‖) ∧
      f'=ᶠ[𝓝 0]f ∧ HolderJet (n+1) f' 0 := by
  obtain ⟨r,hr,hjets⟩ := Metric.mem_nhds_iff.mp hf.eventually
  have hfc : ContDiffOn ℝ (n+1) f (Metric.ball 0 r) := fun y hy ↦
    (hjets hy).contDiffAt.contDiffWithinAt
  let b : ContDiffBump (0 : Plane) := ⟨r/2,3*r/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 r := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f' : Plane → F := fun y ↦ b y • f y
  have hc : ContDiff ℝ (n+1) f' := contDiff_local_vector_cutoff Metric.isOpen_ball hfc b.contDiff hbs
  have hcs : HasCompactSupport f' := b.hasCompactSupport.smul_right
  obtain ⟨K,hK⟩ := compact_C1_lipschitz (hc.of_le (by norm_cast; omega)) hcs
  obtain ⟨M,hM⟩ := hcs.exists_bound_of_continuous hc.continuous
  have he : f'=ᶠ[𝓝 0]f := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (by linarith : 0 < r/2)] with y hy
    dsimp only [f']
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_smul]
  refine ⟨f',K,M,hc,hcs,hK,hM,?_,he,hf.congr he.symm⟩
  intro y
  dsimp only [f']
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg b.nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) b.le_one

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquationNear.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane}
    (hw : LinearCMCEquationNear g p B)
    (hg : g'=ᶠ[𝓝 0]g) (hp : p'=ᶠ[𝓝 0]p) (hB : B'=ᶠ[𝓝 0]B) : LinearCMCEquationNear g' p' B' := by
  obtain ⟨R,hR,hw⟩ := hw
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp (hg.and (hp.and hB))
  refine ⟨min r R,lt_min hr hR,?_⟩
  have hsub : Metric.ball (0 : Plane) (min r R)⊆Metric.ball 0 r := Metric.ball_subset_ball (min_le_left _ _)
  exact (hw.mono (Metric.ball_subset_ball (min_le_right _ _))).congr Metric.isOpen_ball
    (fun _ hy ↦ (he (hsub hy)).1) (fun _ hy ↦ (he (hsub hy)).2.1) (fun _ hy ↦ (he (hsub hy)).2.2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem WeakCMCGraph.directional_linear_near {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hgJ : HolderJet 2 g 0)
    (v : Plane) (hv : ‖v‖≤1) :
    LinearCMCEquationNear (fun y ↦ fderiv ℝ g y v) (gradient g) (fun _ ↦ 0) := by
  obtain ⟨d,Kd,Md,hdc,_,_,_,_,hde,_⟩ := (hgJ.directional v).extension
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp hde
  obtain ⟨u,G,hue,hug,hlin⟩ := hw.scalar_linearized_equation hg hK hR hgc v hv
  let s := min r (R/4)
  have hs : 0 < s := lt_min hr (by linarith)
  have hsr : s ≤ r := min_le_left _ _
  have hsR : s≤R/4 := min_le_right _ _
  have hsub : Metric.ball (0 : Plane) s⊆Metric.ball 0 (R/4) := Metric.ball_subset_ball hsR
  have hdu : PlaneWeakGradient (Metric.ball 0 s) d G := by
    apply (hug.mono hsub).local_congr measurableSet_ball ?_ EventuallyEq.rfl
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hue,
      ae_restrict_mem measurableSet_ball] with y hy hyS
    exact (he ((Metric.ball_subset_ball hsr) hyS)).trans hy.symm
  have hgradc : Continuous (gradient d) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hdc.continuous_fderiv (by simp))
  have hGe := PlaneWeakGradient.unique Metric.isOpen_ball
    ((Lp.memLp G).locallyIntegrable (by norm_num)) hgradc.locallyIntegrable hdu (C1_weak_gradient hdc _)
  have hw' : LinearCMCEquationNear d (gradient g) (fun _ ↦ 0) := by
    refine ⟨s,hs,?_⟩
    intro ψ hψ hc hψs
    simp only [sub_zero]
    rw [← hlin ψ hψ hc (hψs.trans hsub)]
    apply integral_congr_ae
    have het := (ae_restrict_iff' measurableSet_ball).mp hGe
    filter_upwards [het] with y hy
    by_cases hys : y∈Metric.ball (0 : Plane) s
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hys (hψs h))]; rfl
  exact hw'.congr hde.symm EventuallyEq.rfl EventuallyEq.rfl

end CubicTorus

end
end

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

theorem graphJacobiForm_transform {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAs : ∀ y v w,⟪v,A y w⟫=⟪w,A y v⟫)
    {q φ ψ : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    graphJacobiForm A q φ ψ=
      ∫ y,⟪gradient (fun z ↦ q z*φ z) y,A y (gradient (fun z ↦ q z*ψ z) y)⟫ := by
  have hgq := plane_gradient_contDiff hq
  have hgφ := plane_gradient_contDiff hφ
  have hgψ := plane_gradient_contDiff hψ
  let F : Plane → Plane := fun y ↦ A y (gradient q y)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hA.clm_apply hgq
  have htest : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ q y*φ y*ψ y) := (hq.mul hφ).mul hψ
  have htestc : HasCompactSupport (fun y ↦ q y*φ y*ψ y) := hc.mul_left
  have hibp := plane_divergence_integration_by_parts (hF.of_le (by simp))
    (htest.of_le (by simp)) htestc
  have hmain : Integrable (fun y ↦ (q y)^2*⟪gradient φ y,A y (gradient ψ y)⟫) := by
    apply ((hq.continuous.pow 2).mul (hgφ.continuous.inner (hA.continuous.clm_apply hgψ.continuous))).integrable_of_hasCompactSupport
    apply hc.mono'
    intro y hy
    by_contra hys
    have he := fderiv_of_notMem_tsupport ℝ hys
    have hge : gradient ψ y=0 := by simp [gradient,he]
    simp [hge] at hy
  have hpot : Integrable (fun y ↦ q y*planeDivergence F y*φ y*ψ y) :=
    (((hq.continuous.mul (planeDivergence_continuous (hF.of_le (by simp)))).mul hφ.continuous).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross : Integrable (fun y ↦ fderiv ℝ (fun z ↦ q z*φ z*ψ z) y (F y)) :=
    ((htest.continuous_fderiv (by simp)).clm_apply hF.continuous).integrable_of_hasCompactSupport
      (htestc.mono' (by
        intro y hy
        by_contra hn
        have he := fderiv_of_notMem_tsupport ℝ hn
        simp [he] at hy))
  have hpoint (y : Plane) :
      ⟪gradient (fun z ↦ q z*φ z) y,A y (gradient (fun z ↦ q z*ψ z) y)⟫=
        (q y)^2*⟪gradient φ y,A y (gradient ψ y)⟫+
          fderiv ℝ (fun z ↦ q z*φ z*ψ z) y (F y) := by
    rw [plane_gradient_mul (hq.differentiable (by simp) y) (hφ.differentiable (by simp) y),
      plane_gradient_mul (hq.differentiable (by simp) y) (hψ.differentiable (by simp) y)]
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      fderiv_fun_mul ((hq.mul hφ).differentiable (by simp) y) (hψ.differentiable (by simp) y),
      fderiv_fun_mul (hq.differentiable (by simp) y) (hφ.differentiable (by simp) y),
      add_apply,smul_apply,smul_eq_mul]
    simp only [← inner_gradient_left,F]
    rw [hAs y (gradient q y) (gradient ψ y)]
    ring
  unfold graphJacobiForm
  rw [integral_sub hmain hpot]
  simp_rw [hpoint]
  rw [integral_add hmain hcross]
  have he : (∫ y,q y*planeDivergence F y*φ y*ψ y)=
      -(∫ y,fderiv ℝ (fun z ↦ q z*φ z*ψ z) y (F y)) := by
    convert hibp using 1
    all_goals try with_reducible_and_instances rfl
    congr 1; funext y; ring
  rw [he,sub_neg_eq_add]

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

lemma cmcGraphJacobi_div_transform {g f ψ : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    cmcGraphJacobi g (fun y ↦ f y/cmcWeight (gradient g y)) ψ=
      ∫ y,⟪gradient f y,cmcJacobian (gradient g y)
        (gradient (fun z ↦ cmcWeight (gradient g z)*ψ z) y)⟫ := by
  have hp := plane_gradient_contDiff hg
  have hq := cmcWeight_contDiff.comp hp
  have he (y : Plane) : cmcWeight (gradient g y)*(f y/cmcWeight (gradient g y))=f y := by
    exact mul_div_cancel₀ _ (cmcWeight_pos _).ne'
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcJacobian (gradient g y)) :=
    cmcJacobian_contDiff.comp hp
  have hq' : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcWeight (gradient g y)) := hq
  have hquot : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ f y/cmcWeight (gradient g y)) :=
    hf.div hq (fun y ↦ (cmcWeight_pos _).ne')
  have ht := graphJacobiForm_transform hA
    (fun y v w ↦ (cmcJacobian_symmetric (gradient g y) v w).trans (real_inner_comm _ _)) hq'
    hquot hψ hc
  have hefun : (fun z ↦ cmcWeight (gradient g z)*(f z/cmcWeight (gradient g z)))=f := funext he
  rw [hefun] at ht
  exact ht

theorem LinearCMCEquation.normal_jacobi {g f : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hw : LinearCMCEquation f (gradient g) (fun _ ↦ 0) U)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆U) :
    cmcGraphJacobi g (fun y ↦ f y/cmcWeight (gradient g y)) ψ=0 := by
  rw [cmcGraphJacobi_div_transform hg hf hψ hc]
  have hq := cmcWeight_contDiff.comp (plane_gradient_contDiff hg)
  have hh := hw (fun y ↦ cmcWeight (gradient g y)*ψ y) (hq.mul hψ) hc.mul_left
    (tsupport_mul_subset_right.trans hs)
  simp only [sub_zero,← inner_gradient_left] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext y
  rw [cmcJacobian_symmetric,real_inner_comm]

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

theorem WeakCMCGraph.coordinate_jacobi_chart {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ (f : Plane → ℝ) (r : ℝ),0 < r ∧ r≤R ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      EqOn f g (Metric.ball 0 r) ∧
      (∀ i : Fin 2,LinearCMCEquation (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1))
        (gradient f) (fun _ ↦ 0) (Metric.ball 0 r)) ∧
      ∀ i : Fin 2,∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 r →
        cmcGraphJacobi f (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1)/
          cmcWeight (gradient f y)) ψ=0 := by
  obtain ⟨f,hfc,hfe⟩ := smooth_graph_extension hR hgc
  have he : f=ᶠ[𝓝 0]g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0 : Plane)∈Metric.ball 0 (R/2) by simp; linarith)] with y hy
    exact hfe hy
  have hgc0 : ContDiffAt ℝ (⊤ : ℕ∞) g 0 := hgc.contDiffAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hR))
  have hnear (i : Fin 2) : LinearCMCEquationNear
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f) (fun _ ↦ 0) := by
    have hh := hw.directional_linear_near hg hK hR (hgc.of_le (by simp))
      (ContDiffAt.holderJet (n := 2) (hgc0.of_le (by
        change ((3 : ℕ∞) : WithTop ℕ∞)≤↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)))
      (EuclideanSpace.single i 1) (by simp)
    apply hh.congr
    · exact (he.fderiv (𝕜 := ℝ)).mono fun _ hy ↦ congrArg (fun L : Plane →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hy
    · exact (he.fderiv (𝕜 := ℝ)).mono fun _ hy ↦ by simp only [gradient,hy]
    · exact EventuallyEq.rfl
  obtain ⟨r0,hr0,h0⟩ := hnear 0
  obtain ⟨r1,hr1,h1⟩ := hnear 1
  let r := min (R/2) (min r0 r1)
  have hr : 0 < r := lt_min (by linarith) (lt_min hr0 hr1)
  have hrR : r≤R/2 := min_le_left _ _
  have hlin (i : Fin 2) : LinearCMCEquation (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1))
      (gradient f) (fun _ ↦ 0) (Metric.ball 0 r) := by
    fin_cases i
    · exact h0.mono (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)))
    · exact h1.mono (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨f,r,hr,by linarith,hfc,hfe.mono (Metric.ball_subset_ball hrR),hlin,?_⟩
  intro i ψ hψ hc hs
  exact (hlin i).normal_jacobi hfc
    ((hfc.fderiv_right (by simp)).clm_apply contDiff_const) hψ hc hs

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceNormalReverse
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

lemma smooth_graph_extension_compact {g : Plane → ℝ} {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ (f : Plane → ℝ) (K : ℝ≥0),ContDiff ℝ (⊤ : ℕ∞) f ∧
      HasCompactSupport f ∧ LipschitzWith K f ∧ EqOn f g (Metric.ball 0 (R/2)) := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f : Plane → ℝ := fun y => b y*g y
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_local_vector_cutoff Metric.isOpen_ball hg b.contDiff hs
  have hfc : HasCompactSupport f := b.hasCompactSupport.mul_right
  obtain ⟨K,hK⟩ := compact_C1_lipschitz (hf.of_le (by simp)) hfc
  refine ⟨f,K,hf,hfc,hK,?_⟩
  intro y hy
  change b y*g y=g y
  rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]

lemma smooth_graph_symbol_extension {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hK : (K : ℝ)≤1) {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ (p : Plane → Plane) (D : ℝ),ContDiff ℝ (⊤ : ℕ∞) p ∧
      (∀ y,‖p y‖≤1) ∧ 0≤D ∧ EqOn p (gradient g) (Metric.ball 0 (R/2)) ∧
      ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hgD : ContDiffOn ℝ (⊤ : ℕ∞) (gradient g) (Metric.ball 0 R) := by
    intro y hy
    have hd := (hg.contDiffAt (Metric.isOpen_ball.mem_nhds hy)).fderiv_right
      (m := (⊤ : ℕ∞)) (by simp)
    exact ((InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
      y hd).contDiffWithinAt
  let p : Plane → Plane := fun y => b y • gradient g y
  have hp : ContDiff ℝ (⊤ : ℕ∞) p :=
    contDiff_local_vector_cutoff Metric.isOpen_ball hgD b.contDiff hs
  have hpc : HasCompactSupport p := b.hasCompactSupport.smul_right
  obtain ⟨C,hC⟩ := compact_C1_lipschitz (hp.of_le (by simp)) hpc
  have hpb (y : Plane) : ‖p y‖≤1 := by
    have hgrad : ‖gradient g y‖≤K := by
      simpa only [gradient,LinearIsometryEquiv.norm_map] using
        norm_fderiv_le_of_lipschitz ℝ hgL (x₀ := y)
    change ‖b y • gradient g y‖≤1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (b.nonneg (x := y))]
    exact ((mul_le_mul_of_nonneg_right (b.le_one (x := y)) (norm_nonneg _)).trans
      (by simpa using hgrad)).trans hK
  obtain ⟨L,hL,hLip⟩ := cmcJacobian_uniform_lipschitz
  refine ⟨p,L*C,hp,hpb,mul_nonneg hL C.coe_nonneg,?_,?_⟩
  · intro y hy
    change b y • gradient g y=gradient g y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_smul]
  · intro x y
    calc
      _ ≤ L*‖p x-p y‖ := hLip _ _ (hpb x) (hpb y)
      _ ≤ L*(C*dist x y) := mul_le_mul_of_nonneg_left
        (by simpa only [← dist_eq_norm] using hC.dist_le_mul x y) hL
      _ = _ := by ring

theorem WeakCMCGraph.smooth_jacobi_data {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hK : (K : ℝ)≤1) {R H : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ (f : Plane → ℝ) (Kf : ℝ≥0) (p : Plane → Plane) (r D : ℝ),
      0 < r ∧ r≤R/2 ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      LipschitzWith Kf f ∧ EqOn f g (Metric.ball 0 (R/2)) ∧
      ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ y,‖p y‖≤1) ∧ 0≤D ∧
      EqOn p (gradient f) (Metric.ball 0 r) ∧
      (∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y) ∧
      ∀ i : Fin 2,LinearCMCEquation
        (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f)
        (fun _ => 0) (Metric.ball 0 r) := by
  obtain ⟨f,Kf,hf,hfc,hfL,hfg⟩ := smooth_graph_extension_compact hR hg
  obtain ⟨p,D,hp,hpb,hD,hpg,hpD⟩ := smooth_graph_symbol_extension hgL hK hR hg
  obtain ⟨f₀,r₀,hr₀,_,hf₀,hf₀g,hlin,_⟩ := hw.coordinate_jacobi_chart hgL hK hR hg
  let r := min (R/2) r₀
  have hr : 0 < r := lt_min (half_pos hR) hr₀
  have hrR : r≤R/2 := min_le_left _ _
  have hr0 : r ≤ r₀ := min_le_right _ _
  have he (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) : f=ᶠ[𝓝 y]g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hrR hy)] with z hz
    exact hfg hz
  have he0 (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) : f=ᶠ[𝓝 y]f₀ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    exact (hfg (Metric.ball_subset_ball hrR hz)).trans
      (hf₀g (Metric.ball_subset_ball hr0 hz)).symm
  refine ⟨f,Kf,p,r,D,hr,hrR,hf,hfc,hfL,hfg,hp,hpb,hD,?_,hpD,?_⟩
  · intro y hy
    rw [hpg (Metric.ball_subset_ball hrR hy)]
    simp only [gradient,(he y hy).fderiv_eq]
  · intro i
    apply LinearCMCEquation.congr Metric.isOpen_ball
      ((hlin i).mono (Metric.ball_subset_ball hr0))
    · intro y hy
      exact congrArg (fun L : Plane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) (he0 y hy).fderiv_eq
    · intro y hy
      simp only [gradient,(he0 y hy).fderiv_eq]
    · intro y hy; rfl

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

theorem actual_centered_normal_linear_chart {V : ℝ} (hV : V∈Ioo 0 1)
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
      (∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v) ∧
      ∃ r : ℝ,0 < r ∧ (∀ y∈Metric.ball (0 : Plane) r,‖gradient f y‖≤1) ∧
        ∀ i : Fin 2,LinearCMCEquation
          (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f)
          (fun _ => 0) (Metric.ball 0 r) := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,hw,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,Kf,p,rj,D,hrj,hrjr,hf,hfc,hfL,hfg,hp0,hpb,hD,hpf,hpD,hlin⟩ :=
    hw.smooth_jacobi_data hg (by norm_num) hr hgc
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
  let F : Cover → Cover := fun x ↦ φ x • (N x-σ • graphUnitNormalExtension cubeCenter n f x)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hφ.smul
    (hN.sub ((graphUnitNormalExtension_contDiff _ hn hf).const_smul σ))
  have hsF : HasCompactSupport F := hsφ.smul_right
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    (tsupport_smul_subset_left _ _).trans hφO
  have he := latticePeriodize_eventuallyEq hsF hFO
    (show ∀ i,0 ≤ cubeCenter i ∧ cubeCenter i≤1 by intro i; norm_num [cubeCenter])
  have hz : ∀ᵐ z ∂(μ : Measure NormalBundle),latticePeriodize F z.1=(0 : Cover) := by
    filter_upwards [hae,hσae] with z hz hloc
    rw [(latticePeriodize_eventuallyEq hsF hFO (compactCell_coordinates z.1)).eq_of_nhds]
    change φ z.1 • (N z.1-σ • graphUnitNormalExtension cubeCenter n f z.1)=0
    by_cases hpos : 0<φ z.1
    · rw [hz,hloc hpos,sub_self,smul_zero]
    · have hzφ : φ z.1=0 := le_antisymm (le_of_not_gt hpos) (hφb z.1).1
      rw [hzφ,zero_smul]
  have hb (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      latticePeriodize F x=0 := by
    have hboundary : latticePeriodize F x+N x=N x :=
      isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
        ((latticePeriodize_contDiff hF hsF).continuous.add hN.continuous) hN.continuous
        (fun shift point => by simp only [Pi.add_apply,latticePeriodize_periodic,hp]) hp
        (hz.mono fun point hzero => by simp only [Pi.add_apply,hzero,zero_add]) x hx
    exact add_right_cancel (hboundary.trans (zero_add _).symm)
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
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_,rj,hrj,?_,hlin⟩
  ·
    filter_upwards [ht.eventually he,ht.eventually hone,Metric.ball_mem_nhds (0 : Plane) (half_pos hr)]
      with y hey hoy hy
    have hgraph : normalGraph n f y=normalGraph n g y := by simp only [normalGraph,hfg hy]
    have hby : quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E) := by
      rw [quotientMap_add,hgraph]
      exact hi y ((Metric.ball_subset_ball (by linarith)) hy)
    have hzero := hb _ hby
    rw [hey] at hzero
    change φ (cubeCenter+normalGraph n f y) •
      (N (cubeCenter+normalGraph n f y)-σ • graphUnitNormalExtension cubeCenter n f
        (cubeCenter+normalGraph n f y))=0 at hzero
    rw [hoy,one_smul,graphUnitNormalExtension_graph cubeCenter hn f f y] at hzero
    exact ⟨sub_eq_zero.mp hzero,hby⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Cover) (half_pos hr)] with v hv
    have hpv : normalPlaneCoordinates n v∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right] at hv ⊢
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt hv
    rw [hcover' v hv]
    simp only [normalGraph,hfg hpv]

  · intro y hy
    rw [← hpf hy]
    exact hpb y

theorem isMinimizerAt_normal_linear_chart_oai {V : ℝ} (hV : V∈Ioo 0 1)
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
      (∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v) ∧
      ∃ r : ℝ,0 < r ∧ (∀ y∈Metric.ball (0 : Plane) r,‖gradient f y‖≤1) ∧
        ∀ i : Fin 2,LinearCMCEquation
          (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f)
          (fun _ => 0) (Metric.ball 0 r) := by
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
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm,hcov,hlin⟩ := actual_centered_normal_linear_chart hV hE' hmin' hc
    (isNormalMeasure_translation hE hμ a) hN' hp' hae'
  have ht (v : Cover) : (cubeCenter+v)+a=x+v := by dsimp [a]; abel
  have htrans (v : Cover) : quotientMap (cubeCenter+v)∈frontier (openRepresentative E') ↔
      quotientMap (x+v)∈frontier (openRepresentative E) := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap (cubeCenter+v)+quotientMap a∈frontier (openRepresentative E) ↔ _
    rw [← quotientMap_add,ht]
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_,hlin⟩
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

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_normal_linear_chart_oai := @OAI.CubicTorus.isMinimizerAt_normal_linear_chart_oai
