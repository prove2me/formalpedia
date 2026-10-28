-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_axial_local_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:31:28.871004+00:00
-- url     : https://prove2.me/submissions/686677fa-b130-43a8-9413-970772e3438d

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_actual_centered_graph_phase_patch
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normal_linear_chart
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
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
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
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
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
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
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
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
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
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlaneAreaCoordinates
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

lemma normalPlaneEmbedding_coordinates_of_inner_zero {n x : Cover} (hn : ‖n‖ = 1)
    (hx : ⟪n,x⟫ = 0) : normalPlaneEmbedding n (normalPlaneCoordinates n x) = x := by
  obtain ⟨⟨t,y⟩,rfl⟩ := (normalColumnChart 0 n).surjective x
  have ht : t = 0 := by
    have hh := normalColumnChart_height 0 hn t y
    simp only [sub_zero] at hh
    exact hh.symm.trans hx
  rw [ht,normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add,
    normalPlaneCoordinates_embedding]

lemma normalPlaneCoordinates_norm_of_inner_zero {n x : Cover} (hn : ‖n‖ = 1)
    (hx : ⟪n,x⟫ = 0) : ‖normalPlaneCoordinates n x‖ = ‖x‖ := by
  rw [← normalPlaneEmbedding_norm n,normalPlaneEmbedding_coordinates_of_inner_zero hn hx]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_ComponentDivergence
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

lemma cover_decompose (v : Cover) : v=∑ i : Fin 3,v i • EuclideanSpace.single i 1 := by
  ext j
  simp [Pi.single_apply]

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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_MinimalGraphDensity
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

lemma normalPlaneEmbedding_inner_coordinates {n : Cover} (hn : ‖n‖=1) (y : Plane) (x : Cover) :
    ⟪normalPlaneEmbedding n y,x⟫ = ⟪y,normalPlaneCoordinates n x⟫ := by
  conv_lhs => rhs; rw [← normalPlaneCoordinates_reconstruct hn x]
  have hz : ⟪normalPlaneEmbedding n y,n⟫=0 :=
    (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn y)
  rw [inner_add_right,inner_smul_right,hz,mul_zero,add_zero]
  exact (normalPlaneLinearIsometry n).inner_map_map y (normalPlaneCoordinates n x)

lemma normalGraph_coordinates_eq_iff {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (x : Cover) :
    normalGraph n g (normalPlaneCoordinates n x)=x ↔ g (normalPlaneCoordinates n x)=⟪n,x⟫ := by
  constructor
  · intro hh
    simpa only [normalGraph_inner hn] using congrArg (fun v : Cover ↦ ⟪n,v⟫) hh
  · intro hh
    rw [normalGraph,hh,normalPlaneCoordinates_reconstruct hn x]

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
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_component_fderiv {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) (y v : Plane) :
    fderiv ℝ (fun z ↦ F z i) y v=(fderiv ℝ F y v) i := by
  have hh := (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).hasFDerivAt.comp y
    ((hF.differentiable (by simp) y).hasFDerivAt)
  have he := hh.fderiv
  change fderiv ℝ (fun z ↦ F z i) y=_ at he
  rw [he]
  rfl

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_decompose_sum (v : Plane) : v=∑ i : Fin 2,v i • EuclideanSpace.single i 1 := by
  rw [Fin.sum_univ_two]
  exact plane_decompose v

lemma plane_cover_clm_component (L : Plane →L[ℝ] Cover) (v : Plane) (i : Fin 3) :
    L v i=∑ j : Fin 2,v j*L (EuclideanSpace.single j 1) i := by
  change (EuclideanSpace.proj i : Cover →L[ℝ] ℝ) (L v)=_
  conv_lhs => rw [plane_decompose_sum v,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

lemma cover_plane_clm_component (L : Cover →L[ℝ] Plane) (v : Cover) (i : Fin 2) :
    L v i=∑ j : Fin 3,v j*L (EuclideanSpace.single j 1) i := by
  change (EuclideanSpace.proj i : Plane →L[ℝ] ℝ) (L v)=_
  conv_lhs => rw [cover_decompose v,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

lemma rectangular_trace (L : Plane →L[ℝ] Cover) (P : Cover →L[ℝ] Plane) :
    coverTrace (L.comp P)=planeTrace (P.comp L) := by
  simp only [coverTrace,planeTrace,ContinuousLinearMap.comp_apply]
  conv_lhs => enter [2,i]; rw [plane_cover_clm_component]
  conv_rhs => enter [2,i]; rw [cover_plane_clm_component]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcJacobian_inner_slope (p v : Plane) :
    ⟪p,cmcJacobian p v⟫=((cmcWeight p)^3)⁻¹*⟪p,v⟫ := by
  rw [cmcJacobian_apply,inner_sub_right,inner_smul_right,inner_smul_right,real_inner_self_eq_norm_sq]
  have hs := cmcWeight_sq p
  have hn := (cmcWeight_pos p).ne'
  field_simp [hn]
  nlinarith [congrArg (fun r : ℝ ↦ r*⟪p,v⟫) hs]

theorem graph_weingarten {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v : Plane) :
    fderiv ℝ (fun z ↦ graphSlopeNormal n (gradient g z)) y v=
      -fderiv ℝ (normalGraph n g) y (graphShapeOperator g y v) := by
  let p := gradient g y
  let L := fderiv ℝ (gradient g) y
  have hp := plane_gradient_contDiff hg
  have hq := (cmcWeight_hasFDerivAt p).comp y
    ((hp.differentiable (by simp) y).hasFDerivAt)
  have hi := (hasDerivAt_inv (cmcWeight_pos p).ne').comp_hasFDerivAt y hq
  have hN := (hasFDerivAt_const n y).sub
    ((normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt.comp y
      ((hp.differentiable (by simp) y).hasFDerivAt))
  have hd := (hi.smul hN).fderiv
  have he : (fun z ↦ graphSlopeNormal n (gradient g z))=
      (fun z ↦ (cmcWeight (gradient g z))⁻¹ • (n-normalPlaneEmbedding n (gradient g z))) :=
    funext fun z ↦ graphSlopeNormal_weight hn _
  rw [he]
  change fderiv ℝ (fun z ↦ (cmcWeight (gradient g z))⁻¹ •
    (n-normalPlaneEmbedding n (gradient g z))) y=_ at hd
  rw [hd,normalGraph_fderiv_apply hg]
  change _= -(normalPlaneEmbedding n (cmcJacobian p (L v))+⟪p,cmcJacobian p (L v)⟫ • n)
  rw [cmcJacobian_inner_slope,cmcJacobian_apply]
  have hE : normalPlaneEmbedding n=(normalPlaneLinearIsometry n).toContinuousLinearMap := rfl
  rw [hE]
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    neg_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul,
    Function.comp_def, Pi.sub_apply, p, L, map_sub, map_smul, smul_sub,
    zero_sub, smul_neg, neg_add_rev, ← inv_pow]
  module

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

lemma normalGraph_metric {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v w : Plane) :
    ⟪fderiv ℝ (normalGraph n g) y v,fderiv ℝ (normalGraph n g) y w⟫=
      ⟪v,w⟫+⟪gradient g y,v⟫*⟪gradient g y,w⟫ := by
  rw [normalGraph_fderiv_apply hg,normalGraph_fderiv_apply hg]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    normalPlaneEmbedding_inner hn,real_inner_self_eq_norm_sq,hn,one_pow,mul_zero,add_zero]
  have ho : ⟪normalPlaneEmbedding n v,n⟫=0 := by rw [real_inner_comm]; exact normalPlaneEmbedding_inner hn v
  have hi := (normalPlaneLinearIsometry n).inner_map_map v w
  change ⟪normalPlaneEmbedding n v,normalPlaneEmbedding n w⟫=⟪v,w⟫ at hi
  simp only [hi,ho,mul_zero,zero_add,mul_one]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_projection_differential {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) :
    (normalPlaneCoordinates n).comp (fderiv ℝ (normalGraph n g) y)=
      ContinuousLinearMap.id ℝ Plane := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply,normalGraph_fderiv_apply hg,map_add,map_smul,
    normalPlaneCoordinates_embedding,normalPlaneCoordinates_normal hn,smul_zero,add_zero]
  rfl

lemma graphUnitNormalExtension_fderiv (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Cover) :
    fderiv ℝ (graphUnitNormalExtension a n g) x=
      -((fderiv ℝ (normalGraph n g) (normalPlaneCoordinates n (x-a))).comp
        ((graphShapeOperator g (normalPlaneCoordinates n (x-a))).comp
          (normalPlaneCoordinates n))) := by
  have hN : Differentiable ℝ (fun y ↦ graphSlopeNormal n (gradient g y)) :=
    ((graphSlopeNormal_contDiff hn).comp (plane_gradient_contDiff hg)).differentiable (by simp)
  have hp := (normalPlaneCoordinates n).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const a)
  have hd := ((hN _).hasFDerivAt.comp x hp).fderiv
  change fderiv ℝ (graphUnitNormalExtension a n g) x=_ at hd
  rw [hd]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,neg_apply]
  exact graph_weingarten hn hg _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_eq_trace (F : Plane → Plane) (y : Plane) :
    planeDivergence F y=planeTrace (fderiv ℝ F y) := by
  simp only [planeDivergence,planeTrace,Fin.sum_univ_two]

lemma cmcFlux_gradient_fderiv {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) :
    fderiv ℝ (fun z ↦ cmcFlux (gradient g z)) y=graphShapeOperator g y := by
  exact ((cmcFlux_hasFDerivAt (gradient g y)).comp y
    (((plane_gradient_contDiff hg).differentiable (by simp) y).hasFDerivAt)).fderiv

theorem graphUnitNormalExtension_divergence (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Cover) :
    divergence (graphUnitNormalExtension a n g) x=
      -planeDivergence (fun z ↦ cmcFlux (gradient g z))
        (normalPlaneCoordinates n (x-a)) := by
  rw [divergence_eq_coverTrace,graphUnitNormalExtension_fderiv a hn hg]
  have hneg (L : Cover →L[ℝ] Cover) : coverTrace (-L)= -coverTrace L := by
    simp [coverTrace,Finset.sum_neg_distrib]
  rw [hneg,rectangular_trace,ContinuousLinearMap.comp_assoc,
    normalGraph_projection_differential hn hg,ContinuousLinearMap.comp_id,
    planeDivergence_eq_trace,cmcFlux_gradient_fderiv hg]

end CubicTorus

end
end

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainAcceleration
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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphInverseMetric_identity (p v w : Plane) :
    ⟪graphInverseMetric p v,w⟫+⟪p,graphInverseMetric p v⟫*⟪p,w⟫=⟪v,w⟫ := by
  simp only [graphInverseMetric,smul_apply,real_inner_smul_left,inner_smul_right]
  rw [cmcJacobian_inner_slope,cmcJacobian_apply]
  simp only [inner_sub_left,real_inner_smul_left]
  field_simp [(cmcWeight_pos p).ne']
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphInverseMetric_slope (p q : Plane) (c : ℝ) :
    graphInverseMetric p (q+c • p)=q+
      ((c-⟪p,q⟫)/(cmcWeight p)^2) • p := by
  rw [graphInverseMetric,smul_apply,cmcJacobian_apply]
  simp only [inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,smul_sub,smul_smul,
    mul_inv_cancel₀ (cmcWeight_pos p).ne',one_smul]
  have he : c-cmcWeight p*(((cmcWeight p)^3)⁻¹*(⟪p,q⟫+c*‖p‖^2))=
      (c-⟪p,q⟫)/(cmcWeight p)^2 := by
    field_simp [(cmcWeight_pos p).ne']
    nlinarith [congrArg (fun r : ℝ ↦ c*r) (cmcWeight_sq p)]
  rw [add_sub_assoc,← sub_smul,he]

lemma graph_metric_projection {n : Cover} (hn : ‖n‖=1) (p : Plane) (v : Cover) :
    normalPlaneEmbedding n (graphInverseMetric p (normalPlaneCoordinates n v+⟪n,v⟫ • p))+
      ⟪p,graphInverseMetric p (normalPlaneCoordinates n v+⟪n,v⟫ • p)⟫ • n=
        v-⟪graphSlopeNormal n p,v⟫ • graphSlopeNormal n p := by
  have he : normalPlaneEmbedding n=(normalPlaneLinearIsometry n).toContinuousLinearMap := rfl
  have hi : ⟪graphSlopeNormal n p,v⟫=(cmcWeight p)⁻¹*(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫) := by
    rw [graphSlopeNormal_weight hn,real_inner_smul_left,inner_sub_left,
      normalPlaneEmbedding_inner_coordinates hn]
  have hc : ⟪p,normalPlaneCoordinates n v⟫+
      ((⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2)*‖p‖^2=
        ⟪n,v⟫-(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2 := by
    field_simp [(cmcWeight_pos p).ne']
    nlinarith [congrArg (fun r : ℝ ↦ (⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)*r) (cmcWeight_sq p)]
  rw [graphInverseMetric_slope,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hc,
    he,map_add,map_smul,hi,graphSlopeNormal_weight hn]
  have hr := normalPlaneCoordinates_reconstruct hn v
  change (normalPlaneLinearIsometry n).toContinuousLinearMap (normalPlaneCoordinates n v)+⟪n,v⟫ • n=v at hr
  conv_rhs => lhs; rw [← hr]

  have hq : (cmcWeight p)⁻¹*(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)*(cmcWeight p)⁻¹=
      (⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2 := by
    field_simp
  simp only [smul_smul,smul_sub,hq,sub_smul,he]
  module

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_trace_invariance {n : Cover} (hn : ‖n‖=1)
    {D B : Cover →L[ℝ] Cover}
    (hD : ∀ v,⟪n,D v⟫=0) (hB : ∀ v,⟪n,B v⟫=0)
    (ht : ∀ v,⟪n,v⟫=0 → D v=B v) :
    coverTrace D=coverTrace B := by
  let w := D n-B n
  let R : Cover →L[ℝ] Cover := (innerSL ℝ n).smulRight w
  have hw : ⟪n,w⟫=0 := by rw [inner_sub_right,hD,hB,sub_self]
  have he : D=B+R := by
    apply ContinuousLinearMap.ext
    intro v
    have htv : ⟪n,v-⟪n,v⟫ • n⟫=0 := by
      rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,sub_self]
    change D v=B v+⟪n,v⟫ • (D n-B n)
    calc
      D v=D (v-⟪n,v⟫ • n)+⟪n,v⟫ • D n := by rw [map_sub,map_smul]; module
      _=B (v-⟪n,v⟫ • n)+⟪n,v⟫ • D n := by rw [ht _ htv]
      _=_ := by rw [map_sub,map_smul]; module
  rw [he,coverTrace_add,coverTrace_smulRight]
  rw [innerSL_apply_apply,hw,add_zero]

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

theorem graph_normal_extension_divergence (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hu : ∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    (hmatch : ∀ᶠ z in 𝓝 y,N (a+normalGraph n g z)=σ • graphSlopeNormal n (gradient g z)) :
    divergence N (a+normalGraph n g y)=
      -σ * planeDivergence (fun z ↦ cmcFlux (gradient g z)) y := by
  let x := a+normalGraph n g y
  let K : Cover → Cover := fun v ↦ σ • graphUnitNormalExtension a n g v
  have hK : ContDiff ℝ (⊤ : ℕ∞) K :=
    (graphUnitNormalExtension_contDiff a hn hg).const_smul σ
  have hKu (v : Cover) : ‖K v‖=1 := by
    rcases hσ with rfl|rfl
    · simpa only [K,one_smul] using graphUnitNormalExtension_unit a hn g v
    · simpa only [K,neg_one_smul,norm_neg] using graphUnitNormalExtension_unit a hn g v
  have hm : (fun z ↦ N (a+normalGraph n g z))=ᶠ[𝓝 y](fun z ↦ K (a+normalGraph n g z)) := by
    filter_upwards [hmatch] with z hz
    simpa only [K,graphUnitNormalExtension_graph a hn g g z] using hz
  have hNx : N x=K x := hm.eq_of_nhds
  have hdN := smooth_unit_normal_derivative (hN.differentiable (by simp) x) hu
  have hdK := smooth_unit_normal_derivative (hK.differentiable (by simp) x)
    (Filter.Eventually.of_forall hKu)
  have hnD (v : Cover) : ⟪N x,fderiv ℝ N x v⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,hdN,inner_zero_left]
  have hnB (v : Cover) : ⟪N x,fderiv ℝ K x v⟫=0 := by
    rw [hNx,← ContinuousLinearMap.adjoint_inner_left,hdK,inner_zero_left]
  have hΦ := (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).differentiableAt.hasFDerivAt.const_add a
  have hdmatch := hm.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (N ∘ fun z ↦ a+normalGraph n g z) y=
    fderiv ℝ (K ∘ fun z ↦ a+normalGraph n g z) y at hdmatch
  rw [((hN.differentiable (by simp) x).hasFDerivAt.comp y hΦ).fderiv,
    ((hK.differentiable (by simp) x).hasFDerivAt.comp y hΦ).fderiv] at hdmatch
  have ht (v : Cover) (hv : ⟪N x,v⟫=0) : fderiv ℝ N x v=fderiv ℝ K x v := by
    have hv' : ⟪graphSlopeNormal n (gradient g y),v⟫=0 := by
      rw [hNx] at hv
      change ⟪σ • graphUnitNormalExtension a n g x,v⟫=0 at hv
      rw [graphUnitNormalExtension_graph a hn g g y,real_inner_smul_left] at hv
      rcases hσ with rfl|rfl <;> simpa using hv
    let q := graphInverseMetric (gradient g y)
      (normalPlaneCoordinates n v+⟪n,v⟫ • gradient g y)
    have hvq : fderiv ℝ (normalGraph n g) y q=v := by
      rw [normalGraph_fderiv_apply hg]
      rw [graph_metric_projection hn,hv',zero_smul,sub_zero]
    have he := congrArg (fun L : Plane →L[ℝ] Cover ↦ L q) hdmatch
    simp only [ContinuousLinearMap.comp_apply] at he
    rw [← hvq]
    exact he
  rw [divergence_eq_coverTrace]
  change coverTrace (fderiv ℝ N x)=_
  rw [normal_trace_invariance (hu.self_of_nhds) hnD hnB ht]
  have he : coverTrace (fderiv ℝ K x)=σ * divergence (graphUnitNormalExtension a n g) x := by
    rw [divergence_eq_coverTrace]
    rcases hσ with rfl|rfl
    · simp only [K,one_smul,one_mul]
    · simp only [K,neg_one_smul]
      change coverTrace (fderiv ℝ (-graphUnitNormalExtension a n g) x)=_
      rw [fderiv_neg]
      simp only [coverTrace,neg_apply,PiLp.neg_apply,
        Finset.sum_neg_distrib,neg_one_mul]
  rw [he,graphUnitNormalExtension_divergence a hn hg]
  simp only [x,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_normal_geometry {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      ∀ᶠ y in 𝓝 (0 : Plane),N (cubeCenter+normalGraph n f y)=
        σ • graphSlopeNormal n (gradient f y) := by
  obtain ⟨normal,height,sign,hnormal,hheight,hzero,hsign,hmatch,_⟩ :=
    actual_centered_normal_graph_chart hV hE hmin hcenter hμ hN hp hae
  exact ⟨normal,height,sign,hnormal,hheight,hzero,hsign,hmatch.mono fun _ hpoint ↦ hpoint.1⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_geometry {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      ∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=σ • graphSlopeNormal n (gradient f y) := by
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
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm⟩ := actual_centered_normal_geometry hV hE' hmin' hc
    (isNormalMeasure_translation hE hμ a) hN' hp' hae'
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_⟩
  filter_upwards [hm] with y hy
  change N ((cubeCenter+normalGraph n f y)+a)=_ at hy
  have he : (cubeCenter+normalGraph n f y)+a=x+normalGraph n f y := by dsimp [a]; abel
  rwa [he] at hy

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

lemma graph_shape_metric_symmetric {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v w : Plane) :
    ⟪fderiv ℝ (normalGraph n g) y (graphShapeOperator g y v),fderiv ℝ (normalGraph n g) y w⟫=
      ⟪fderiv ℝ (normalGraph n g) y v,fderiv ℝ (normalGraph n g) y (graphShapeOperator g y w)⟫ := by
  have he (v w : Plane) :
      ⟪fderiv ℝ (normalGraph n g) y (graphShapeOperator g y v),fderiv ℝ (normalGraph n g) y w⟫=
        (cmcWeight (gradient g y))⁻¹*⟪fderiv ℝ (gradient g) y v,w⟫ := by
    rw [normalGraph_metric hn hg]
    have h := graphInverseMetric_identity (gradient g y) (fderiv ℝ (gradient g) y v) w
    simp only [graphInverseMetric,smul_apply,real_inner_smul_left,
      real_inner_smul_right] at h
    change ⟪cmcJacobian (gradient g y) (fderiv ℝ (gradient g) y v),w⟫+
      ⟪gradient g y,cmcJacobian (gradient g y) (fderiv ℝ (gradient g) y v)⟫*⟪gradient g y,w⟫=_
    field_simp [(cmcWeight_pos (gradient g y)).ne']
    nlinarith only [h]
  rw [he]
  conv_rhs => rw [real_inner_comm,he]
  rw [plane_hessian_symmetric hg,real_inner_comm v]

theorem graph_normal_tangent_symmetric (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hm : ∀ᶠ z in 𝓝 y,N (a+normalGraph n g z)=σ • graphSlopeNormal n (gradient g z))
    (v w : Cover) (hv : ⟪N (a+normalGraph n g y),v⟫=0)
    (hw : ⟪N (a+normalGraph n g y),w⟫=0) :
    ⟪fderiv ℝ N (a+normalGraph n g y) v,w⟫=
      ⟪v,fderiv ℝ N (a+normalGraph n g y) w⟫ := by
  have hnσ : σ≠0 := by rcases hσ with rfl|rfl <;> norm_num
  have hv' : ⟪graphSlopeNormal n (gradient g y),v⟫=0 := by
    rw [hm.self_of_nhds,real_inner_smul_left] at hv
    exact (mul_eq_zero.mp hv).resolve_left hnσ
  have hw' : ⟪graphSlopeNormal n (gradient g y),w⟫=0 := by
    rw [hm.self_of_nhds,real_inner_smul_left] at hw
    exact (mul_eq_zero.mp hw).resolve_left hnσ
  let q (v : Cover) := graphInverseMetric (gradient g y) (normalPlaneCoordinates n v+⟪n,v⟫ • gradient g y)
  have hj (v : Cover) (hv : ⟪graphSlopeNormal n (gradient g y),v⟫=0) :
      fderiv ℝ (normalGraph n g) y (q v)=v := by
    rw [normalGraph_fderiv_apply hg]
    dsimp [q]
    rw [graph_metric_projection hn,hv,zero_smul,sub_zero]
  have hΦ := (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).differentiableAt.hasFDerivAt.const_add a
  have hGN : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ graphSlopeNormal n (gradient g z)) :=
    (graphSlopeNormal_contDiff hn).comp (plane_gradient_contDiff hg)
  have hm' : (fun z ↦ N (a+normalGraph n g z))=ᶠ[𝓝 y]
      (fun z ↦ σ • graphSlopeNormal n (gradient g z)) := hm
  have hd := hm'.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (N ∘ fun z ↦ a+normalGraph n g z) y=
    fderiv ℝ (fun z ↦ σ • graphSlopeNormal n (gradient g z)) y at hd
  rw [((hN.differentiable (by simp) _).hasFDerivAt.comp y hΦ).fderiv,
    ] at hd
  change (fderiv ℝ N (a+normalGraph n g y)).comp (fderiv ℝ (normalGraph n g) y)=
    fderiv ℝ (σ • (fun z ↦ graphSlopeNormal n (gradient g z))) y at hd
  rw [fderiv_const_smul (hGN.differentiable (by simp) y)] at hd
  have hdv (r : Plane) : fderiv ℝ N (a+normalGraph n g y) (fderiv ℝ (normalGraph n g) y r)=
      σ • (-fderiv ℝ (normalGraph n g) y (graphShapeOperator g y r)) := by
    have h := congrArg (fun L : Plane →L[ℝ] Cover ↦ L r) hd
    simp only [ContinuousLinearMap.comp_apply,smul_apply] at h
    exact h.trans (congrArg (fun z : Cover ↦ σ • z) (graph_weingarten hn hg y r))
  calc
    _ = ⟪fderiv ℝ N (a+normalGraph n g y) (fderiv ℝ (normalGraph n g) y (q v)),
        fderiv ℝ (normalGraph n g) y (q w)⟫ := by rw [hj v hv',hj w hw']
    _ = ⟪fderiv ℝ (normalGraph n g) y (q v),
        fderiv ℝ N (a+normalGraph n g y) (fderiv ℝ (normalGraph n g) y (q w))⟫ := by
      rw [hdv,hdv]
      simp only [real_inner_smul_left,real_inner_smul_right,inner_neg_left,inner_neg_right]
      rw [graph_shape_metric_symmetric hn hg]
    _ = _ := by rw [hj v hv',hj w hw']

 theorem isMinimizerAt_shape_tangent_symmetric {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (v w : Cover) (hv : ⟪N x,v⟫=0) (hw : ⟪N x,w⟫=0) :
    ⟪fderiv ℝ N x v,w⟫=⟪v,fderiv ℝ N x w⟫ := by
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm⟩ := isMinimizerAt_normal_geometry hV hE hmin hμ hN hp hae x hx
  have hx0 : x+normalGraph n f 0=x := by
    have hz : normalPlaneEmbedding n 0=0 := norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
    simp [normalGraph,hf0,hz]
  simpa only [hx0] using graph_normal_tangent_symmetric x hn hf 0 hσ hN hm v w
    (by simpa only [hx0] using hv) (by simpa only [hx0] using hw)

end CubicTorus

end
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

lemma plane_smooth_local_inverse {P : Plane → Plane}
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hP0 : P 0=0)
    (hinj : Function.Injective (fderiv ℝ P 0)) :
    ∃ q : Plane → Plane,∃ R>0,q 0=0 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) q (Metric.ball 0 R) ∧
      (∀ y∈Metric.ball 0 R,P (q y)=y) ∧
      ∀ᶠ y in 𝓝 (0 : Plane),q (P y)=y := by
  have hbij : Function.Bijective (fderiv ℝ P 0) :=
    ⟨hinj,(LinearMap.injective_iff_surjective (f := (fderiv ℝ P 0).toLinearMap)).mp hinj⟩
  let e : Plane ≃L[ℝ] Plane := (LinearEquiv.ofBijective (fderiv ℝ P 0).toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasFDerivAt P (e : Plane →L[ℝ] Plane) 0 := (hP.differentiable (by simp) 0).hasFDerivAt
  let h := hP.contDiffAt.toOpenPartialHomeomorph P hd (by simp)
  have hsource : (0 : Plane)∈h.source := hP.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have htarget : (0 : Plane)∈h.target := by
    simpa only [hP0] using hP.contDiffAt.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have hcoe : (h : Plane → Plane)=P := rfl
  have hq0 : h.symm (0 : Plane)=0 := by
    simpa only [hcoe,hP0] using h.left_inv hsource
  have hqcont : ContinuousAt h.symm (0 : Plane) :=
    h.continuousOn_invFun.continuousAt (h.open_target.mem_nhds htarget)
  have hunit : ∀ᶠ y in 𝓝 (0 : Plane),IsUnit (fderiv ℝ P y) := by
    have hevent := (hP.continuous_fderiv (by simp)).continuousAt.eventually e.nhds
    filter_upwards [hevent] with point hpoint
    obtain ⟨equiv,hequiv⟩ := hpoint
    rw [← hequiv]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr equiv.bijective
  have hunitq : ∀ᶠ y in 𝓝 (0 : Plane),IsUnit (fderiv ℝ P (h.symm y)) := by
    have ht : Tendsto h.symm (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by simpa [hq0] using hqcont.tendsto
    exact ht.eventually hunit
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (h.open_target.mem_nhds htarget) hunitq)
  refine ⟨h.symm,R,hR,hq0,?_,?_,?_⟩
  · intro y hy
    have hb := hball hy
    have hbj := ContinuousLinearMap.isUnit_iff_bijective.mp hb.2
    let ey : Plane ≃L[ℝ] Plane :=
      (LinearEquiv.ofBijective (fderiv ℝ P (h.symm y)).toLinearMap hbj).toContinuousLinearEquiv
    have hdy : HasFDerivAt h (ey : Plane →L[ℝ] Plane) (h.symm y) :=
      (hP.differentiable (by simp) _).hasFDerivAt
    exact (h.contDiffAt_symm hb.1 hdy (show ContDiffAt ℝ (⊤ : ℕ∞) h (h.symm y) from hP.contDiffAt)).contDiffWithinAt
  · intro y hy
    exact h.right_inv (hball hy).1
  · filter_upwards [h.open_source.mem_nhds hsource] with y hy
    exact h.left_inv hy

lemma normalPlane_decomposition {n : Cover} (hn : ‖n‖=1) (v : Cover) :
    normalPlaneEmbedding n (normalPlaneCoordinates n v)+⟪n,v⟫ • n=v := by
  have hz : ⟪n,v-⟪n,v⟫ • n⟫=0 := by
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,sub_self]
  have hh := normalPlaneEmbedding_coordinates_of_inner_zero hn hz
  rw [map_sub,map_smul,normalPlaneCoordinates_normal hn,smul_zero,sub_zero] at hh
  rw [hh]
  abel

lemma normalGraph_derivative_tangent {m : Cover} (hm : ‖m‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v : Plane) :
    ⟪graphSlopeNormal m (gradient g y),fderiv ℝ (normalGraph m g) y v⟫=0 := by
  have he : ⟪normalPlaneEmbedding m (gradient g y),m⟫=0 := by
    rw [real_inner_comm,normalPlaneEmbedding_inner hm]
  have hp : ⟪normalPlaneEmbedding m (gradient g y),normalPlaneEmbedding m v⟫=⟪gradient g y,v⟫ :=
    (normalPlaneLinearIsometry m).inner_map_map _ _
  rw [normalGraph_fderiv_apply hg,graphSlopeNormal_weight hm]
  simp only [real_inner_smul_left,inner_sub_left,inner_add_right,real_inner_smul_right,
    normalPlaneEmbedding_inner hm,real_inner_self_eq_norm_sq,hm,one_pow,he,hp]
  ring

theorem normalGraph_regraph {m n : Cover} (hm : ‖m‖=1) (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : g 0=0)
    (ht : ∀ v : Plane,⟪n,fderiv ℝ (normalGraph m g) 0 v⟫=0) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),normalGraph m g
        (normalPlaneCoordinates m (normalGraph n f y))=normalGraph n f y) ∧
      ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n f
        (normalPlaneCoordinates n (normalGraph m g y))=normalGraph m g y := by
  let G := normalGraph m g
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry m).contDiff.add (hg.smul contDiff_const)
  have hG0 : G 0=0 := by
    change (normalPlaneLinearIsometry m) 0+g 0 • m=0
    simp [hg0]
  let P : Plane → Plane := fun y => normalPlaneCoordinates n (G y)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (normalPlaneCoordinates n).contDiff.comp hG
  have hP0 : P 0=0 := by simp [P,hG0]
  have hder : fderiv ℝ P 0=(normalPlaneCoordinates n).comp (fderiv ℝ G 0) :=
    ((normalPlaneCoordinates n).hasFDerivAt.comp 0 (hG.differentiable (by simp) 0).hasFDerivAt).fderiv
  have hinj : Function.Injective (fderiv ℝ P 0) := by
    intro v w he
    have he' : fderiv ℝ G 0 v=fderiv ℝ G 0 w := by
      rw [hder] at he
      have hv := normalPlaneEmbedding_coordinates_of_inner_zero hn (ht v)
      have hw := normalPlaneEmbedding_coordinates_of_inner_zero hn (ht w)
      rw [← hv,← hw]
      exact congrArg (normalPlaneEmbedding n) he
    have hh := congrArg (normalPlaneCoordinates m) he'
    simpa only [G,normalGraph_fderiv_apply hg,map_add,map_smul,normalPlaneCoordinates_embedding,
      normalPlaneCoordinates_normal hm,smul_zero,add_zero] using hh
  obtain ⟨q,R,hR,hq0,hq,hpq,hqp⟩ := plane_smooth_local_inverse hP hP0 hinj
  let f₀ : Plane → ℝ := fun y => ⟪n,G (q y)⟫
  have hf₀ : ContDiffOn ℝ (⊤ : ℕ∞) f₀ (Metric.ball 0 R) :=
    contDiffOn_const.inner ℝ (hG.comp_contDiffOn hq)
  obtain ⟨f,hf,hff⟩ := smooth_graph_extension hR hf₀
  have hf0 : f 0=0 := by
    rw [hff (by simpa using half_pos hR)]
    simp [f₀,hq0,hG0]
  have heq : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n f y=G (q y) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (half_pos hR)] with y hy
    have hyR : y∈Metric.ball (0 : Plane) R := (Metric.ball_subset_ball (by linarith)) hy
    have hh := normalPlane_decomposition hn (G (q y))
    have hpq' : normalPlaneCoordinates n (G (q y))=y := hpq y hyR
    rw [hpq'] at hh
    simpa only [normalGraph,hff hy,f₀] using hh
  refine ⟨f,hf,hf0,?_,?_⟩
  · filter_upwards [heq] with y hy
    rw [hy,normalPlaneCoordinates_graph hm]
  · have htP : Tendsto P (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by simpa [hP0] using hP.continuous.continuousAt.tendsto (x := 0)
    filter_upwards [htP.eventually heq,hqp] with y hy hqy
    change normalGraph n f (P y)=G y
    rw [hy,hqy]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma unit_normal_graph_unique {n ν : Cover} (hn : ‖n‖=1) (hν : ‖ν‖=1)
    {p : Plane} (hpos : 0<⟪n,ν⟫)
    (ht : ∀ v : Plane,⟪ν,normalPlaneEmbedding n v+⟪p,v⟫ • n⟫=0) :
    ν=graphSlopeNormal n p := by
  let d : ℝ := ⟪n,ν⟫
  have hproj : normalPlaneCoordinates n ν= -d • p := by
    apply ext_inner_left ℝ
    intro v
    have hh := ht v
    rw [inner_add_right,real_inner_smul_right,real_inner_comm n ν] at hh
    rw [normalPlaneCoordinates,ContinuousLinearMap.adjoint_inner_right,real_inner_smul_right,
      real_inner_comm p v]
    change ⟪normalPlaneEmbedding n v,ν⟫ = -d*⟪p,v⟫
    rw [real_inner_comm ν (normalPlaneEmbedding n v)]
    dsimp [d] at *
    linarith
  have he : ν=d • (n-normalPlaneEmbedding n p) := by
    have hh := normalPlane_decomposition hn ν
    rw [hproj] at hh
    change (normalPlaneLinearIsometry n) (-d • p)+d • n=ν at hh
    rw [map_smul] at hh
    rw [← hh]
    change -d • normalPlaneEmbedding n p+d • n=d • (n-normalPlaneEmbedding n p)
    module
  have ha : ‖n-normalPlaneEmbedding n p‖≠0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (graphSlopeVector_norm_ge hn p))
  have hd : d=‖n-normalPlaneEmbedding n p‖⁻¹ := by
    have hh := congrArg norm he
    rw [hν,norm_smul,Real.norm_eq_abs,abs_of_pos hpos] at hh
    rw [← one_div]
    apply (eq_div_iff ha).mpr
    simpa only [one_div] using hh.symm
  rw [he,hd,graphSlopeNormal]

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

theorem normalGraph_regraph_normal {m n x : Cover} (hm : ‖m‖=1) (hn : ‖n‖=1)
    {g f : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0=0) {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNx : N x=n)
    (hmatch : ∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph m g y)=σ • graphSlopeNormal m (gradient g y))
    (hgraph : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph m g
      (normalPlaneCoordinates m (normalGraph n f y))=normalGraph n f y) :
    ∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=graphSlopeNormal n (gradient f y) := by
  let P : Plane → Plane := fun y => normalPlaneCoordinates m (normalGraph n f y)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (normalPlaneCoordinates m).contDiff.comp
    ((normalPlaneLinearIsometry n).contDiff.add (hf.smul contDiff_const))
  have hP0 : P 0=0 := by simp only [P,normalGraph_zero hf0,map_zero]
  have htP : Tendsto P (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by
    simpa only [hP0] using hP.continuous.continuousAt.tendsto (x := 0)
  have hpos : ∀ᶠ y in 𝓝 (0 : Plane),0<⟪n,N (x+normalGraph n f y)⟫ := by
    have hc : Continuous (fun y => ⟪n,N (x+normalGraph n f y)⟫) :=
      continuous_const.inner (hN.continuous.comp
        (continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
          (hf.continuous.smul continuous_const))))
    have hz : 0<⟪n,N (x+normalGraph n f 0)⟫ := by
      rw [normalGraph_zero hf0,add_zero,hNx,real_inner_self_eq_norm_sq,hn,one_pow]
      norm_num
    exact hc.continuousAt.eventually (lt_mem_nhds hz)
  have hgraph' : ∀ᶠ y in 𝓝 (0 : Plane),∀ᶠ z in 𝓝 y,normalGraph m g (P z)=normalGraph n f z :=
    eventually_eventually_nhds.mpr hgraph
  filter_upwards [hgraph,hgraph',htP.eventually hmatch,hpos] with y hy he hm' hpos'
  have hmy : N (x+normalGraph n f y)=σ • graphSlopeNormal m (gradient g (P y)) := by
    rw [← hy]
    exact hm'
  refine unit_normal_graph_unique hn ?_ hpos' ?_
  · rw [hmy]
    rcases hσ with rfl|rfl <;> simp [graphSlopeNormal_unit hm]
  · intro v
    have he' : (fun z => normalGraph m g (P z)) =ᶠ[𝓝 y] normalGraph n f := he
    have hder := he'.fderiv_eq (𝕜 := ℝ)
    have hgD := (normalGraph_hasFDerivAt (n := m) (hg.differentiable (by simp) (P y)))
    have hPder := (hP.differentiable (by simp) y).hasFDerivAt
    change fderiv ℝ (normalGraph m g ∘ P) y=fderiv ℝ (normalGraph n f) y at hder
    rw [(hgD.comp y hPder).fderiv] at hder
    have hs := congrArg (fun L : Plane →L[ℝ] Cover => L v) hder
    have hs' : fderiv ℝ (normalGraph m g) (P y) (fderiv ℝ P y v)=
        fderiv ℝ (normalGraph n f) y v := by
      rw [hgD.fderiv]
      exact hs
    rw [← normalGraph_fderiv_apply hf,← hs',hmy,real_inner_smul_left,
      normalGraph_derivative_tangent hm hg,mul_zero]

lemma normalGraph_regraph_cover {m n : Cover} {g f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf0 : f 0=0) (hg0 : g 0=0)
    (hforward : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph m g
      (normalPlaneCoordinates m (normalGraph n f y))=normalGraph n f y)
    (hback : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n f
      (normalPlaneCoordinates n (normalGraph m g y))=normalGraph m g y) :
    ∀ᶠ v in 𝓝 (0 : Cover),
      (normalGraph m g (normalPlaneCoordinates m v)=v ↔
        normalGraph n f (normalPlaneCoordinates n v)=v) := by
  have htm : Tendsto (normalPlaneCoordinates m) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) :=
    (normalPlaneCoordinates m).continuous.tendsto' _ _ (map_zero _)
  have htn : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) :=
    (normalPlaneCoordinates n).continuous.tendsto' _ _ (map_zero _)
  have hgm : Tendsto (fun v : Cover => normalGraph m g (normalPlaneCoordinates m v))
      (𝓝 (0 : Cover)) (𝓝 (0 : Cover)) := (normalGraph_tendsto_zero hg hg0).comp htm
  have hfn : Tendsto (fun v : Cover => normalGraph n f (normalPlaneCoordinates n v))
      (𝓝 (0 : Cover)) (𝓝 (0 : Cover)) := (normalGraph_tendsto_zero hf hf0).comp htn
  filter_upwards [hgm.eventually (htm.eventually hback),
    hfn.eventually (htn.eventually hforward)] with v hb hf'
  constructor
  · intro hv
    simpa only [hv] using hb
  · intro hv
    simpa only [hv] using hf'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_tangent_CMC_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ k x,N (x+latticeVector k)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) {H : ℝ}
    (hgeom : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),
        N (x+normalGraph (N x) f y)=graphSlopeNormal (N x) (gradient f y) ∧
        quotientMap (x+normalGraph (N x) f y)∈frontier (openRepresentative E) ∧
        planeDivergence (fun z => cmcFlux (gradient f z)) y= -H) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph (N x) f (normalPlaneCoordinates (N x) v)=v := by
  obtain ⟨m,g,σ,hm,hg,hg0,hσ,hmatch,hcover⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hmin hμ hN hp hae x hx
  have hn : ‖N x‖=1 := (hgeom x hx).1.self_of_nhds
  have hcenter : N x=σ • graphSlopeNormal m (gradient g 0) := by
    simpa only [normalGraph_zero hg0,add_zero] using hmatch.self_of_nhds.1
  have ht (v : Plane) : ⟪N x,fderiv ℝ (normalGraph m g) 0 v⟫=0 := by
    rw [hcenter,real_inner_smul_left,normalGraph_derivative_tangent hm hg,mul_zero]
  obtain ⟨f,hf,hf0,hforward,hback⟩ := normalGraph_regraph hm hn hg hg0 ht
  have hnorm := normalGraph_regraph_normal hm hn hg hf hf0 hσ hN rfl
    (hmatch.mono fun y hy => hy.1) hforward
  have hnewcov := normalGraph_regraph_cover hf hg hf0 hg0 hforward hback
  have hP : Tendsto (fun y => normalPlaneCoordinates m (normalGraph (N x) f y))
      (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) :=
    ((normalPlaneCoordinates m).continuous.tendsto' _ _ (map_zero _)).comp
      (normalGraph_tendsto_zero hf hf0)
  have hnew : ∀ᶠ y in 𝓝 (0 : Plane),quotientMap (x+normalGraph (N x) f y)∈frontier (openRepresentative E) := by
    filter_upwards [hP.eventually hmatch,hforward] with y hy he
    have hh := hy.2
    rwa [he] at hh
  refine ⟨f,hf,hf0,?_,?_⟩
  · filter_upwards [hnorm,hnew,eventually_eventually_nhds.mpr hnorm] with y hy hyS hny
    refine ⟨hy,hyS,?_⟩
    have hd := graph_normal_extension_divergence x hn hf y (σ := 1) (Or.inl rfl) hN
      (hgeom _ hyS).1 (by simpa only [one_smul] using hny)
    rw [(hgeom _ hyS).2] at hd
    linarith
  · filter_upwards [hcover,hnewcov] with v hv hvc
    exact hv.trans hvc

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_MinimizerAxialCenter
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

lemma graph_tangent_fderiv_zero (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    {f : Cover → ℝ} (hf : DifferentiableAt ℝ f (a+normalGraph n g y))
    (hz : ∀ᶠ z in 𝓝 y,f (a+normalGraph n g z)=0)
    (v : Cover) (hv : ⟪graphSlopeNormal n (gradient g y),v⟫=0) :
    fderiv ℝ f (a+normalGraph n g y) v=0 := by
  let q := graphInverseMetric (gradient g y) (normalPlaneCoordinates n v+⟪n,v⟫ • gradient g y)
  have hj : fderiv ℝ (normalGraph n g) y q=v := by
    rw [normalGraph_fderiv_apply hg]
    dsimp [q]
    rw [graph_metric_projection hn,hv,zero_smul,sub_zero]
  have hΦ := (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).differentiableAt.hasFDerivAt.const_add a
  have he : (fun z => f (a+normalGraph n g z))=ᶠ[𝓝 y](fun _ => (0 : ℝ)) := hz
  have hd := he.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (f ∘ fun z => a+normalGraph n g z) y=_ at hd
  rw [(hf.hasFDerivAt.comp y hΦ).fderiv] at hd
  simp only [fderiv_const_apply] at hd
  have hh := congrArg (fun L : Plane →L[ℝ] ℝ => L q) hd
  simpa only [ContinuousLinearMap.comp_apply,zero_apply,hj] using hh

theorem isMinimizerAt_tangent_fderiv_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {f : Cover → ℝ} (hf : Differentiable ℝ f)
    (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → f x=0)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (v : Cover) (hv : ⟪N x,v⟫=0) : fderiv ℝ f x v=0 := by
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hchart,hcov,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmE hμ hN hp hae x hx
  have hx0 : x+normalGraph n g 0=x := by
    have hz : normalPlaneEmbedding n 0=0 := norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
    simp [normalGraph,hg0,hz]
  have hc : N x=σ • graphSlopeNormal n (gradient g 0) := by
    simpa only [hx0] using hchart.self_of_nhds.1
  have hv' : ⟪graphSlopeNormal n (gradient g 0),v⟫=0 := by
    rw [hc,real_inner_smul_left] at hv
    rcases hσ with rfl|rfl <;> simpa using hv
  have hz' : ∀ᶠ y in 𝓝 (0 : Plane),f (x+normalGraph n g y)=0 :=
    hchart.mono fun y hy => hz _ hy.2
  simpa only [hx0] using graph_tangent_fderiv_zero x hn hg 0 (hf _) hz' v hv'

theorem isMinimizerAt_axial_shape_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (v : Cover) (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) : fderiv ℝ N x v=0 := by
  have hv : ⟪N x,v⟫=0 := by rw [real_inner_comm]; exact hz x hx
  have hn : ‖N x‖=1 := hu.self_of_nhds
  have hNt (w : Cover) : ⟪N x,fderiv ℝ N x w⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      smooth_unit_normal_derivative (hN.differentiable (by simp) x) hu,inner_zero_left]
  have hscalar : Differentiable ℝ (fun y => ⟪v,N y⟫) :=
    (innerSL ℝ v).differentiable.comp (hN.differentiable (by simp))
  have hd (w : Cover) (hw : ⟪N x,w⟫=0) : ⟪fderiv ℝ N x v,w⟫=0 := by
    rw [isMinimizerAt_shape_tangent_symmetric hV hE hmE hμ hN hp hae x hx v w hv hw]
    have hh := isMinimizerAt_tangent_fderiv_zero hV hE hmE hμ hN hp hae hscalar hz x hx w hw
    have he := (innerSL ℝ v).hasFDerivAt.comp x (hN.differentiable (by simp) x).hasFDerivAt
    rw [show (fun y => ⟪v,N y⟫)=(innerSL ℝ v) ∘ N from rfl,he.fderiv] at hh
    exact hh
  have hh := hd (fderiv ℝ N x v) (hNt v)
  exact inner_self_eq_zero.mp hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_symmetric_null_shape (L : Plane →L[ℝ] Plane)
    (hs : ∀ v w,⟪L v,w⟫=⟪v,L w⟫) {p : Plane} (hp : ‖p‖=1)
    (hz : L p=0) (w : Plane) : L w=planeTrace L • (w-⟪p,w⟫ • p) := by
  let a := L (EuclideanSpace.single 0 1) 0
  let b := L (EuclideanSpace.single 1 1) 0
  let d := L (EuclideanSpace.single 1 1) 1
  have hb : L (EuclideanSpace.single 0 1) 1=b := by
    have h := hs (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,mul_one,one_mul] using h
  have hc (q : Plane) : L q 0=a*q 0+b*q 1 ∧ L q 1=b*q 0+d*q 1 := by
    constructor
    · conv_lhs => rw [plane_decompose q]
      simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      dsimp [a,b]; ring
    · conv_lhs => rw [plane_decompose q]
      simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,hb]
      dsimp [d]; ring
  have h0 : a*p 0+b*p 1=0 := by rw [← (hc p).1,hz]; rfl
  have h1 : b*p 0+d*p 1=0 := by rw [← (hc p).2,hz]; rfl
  have hn : (p 0)^2+(p 1)^2=1 := by
    have hh := real_inner_self_eq_norm_sq p
    rw [plane_inner_components,hp,one_pow] at hh
    nlinarith only [hh]
  have htr : planeTrace L=a+d := by simp only [planeTrace,Fin.sum_univ_two]; rfl
  have ha : a=(a+d)*(p 1)^2 := by
    linear_combination p 0*h0-p 1*h1-a*hn
  have hd : d=(a+d)*(p 0)^2 := by
    linear_combination p 1*h1-p 0*h0-d*hn
  have hb' : b= -(a+d)*p 0*p 1 := by
    linear_combination p 1*h0+p 0*h1-b*hn
  ext i
  fin_cases i
  · change L w 0=planeTrace L*(w 0-⟪p,w⟫*p 0)
    rw [plane_inner_components,htr,(hc w).1]
    linear_combination w 0*ha+w 1*hb'+(a+d)*w 0*hn
  · change L w 1=planeTrace L*(w 1-⟪p,w⟫*p 1)
    rw [plane_inner_components,htr,(hc w).2]
    linear_combination w 0*hb'+w 1*hd+(a+d)*w 1*hn

lemma normal_plane_trace {n : Cover} (hn : ‖n‖=1)
    (D : Cover →L[ℝ] Cover) (ht : ∀ w,⟪n,D w⟫=0) :
    planeTrace ((normalPlaneCoordinates n).comp (D.comp
      (normalPlaneLinearIsometry n).toContinuousLinearMap))=coverTrace D := by
  rw [← rectangular_trace]
  symm
  apply normal_trace_invariance hn ht
  · intro w
    exact ht _
  · intro w hw
    simp only [ContinuousLinearMap.comp_apply]
    change D w=D (normalPlaneEmbedding n (normalPlaneCoordinates n w))
    rw [normalPlaneEmbedding_coordinates_of_inner_zero hn hw]

lemma normal_axial_shape {n v : Cover} (hn : ‖n‖=1) (hv : ‖v‖=1)
    (hvn : ⟪n,v⟫=0) (D : Cover →L[ℝ] Cover)
    (ht : ∀ w,⟪n,D w⟫=0)
    (hs : ∀ z w,⟪n,z⟫=0 → ⟪n,w⟫=0 → ⟪D z,w⟫=⟪z,D w⟫)
    (hz : D v=0) (w : Cover) (hw : ⟪n,w⟫=0) :
    D w=coverTrace D • (w-⟪v,w⟫ • v) := by
  let P := normalPlaneCoordinates n
  let T := (normalPlaneLinearIsometry n).toContinuousLinearMap
  let L := P.comp (D.comp T)
  have hT (u : Plane) : T u=normalPlaneEmbedding n u := rfl
  have he (u : Cover) (hu : ⟪n,u⟫=0) : T (P u)=u :=
    normalPlaneEmbedding_coordinates_of_inner_zero hn hu
  have hPs (u : Plane) (z : Cover) : ⟪P z,u⟫=⟪z,T u⟫ := by
    rw [real_inner_comm,← normalPlaneEmbedding_inner_coordinates hn,real_inner_comm]
    rfl
  have hLs (u z : Plane) : ⟪L u,z⟫=⟪u,L z⟫ := by
    change ⟪P (D (T u)),z⟫=⟪u,P (D (T z))⟫
    rw [hPs,← normalPlaneEmbedding_inner_coordinates hn]
    exact hs _ _ (normalPlaneEmbedding_inner hn _) (normalPlaneEmbedding_inner hn _)
  have hp : ‖P v‖=1 := (normalPlaneCoordinates_norm_of_inner_zero hn hvn).trans hv
  have hz' : L (P v)=0 := by change P (D (T (P v)))=0; rw [he v hvn,hz,map_zero]
  have hh := plane_symmetric_null_shape L hLs hp hz' (P w)
  have htr : planeTrace L=coverTrace D := normal_plane_trace hn D ht
  have hi : ⟪P v,P w⟫=⟪v,w⟫ := by rw [hPs,he w hw]
  have hhd := congrArg T hh
  simp only [map_smul,map_sub,htr,hi] at hhd
  change T (P (D (T (P w))))=coverTrace D • (T (P w)-⟪v,w⟫ • T (P v)) at hhd
  simpa only [he w hw,he v hvn,he (D w) (ht w)] using hhd

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialCenter_fderiv {N : Cover → Cover} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (v : Cover) (H : ℝ) (w : Cover) :
    fderiv ℝ (axialCenter v H N) x w=w-⟪v,w⟫ • v-H⁻¹ • fderiv ℝ N x w := by
  have hh := ((hasFDerivAt_id x).sub ((innerSL ℝ v).hasFDerivAt.smul_const v)).sub
    (hN.hasFDerivAt.const_smul H⁻¹)
  change HasFDerivAt (axialCenter v H N) _ x at hh
  rw [hh.fderiv]
  rfl

theorem isMinimizerAt_axial_shape {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {H : ℝ} (hgeom : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (w : Cover) (hw : ⟪N x,w⟫=0) :
    fderiv ℝ N x w=H • (w-⟪v,w⟫ • v) := by
  have hn := (hgeom x hx).1.self_of_nhds
  have htan (z : Cover) : ⟪N x,fderiv ℝ N x z⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      smooth_unit_normal_derivative (hN.differentiable (by simp) x) (hgeom x hx).1,inner_zero_left]
  have he := normal_axial_shape hn hv (by rw [real_inner_comm]; exact hz x hx)
    (fderiv ℝ N x) htan
    (isMinimizerAt_shape_tangent_symmetric hV hE hmE hμ hN hp hae x hx)
    (isMinimizerAt_axial_shape_zero hV hE hmE hμ hN hp hae v hz x hx (hgeom x hx).1) w hw
  rw [← divergence_eq_coverTrace,(hgeom x hx).2] at he
  exact he

theorem isMinimizerAt_axialCenter_local {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {H : ℝ} (hH : H≠0)
    (hgeom : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (a : Cover) (ha : quotientMap a∈frontier (openRepresentative E)) :
    ∀ᶠ z in 𝓝 a,quotientMap z∈frontier (openRepresentative E) →
      axialCenter v H N z=axialCenter v H N a := by
  obtain ⟨g,hg,hg0,hchart,hcov⟩ :=
    isMinimizerAt_tangent_CMC_chart hV hE hmE hμ hN hp hae hgeom a ha
  let X : Plane → Cover := fun y => a+normalGraph (N a) g y
  have hX : Differentiable ℝ X := fun y =>
    ((normalGraph_hasFDerivAt (n := N a) (hg.differentiable (by simp) y)).const_add a).differentiableAt
  have hC : Differentiable ℝ (axialCenter v H N) := by
    intro x
    exact (((hasFDerivAt_id x).sub ((innerSL ℝ v).hasFDerivAt.smul_const v)).sub
      ((hN.differentiable (by simp) x).hasFDerivAt.const_smul H⁻¹)).differentiableAt
  have hF := hC.comp hX
  obtain ⟨r,hr,hrc⟩ := Metric.eventually_nhds_iff.mp hchart
  have hd : ∀ y∈Metric.ball (0 : Plane) r,fderiv ℝ (axialCenter v H N ∘ X) y=0 := by
    intro y hy
    rw [fderiv_comp y (hC _) (hX y)]
    apply ContinuousLinearMap.ext
    intro w
    simp only [ContinuousLinearMap.comp_apply,zero_apply]
    rw [axialCenter_fderiv (hN.differentiable (by simp) _)]
    have ht : ⟪N (X y),fderiv ℝ X y w⟫=0 := by
      change ⟪N (a+normalGraph (N a) g y),fderiv ℝ (fun z => a+normalGraph (N a) g z) y w⟫=0
      rw [(hrc hy).1,fderiv_const_add]
      exact normalGraph_derivative_tangent ((hgeom a ha).1.self_of_nhds) hg y w
    rw [isMinimizerAt_axial_shape hV hE hmE hμ hN hp hae hv hz hgeom (X y) (hrc hy).2.1 _ ht,
      smul_smul,inv_mul_cancel₀ hH,one_smul,sub_self]
  have he (y : Plane) (hy : y∈Metric.ball 0 r) : axialCenter v H N (X y)=axialCenter v H N a := by
    have hh := (convex_ball (0 : Plane) r).is_const_of_fderivWithin_eq_zero hF.differentiableOn
      (fun z hz' => by rw [fderivWithin_of_isOpen Metric.isOpen_ball hz']; exact hd z hz')
      hy (Metric.mem_ball_self hr)
    simpa only [Function.comp_apply,X,normalGraph_zero hg0,add_zero] using hh
  have hsub : Tendsto (fun z : Cover => z-a) (𝓝 a) (𝓝 (0 : Cover)) := by
    have hc : Continuous (fun z : Cover => z-a) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto a
  have hP : Tendsto (fun z : Cover => normalPlaneCoordinates (N a) (z-a)) (𝓝 a) (𝓝 (0 : Plane)) := by
    exact ((normalPlaneCoordinates (N a)).continuous.tendsto' _ _ (map_zero _)).comp hsub
  filter_upwards [hsub.eventually hcov,hP.eventually (Metric.ball_mem_nhds (0 : Plane) hr)] with z hz hy hzb
  have hgx := hz.mp (by simpa only [add_sub_cancel] using hzb)
  have hh := he _ hy
  simpa only [X,hgx,add_sub_cancel] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialProjection_tangent {v x : Cover} (hx : ⟪v,x⟫=0) : axialProjection v x=x := by simp [hx]

lemma axialProjection_inner {v n x : Cover} (hn : ⟪v,n⟫=0) :
    ⟪n,axialProjection v x⟫=⟪n,x⟫ := by
  simp only [axialProjection_apply,inner_sub_right,real_inner_smul_right,
    real_inner_comm v n,hn,mul_zero,sub_zero]

lemma axialProjection_inner_zero {v : Cover} (hv : ‖v‖=1) (x : Cover) :
    ⟪v,axialProjection v x⟫=0 := by
  rw [axialProjection_apply,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hv,one_pow,mul_one,sub_self]

lemma axialProjection_idempotent {v : Cover} (hv : ‖v‖=1) (x : Cover) :
    axialProjection v (axialProjection v x)=axialProjection v x :=
  axialProjection_tangent (axialProjection_inner_zero hv x)

lemma normal_squared_cylinder_difference {n v : Cover} (hn : ‖n‖=1) (hvn : ⟪v,n⟫=0)
    (g : Plane → ℝ) (c z : Cover) :
    ‖axialProjection v (z-c)‖^2-‖axialProjection v (normalGraph n g (normalPlaneCoordinates n z)-c)‖^2=
      (⟪n,z⟫-g (normalPlaneCoordinates n z))*(⟪n,z⟫+g (normalPlaneCoordinates n z)-2*⟪n,c⟫) := by
  let w := normalGraph n g (normalPlaneCoordinates n z)
  let k := ⟪n,z⟫-g (normalPlaneCoordinates n z)
  have he : z-c=(w-c)+k • n := by
    calc
      z-c=(normalPlaneEmbedding n (normalPlaneCoordinates n z)+⟪n,z⟫ • n)-c :=
        congrArg (fun q : Cover => q-c) (normalPlaneCoordinates_reconstruct hn z).symm
      _=(w-c)+k • n := by dsimp [w,k,normalGraph]; rw [sub_smul]; module
  have hi : ⟪n,axialProjection v (w-c)⟫=g (normalPlaneCoordinates n z)-⟪n,c⟫ := by
    rw [axialProjection_inner hvn,inner_sub_right]
    dsimp [w,normalGraph]
    rw [inner_add_right,normalPlaneEmbedding_inner hn,real_inner_smul_right,
      real_inner_self_eq_norm_sq,hn,one_pow,mul_one,zero_add]
  rw [he,map_add,map_smul,axialProjection_tangent hvn,norm_add_sq_real]
  rw [real_inner_smul_right,real_inner_comm n (axialProjection v (w-c)),hi,
    norm_smul,Real.norm_eq_abs,hn,mul_one,sq_abs]
  dsimp [k,w]
  ring

lemma local_graph_cylinder_iff {n v : Cover} (hn : ‖n‖=1) (hvn : ⟪v,n⟫=0)
    {g : Plane → ℝ} (hg : Continuous g) (hg0 : g 0=0) {c : Cover} {R : ℝ}
    (hc : ⟪n,c⟫≠0)
    (hs : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n g y∈euclideanCylinder v c R) :
    ∀ᶠ z in 𝓝 (0 : Cover),normalGraph n g (normalPlaneCoordinates n z)=z ↔
      z∈euclideanCylinder v c R := by
  have hct : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates n).continuous.tendsto (0 : Cover)
  have hnon : ∀ᶠ z in 𝓝 (0 : Cover),⟪n,z⟫+g (normalPlaneCoordinates n z)-2*⟪n,c⟫≠0 := by
    have ht : ContinuousAt (fun z : Cover => ⟪n,z⟫+g (normalPlaneCoordinates n z)-2*⟪n,c⟫) 0 := by fun_prop
    apply ht.eventually_ne
    simp only [inner_zero_right,map_zero,hg0,zero_add,zero_sub,neg_ne_zero,mul_ne_zero_iff]
    exact ⟨by norm_num,hc⟩
  filter_upwards [hct.eventually hs,hnon] with z hz hnz
  constructor
  · intro he
    rwa [← he]
  · intro he
    have hz0 : ‖axialProjection v (z-c)‖^2-
        ‖axialProjection v (normalGraph n g (normalPlaneCoordinates n z)-c)‖^2=0 := by
      change ‖axialProjection v (z-c)‖=R at he
      change ‖axialProjection v (normalGraph n g (normalPlaneCoordinates n z)-c)‖=R at hz
      rw [he,hz,sub_self]
    rw [normal_squared_cylinder_difference hn hvn,mul_eq_zero] at hz0
    exact (normalGraph_coordinates_eq_iff hn g z).mpr
      ((sub_eq_zero.mp (hz0.resolve_right hnz)).symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cylinder_center_translation {v : Cover} (hv : ‖v‖=1) {N : Cover → Cover}
    (H : ℝ) {a : Cover} (ha : ⟪v,N a⟫=0) (z : Cover) (R : ℝ) :
    a+z∈euclideanCylinder v (axialCenter v H N a) R ↔
      z∈euclideanCylinder v (-H⁻¹ • N a) R := by
  have he : axialProjection v (a+z-axialCenter v H N a)=
      axialProjection v (z-(-H⁻¹ • N a)) := by
    change axialProjection v (a+z-(axialProjection v a-H⁻¹ • N a))=_
    rw [map_sub,map_add,map_sub,map_smul,axialProjection_idempotent hv,
      axialProjection_tangent ha,map_sub,map_smul,axialProjection_tangent ha]
    module
  exact iff_of_eq (congrArg (fun w : Cover => ‖w‖=R) he)

theorem isMinimizerAt_axial_local_cylinder_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {H : ℝ} (hH : H≠0)
    (hgeom : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (a : Cover) (ha : quotientMap a∈frontier (openRepresentative E)) :
    ∀ᶠ z in 𝓝 a,
      (quotientMap z∈frontier (openRepresentative E) ↔
        z∈euclideanCylinder v (axialCenter v H N a) |H⁻¹|) ∧
      (quotientMap z∈frontier (openRepresentative E) →
        axialCenter v H N z=axialCenter v H N a) := by
  obtain ⟨g,hg,hg0,hchart,hcov⟩ :=
    isMinimizerAt_tangent_CMC_chart hV hE hmE hμ hN hp hae hgeom a ha
  have hn : ‖N a‖=1 := (hgeom a ha).1.self_of_nhds
  have hza := hz a ha
  have hcenter := isMinimizerAt_axialCenter_local hV hE hmE hμ hN hp hae hv hz hH hgeom a ha
  have hX : Tendsto (fun y => a+normalGraph (N a) g y) (𝓝 (0 : Plane)) (𝓝 a) := by
    have ht := (normalGraph_tendsto_zero (n := N a) hg hg0).const_add a
    simpa only [add_zero] using ht
  have hs : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph (N a) g y∈euclideanCylinder v (-H⁻¹ • N a) |H⁻¹| := by
    filter_upwards [hchart,hX.eventually hcenter] with y hy hyc
    have he := hyc hy.2.1
    have hproj : axialProjection v (normalGraph (N a) g y-(-H⁻¹ • N a))=
        H⁻¹ • N (a+normalGraph (N a) g y) := by
      apply sub_eq_zero.mp
      calc
        _=axialCenter v H N (a+normalGraph (N a) g y)-axialCenter v H N a := by
          change axialProjection v (_-_) - _ =
            (axialProjection v (a+normalGraph (N a) g y)-H⁻¹ • N (a+normalGraph (N a) g y))-
              (axialProjection v a-H⁻¹ • N a)
          rw [map_sub,map_smul,axialProjection_tangent hza,map_add]
          module
        _=0 := sub_eq_zero.mpr he
    change ‖axialProjection v (_-_)‖=|H⁻¹|
    rw [hproj,norm_smul,Real.norm_eq_abs,(hgeom _ hy.2.1).1.self_of_nhds,mul_one]
  have hcn : ⟪N a,-H⁻¹ • N a⟫≠0 := by
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
    exact neg_ne_zero.mpr (inv_ne_zero hH)
  have hlocal := local_graph_cylinder_iff hn hza hg.continuous hg0 hcn hs
  have ht : Tendsto (fun z : Cover => z-a) (𝓝 a) (𝓝 (0 : Cover)) := by
    have hc : Continuous (fun z : Cover => z-a) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto a
  filter_upwards [ht.eventually hcov,ht.eventually hlocal,hcenter] with z hcovz hlocalz hcz
  refine ⟨?_,hcz⟩
  have hh := hcovz.trans hlocalz
  simpa only [add_sub_cancel] using hh.trans
    (cylinder_center_translation hv H hza (z-a) |H⁻¹|).symm

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_axial_local_cylinder_oai := @OAI.CubicTorus.isMinimizerAt_axial_local_cylinder_oai
