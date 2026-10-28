-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:06:49.326572+00:00
-- url     : https://prove2.me/submissions/cd3ab2e0-8f8c-41bf-b4e5-1b0518625467

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Definitions.Def_OAIQ079A001
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_lower_density

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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

lemma quotientMap_measurePreserving :
    MeasurePreserving quotientMap (volume.restrict fundamentalCube) torusVolume :=
  ⟨measurable_quotientMap, rfl⟩

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

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 1 / 2) :
    Metric.ball cubeCenter r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - cubeCenter‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans_lt hx'
  change ‖x i - (1 / 2 : ℝ)‖ < r at hb
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

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

lemma shortestLift_quotientMap {x : Cover} (hx : ‖x‖ < 1 / 2) :
    shortestLift (quotientMap x) = x := by
  have hc : x + cubeCenter ∈ fundamentalCube := coverBall_subset_cube (by rfl)
    (by simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hx)
  rw [shortestLift, ← quotientMap_add, representative_quotientMap_of_mem hc, add_sub_cancel_right]

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
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma ediam_metricBall_le (a : Torus) {r : ℝ} (_hr : 0 ≤ r) :
    ediam (Metric.ball a r) ≤ ENNReal.ofReal (2 * r) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hh := dist_triangle_right x y a
  exact hh.trans (by linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hy])

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma hausdorff_two_le_open_of_lower_density (σ : FiniteMeasure Torus) (S U : Set Torus)
    (hU : IsOpen U) (hSU : S ⊆ U) {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ S, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r)) :
    Measure.hausdorffMeasure 2 S ≤ ENNReal.ofReal (64 / c) * (σ : Measure Torus) U := by
  classical
  let r : ℕ → ℝ := fun n ↦ R / ((n : ℝ) + 1)
  have hr (n) : 0 < r n := by dsimp [r]; positivity
  have hrR (n) : r n ≤ R := by
    dsimp [r]
    exact div_le_self hR.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := R)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, mul_one_div] using hh
  have heps : ∀ a ∈ S, ∃ e : ℝ, 0 < e ∧ Metric.ball a e ⊆ U := by
    intro a ha
    exact Metric.isOpen_iff.mp hU a (hSU ha)
  choose e he heU using heps
  let rad (n : ℕ) (a : Torus) : ℝ := if ha : a ∈ S then min (r n) (e a ha) else r n
  have hrad (n : ℕ) (a : Torus) (ha : a ∈ S) : 0 < rad n a := by
    simp only [rad, dite_eq_left ha]
    exact lt_min (hr n) (he a ha)
  have hradle (n : ℕ) (a : Torus) : rad n a ≤ r n := by
    by_cases ha : a ∈ S
    · simp only [rad, dite_eq_left ha]; exact min_le_left _ _
    · simp only [rad, dite_eq_right ha]; exact le_rfl
  have hradU (n : ℕ) (a : Torus) (ha : a ∈ S) : Metric.ball a (rad n a) ⊆ U := by
    apply (Metric.ball_subset_ball ?_).trans (heU a ha)
    simp only [rad, dite_eq_left ha]
    exact min_le_right _ _
  have hex (n : ℕ) := Vitali.exists_disjoint_subfamily_covering_enlargement_ball S id
    (rad n) (r n) (fun a _ ↦ hradle n a) 4 (by norm_num)
  choose u hu hdis hcov using hex
  have hcount (n) : (u n).Countable :=
    (hdis n).countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
      (fun a ha ↦ ⟨a, Metric.mem_ball_self (hrad n a (hu n ha))⟩)
  let : ∀ n, Countable (u n) := fun n ↦ (hcount n).to_subtype
  let t (n : ℕ) (a : u n) : Set Torus := Metric.ball (a : Torus) (4 * rad n a)
  have hdiam' (n : ℕ) (a : u n) : ediam (t n a) ≤ ENNReal.ofReal (8 * rad n a) := by
    simpa only [t, show (2 : ℝ) * (4 * rad n a) = 8 * rad n a by ring] using
      ediam_metricBall_le (a : Torus) (show 0 ≤ 4 * rad n a from by
        have hh := hrad n a (hu n a.property); positivity)
  have hdiam (n : ℕ) (a : u n) : ediam (t n a) ≤ ENNReal.ofReal (8 * r n) :=
    (hdiam' n a).trans (ENNReal.ofReal_le_ofReal (by nlinarith [hradle n a]))
  have hcover (n) : S ⊆ ⋃ a : u n, t n a := by
    intro a ha
    obtain ⟨b, hb, hsub⟩ := hcov n a ha
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hsub (Metric.mem_ball_self (hrad n a ha))⟩
  have hstep (n : ℕ) (a : u n) : ediam (t n a) ^ (2 : ℝ) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) := by
    have hrpos := hrad n a (hu n a.property)
    have hlow := hl a (hu n a.property) (rad n a) hrpos ((hradle n a).trans (hrR n))
    have hb : ENNReal.ofReal (c * rad n a ^ 2) ≤
        (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hlow
    calc
      _ = ediam (t n a) ^ (2 : ℕ) := ENNReal.rpow_two _
      _ ≤ (ENNReal.ofReal (8 * rad n a)) ^ (2 : ℕ) := pow_le_pow_left' (hdiam' n a) _
      _ = ENNReal.ofReal (64 / c) * ENNReal.ofReal (c * rad n a ^ 2) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
      _ ≤ _ := mul_le_mul_right hb _
  have hsum (n : ℕ) : (∑' a : u n, ediam (t n a) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) U := by
    calc
      _ ≤ ∑' a : u n, ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) := ENNReal.tsum_le_tsum (hstep n)
      _ = ENNReal.ofReal (64 / c) *
          (∑' a : u n, (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a))) := by
        rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (⋃ a ∈ u n, Metric.ball a (rad n a)) := by
        congr 1
        exact (measure_biUnion (hcount n) (hdis n)
          (fun _ _ ↦ Metric.isOpen_ball.measurableSet)).symm
      _ ≤ _ := mul_le_mul_right (measure_mono (by
        intro x hx
        obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
        exact hradU n a (hu n ha) hx)) _
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (8 * r n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hr0.const_mul 8)
  have hh := Measure.hausdorffMeasure_le_liminf_tsum 2 S
    (fun n ↦ ENNReal.ofReal (8 * r n)) hlim t
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  exact hh.trans (liminf_le_of_frequently_le' (Eventually.of_forall hsum).frequently)

lemma hausdorff_two_le_measure_of_lower_density (σ : FiniteMeasure Torus) (S : Set Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ S, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r)) :
    Measure.hausdorffMeasure 2 S ≤ ENNReal.ofReal (64 / c) * (σ : Measure Torus) S := by
  have h0 : ENNReal.ofReal (64 / c) ≠ 0 := by positivity
  rw [S.measure_eq_iInf_isOpen (σ : Measure Torus),
    ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro U
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro hSU
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  exact le_iInf fun hU ↦ hausdorff_two_le_open_of_lower_density σ S U hU hSU hR hc hl

lemma hausdorff_two_null_of_lower_density (σ : FiniteMeasure Torus) (B : Set Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    {S : Set Torus} (hSB : S ⊆ B) (hS : (σ : Measure Torus) S = 0) :
    Measure.hausdorffMeasure 2 S = 0 := by
  have hh := hausdorff_two_le_measure_of_lower_density σ S hR hc
    (fun a ha ↦ hl a (hSB ha))
  rw [hS, mul_zero] at hh
  exact le_zero_iff.mp hh

theorem isMinimizerAt_boundary_area_absolutelyContinuous {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (Measure.hausdorffMeasure 2).restrict (frontier (openRepresentative E)) ≪
      (spatialNormalMeasure μ : Measure Torus) := by
  obtain ⟨R, c, hR, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  intro S hS
  rw [Measure.restrict_apply₀' isClosed_frontier.measurableSet.nullMeasurableSet]
  apply hausdorff_two_null_of_lower_density (spatialNormalMeasure μ)
    (volumeSupport E ∩ volumeSupport Eᶜ) hR hc (hl μ hμ)
  · rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact inter_subset_right
  · exact measure_mono_null inter_subset_left hS

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CirclePeriodize
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

lemma continuous_periodic_lift {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : Continuous f) : Continuous hp.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact hf

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_OctantVertex
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

lemma smooth_periodic_centered_primitive {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    ∃ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ ∧ Function.Periodic ψ 1 ∧
      ∀ t,deriv ψ t=f t-∫ u in (0 : ℝ)..1,f u := by
  let c : ℝ := ∫ u in (0 : ℝ)..1,f u
  let g : ℝ → ℝ := fun t ↦ f t-c
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.sub contDiff_const
  have hgp : Function.Periodic g 1 := fun t ↦ by simp [g,hp t]
  let ψ : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t,g u
  have hd (t : ℝ) : HasDerivAt ψ (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable _ _)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuous.continuousAt
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply contDiff_infty_iff_deriv.mpr
    exact ⟨fun t ↦ (hd t).differentiableAt,(funext fun t ↦ (hd t).deriv) ▸ hg⟩
  have hz : (∫ u in (0 : ℝ)..1,g u)=0 := by
    rw [show g=(fun t ↦ f t-c) from rfl,
      intervalIntegral.integral_sub (hf.continuous.intervalIntegrable _ _)
        intervalIntegrable_const,intervalIntegral.integral_const]
    simp [c]
  refine ⟨ψ,hψ,?_,fun t ↦ (hd t).deriv⟩
  intro t
  change (∫ u in (0 : ℝ)..t+1,g u)=∫ u in (0 : ℝ)..t,g u
  rw [hgp.intervalIntegral_add_eq_add 0 t (fun _ _ ↦ hg.continuous.intervalIntegrable _ _)]
  simp only [zero_add,hz,add_zero]

lemma axial_scalar_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) (i : Fin 3) :
    ∀ (m : Fin 3 → ℤ) (x : Cover),f ((x+latticeVector m) i)=f (x i) := by
  intro m x
  simpa only [PiLp.add_apply,latticeVector,WithLp.ofLp_toLp,mul_one] using hp.int_mul (m i) (x i)

lemma axial_scalar_fderiv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (i : Fin 3) (x v : Cover) :
    fderiv ℝ (fun y : Cover ↦ f (y i)) x v=deriv f (x i)*v i := by
  have hh := (hf (x i)).hasDerivAt.comp_hasFDerivAt x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun y : Cover ↦ f (y i)) _ x at hh
  rw [hh.fderiv]
  rfl

lemma axial_field_divergence {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x : Cover) :
    divergence (fun y : Cover ↦ f (y i) • EuclideanSpace.single i 1) x=deriv f (x i) := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ f (y i)) x :=
    hf.differentiableAt.comp x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiableAt
  rw [divergence_smul_const hd,axial_scalar_fderiv hf]
  simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalSphere_sum_sq (ν : NormalSphere) : (∑ i : Fin 3,((ν : Cover) i)^2)=1 := by
  have hh := real_inner_self_eq_norm_sq (ν : Cover)
  rw [ν.property,one_pow] at hh
  simpa only [PiLp.inner_apply,RCLike.inner_apply,RCLike.conj_to_real,←pow_two] using hh

lemma normalSphere_coordinate_sq_le (ν : NormalSphere) (i : Fin 3) : ((ν : Cover) i)^2≤1 := by
  exact (Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) ↦ sq_nonneg ((ν : Cover) j))
    (Finset.mem_univ i)).trans_eq (normalSphere_sum_sq ν)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma circleMollifier_tendsto : Tendsto (fun n ↦ (circleMollifier n).rOut) atTop (𝓝 0) := by
  simpa only [circleMollifier,mul_one,mul_div,mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma circleSmoothApprox_contDiff {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (circleSmoothApprox f n) :=
  (circleMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (circleMollifier n).contDiff_normed hf.locallyIntegrable

lemma circleSmoothApprox_tendsto {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun n ↦ circleSmoothApprox f n x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous circleMollifier_tendsto hf x

lemma circleSmoothApprox_bound {f : ℝ → ℝ} {C : ℝ} (hb : ∀ x,‖f x‖≤C)
    (n : ℕ) (x : ℝ) : ‖circleSmoothApprox f n x‖≤C := by
  rw [circleSmoothApprox,convolution_def]
  calc
    _ ≤ ∫ y : ℝ,(circleMollifier n).normed volume y*C := by
      apply norm_integral_le_of_norm_le ((circleMollifier n).integrable_normed.mul_const C)
      filter_upwards [] with y
      rw [ContinuousLinearMap.lsmul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg ((circleMollifier n).nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (hb (x-y)) ((circleMollifier n).nonneg_normed y)
    _ = C := by rw [integral_mul_const,(circleMollifier n).integral_normed,one_mul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_AxisCircleLebesgue
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

lemma axialVolumeMarginal_integral (E : Set Torus) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i : AxisCircle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun x : Cover ↦ (x i : AxisCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircleLebesgue_eq_volume : (axisCircleLebesgue : Measure AxisCircle)=volume := by
  change Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1))=volume
  exact (show MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle))
    (volume.restrict (Ioc 0 1)) volume from by simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq

lemma torus_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Torus ↦ x i) torusVolume (volume : Measure AxisCircle) := by
  have he := measurePreserving_eval (fun _ : Fin 3 ↦ (volume : Measure AxisCircle)) i
  rw [←volume_pi] at he
  exact he.comp torus_to_product_measurePreserving

lemma cube_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Cover ↦ (x i : AxisCircle))
      (volume.restrict fundamentalCube) volume :=
  (torus_axis_measurePreserving i).comp quotientMap_measurePreserving

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_axisCircle_continuous (i : Fin 3) :
    Continuous (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircle_singleton_null (x : AxisCircle) : volume ({x} : Set AxisCircle)=0 := by
  let : Fact (0<(1 : ℝ)) := ⟨by norm_num⟩
  have hh := AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) (ε := (0 : ℝ))
  simpa using hh

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaMarginal
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

lemma torusAxialSplit_measurePreserving (i : Fin 3) :
    MeasurePreserving (torusAxialSplit i) torusVolume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ AxisCircle) i).comp
    torus_to_product_measurePreserving

lemma torusAxialSplit_symm_apply (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    (torusAxialSplit i).symm (t,y)=WithLp.toLp 2 (i.insertNth t y) := rfl

lemma axialSlice_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : AxisCircle) :
    MeasurableSet (axialSlice E i t) :=
  hE.preimage ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))

lemma axialSliceVolume_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Measurable (axialSliceVolume E i) := by
  exact measurable_measure_prodMk_left (hE.preimage (torusAxialSplit i).symm.measurable)

lemma axialVolumeMarginal_apply {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {s : Set AxisCircle} (hs : MeasurableSet s) :
    (axialVolumeMarginal E i : Measure AxisCircle) s=torusVolume (E∩{z : Torus | z i∈s}) := by
  have hm : Measurable (fun x : Cover ↦ (x i : AxisCircle)) :=
    (cube_axis_measurePreserving i).measurable
  change Measure.map _ _ s=_
  rw [Measure.map_apply hm hs,Measure.restrict_apply (hs.preimage hm)]
  have he : (fun x : Cover ↦ (x i : AxisCircle)) ⁻¹' s∩(fundamentalCube∩quotientMap ⁻¹' E)=
      quotientMap ⁻¹' (E∩{z : Torus | z i∈s})∩fundamentalCube := by
    ext x; simp only [mem_preimage,mem_inter_iff,mem_ofPred_eq]; tauto
  rw [he]
  have hS : MeasurableSet (E∩{z : Torus | z i∈s}) := hE.inter
    (hs.preimage (torus_axis_measurePreserving i).measurable)
  have hh := quotientMap_measurePreserving.measure_preimage hS.nullMeasurableSet
  rw [Measure.restrict_apply (hS.preimage continuous_quotientMap.measurable)] at hh
  exact hh

theorem axialVolumeMarginal_eq_withDensity {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    (axialVolumeMarginal E i : Measure AxisCircle)=volume.withDensity (axialSliceVolume E i) := by
  apply Measure.ext
  intro s hs
  rw [axialVolumeMarginal_apply hE i hs,withDensity_apply _ hs]
  have hS : MeasurableSet (E∩{z : Torus | z i∈s}) := hE.inter
    (hs.preimage (torus_axis_measurePreserving i).measurable)
  rw [←(torusAxialSplit_measurePreserving i).symm.measure_preimage hS.nullMeasurableSet]
  change (volume.prod volume) ((torusAxialSplit i).symm ⁻¹' (E∩{z : Torus | z i∈s}))=_
  rw [Measure.prod_apply (hS.preimage (torusAxialSplit i).symm.measurable),←lintegral_indicator hs]
  apply lintegral_congr
  intro t
  by_cases ht : t∈s
  · rw [indicator_of_mem ht]
    congr 1
    ext y
    simp [axialSlice,ht]
  · rw [indicator_of_notMem ht]
    have he : Prod.mk t ⁻¹' ((torusAxialSplit i).symm ⁻¹' (E∩{z : Torus | z i∈s}))=∅ := by
      ext y; simp [ht]
    rw [he,measure_empty]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialPlanePoint_dist (i : Fin 3) (t : ℝ) (x y : Plane) :
    dist (axialPlanePoint i t x) (axialPlanePoint i t y)=dist x y := by
  simp only [dist_eq_norm]
  have hs : ‖axialPlanePoint i t x-axialPlanePoint i t y‖^2=‖x-y‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succAbove _ i]
    simp [axialPlanePoint,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  nlinarith [norm_nonneg (axialPlanePoint i t x-axialPlanePoint i t y),norm_nonneg (x-y)]

lemma axialPlane_local_antilipschitz (i : Fin 3) (t : ℝ) (a : Plane) :
    AntilipschitzWith 1 (fun y : ball a (1/8 : ℝ) ↦ quotientMap (axialPlanePoint i t y)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one,one_mul,Subtype.dist_eq]
  have hs : ‖axialPlanePoint i t x-axialPlanePoint i t y‖<1/2 := by
    rw [←dist_eq_norm,axialPlanePoint_dist]
    exact (dist_triangle (x : Plane) a (y : Plane)).trans_lt (by have hy := y.property; rw [mem_ball,dist_comm] at hy; linarith [show dist (x : Plane) a<1/8 from x.property])
  have he : dist (quotientMap (axialPlanePoint i t x)) (quotientMap (axialPlanePoint i t y))=
      dist (axialPlanePoint i t x) (axialPlanePoint i t y) := by
    rw [dist_eq_norm,←quotientMap_sub,←norm_shortestLift,shortestLift_quotientMap hs,dist_eq_norm]
  rw [he,axialPlanePoint_dist]

lemma axialPlane_preimage_hausdorff_null (i : Fin 3) (t : ℝ) {S : Set Torus}
    (hS : Measure.hausdorffMeasure 2 S=0) :
    (volume : Measure Plane) ((fun y ↦ quotientMap (axialPlanePoint i t y)) ⁻¹' S)=0 := by
  let f : Plane → Torus := fun y ↦ quotientMap (axialPlanePoint i t y)
  have hl (a : Plane) : volume (f ⁻¹' S∩ball a (1/8 : ℝ))=0 := by
    have hh := (axialPlane_local_antilipschitz i t a).hausdorffMeasure_preimage_le (by norm_num : (0 : ℝ)≤2) S
    have hz : Measure.hausdorffMeasure 2 ((fun y : ball a (1/8 : ℝ) ↦ f y) ⁻¹' S)=0 := by
      apply le_zero_iff.mp
      simpa [hS] using hh
    have he := (isometry_subtype_coe : Isometry (Subtype.val : ball a (1/8 : ℝ) → Plane)).hausdorffMeasure_image
      (Or.inl (by norm_num : (0 : ℝ)≤2)) ((fun y : ball a (1/8 : ℝ) ↦ f y) ⁻¹' S)
    have ht : Subtype.val '' ((fun y : ball a (1/8 : ℝ) ↦ f y) ⁻¹' S)=f ⁻¹' S∩ball a (1/8 : ℝ) := by
      ext y; simp only [mem_image,mem_preimage,mem_inter_iff]; constructor
      · rintro ⟨z,hz,rfl⟩; exact ⟨hz,z.property⟩
      · rintro ⟨hy,hb⟩; exact ⟨⟨y,hb⟩,hy,rfl⟩
    rw [ht,hz] at he
    exact Measure.absolutelyContinuous_isAddHaarMeasure (volume : Measure Plane) (Measure.hausdorffMeasure 2) he
  obtain ⟨D,hD,hDD⟩ := TopologicalSpace.exists_countable_dense Plane
  have hc : ⋃ a∈D,ball a (1/8 : ℝ)=univ := (dense_iff_iUnion_ball D).mp hDD _ (by norm_num)
  have he : f ⁻¹' S=⋃ a∈D,f ⁻¹' S∩ball a (1/8 : ℝ) := by
    rw [←inter_iUnion₂,hc,inter_univ]
  rw [he]
  exact measure_biUnion_null_iff hD |>.mpr (fun a _ ↦ hl a)

lemma transverse_quotient_measurePreserving :
    MeasurePreserving (fun y : Fin 2 → ℝ ↦ fun j ↦ (y j : AxisCircle))
      ((volume : Measure (Fin 2 → ℝ)).restrict (univ.pi (fun _ ↦ Ico (0 : ℝ) 1))) volume := by
  have hh := measurePreserving_pi (fun _ : Fin 2 ↦ volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 2 ↦ (volume : Measure AxisCircle)) (fun _ ↦ circle_measurePreserving_mk_Ico)
  simpa only [volume_pi,Measure.restrict_pi_pi] using hh

lemma axialSlice_hausdorff_null (i : Fin 3) (t : AxisCircle) {S : Set Torus}
    (hSm : MeasurableSet S) (hS : Measure.hausdorffMeasure 2 S=0) : volume (axialSlice S i t)=0 := by
  induction t using Quotient.inductionOn with | h t =>
    have hp := axialPlane_preimage_hausdorff_null i t hS
    have he : (fun y : Fin 2 → ℝ ↦ (torusAxialSplit i).symm ((t : AxisCircle),fun j ↦ (y j : AxisCircle)))=
        (fun y : Plane ↦ quotientMap (axialPlanePoint i t y)) ∘ (WithLp.toLp 2) := by
      funext y
      apply PiLp.ext
      refine (Fin.forall_iff_succAbove i).mpr ⟨?_,?_⟩
      · simp [axialPlanePoint,torusAxialSplit_symm_apply,quotientMap]
      · intro j; simp [axialPlanePoint,torusAxialSplit_symm_apply,quotientMap]
    have hnull : volume ((fun y : Fin 2 → ℝ ↦ (torusAxialSplit i).symm ((t : AxisCircle),fun j ↦ (y j : AxisCircle))) ⁻¹' S)=0 := by
      rw [he,preimage_comp]
      exact (PiLp.volume_preserving_toLp (Fin 2)).quasiMeasurePreserving.preimage_null hp
    rw [←transverse_quotient_measurePreserving.map_eq,
      Measure.map_apply transverse_quotient_measurePreserving.measurable (axialSlice_measurable hSm i (t : AxisCircle))]
    exact le_zero_iff.mp ((Measure.restrict_le_self _) |>.trans_eq hnull)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_component_abs_le_one (ν : NormalSphere) (i : Fin 3) :
    |(ν : Cover) i|≤1 := by
  have hh := normalSphere_coordinate_sq_le ν i
  nlinarith [sq_abs ((ν : Cover) i),abs_nonneg ((ν : Cover) i)]

lemma axialPositiveFluxMarginal_absolutelyContinuous {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (axialPositiveFluxMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := ha hz
  change Measure.map _ _ s=0 at hh ⊢
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh ⊢
  exact withDensity_absolutelyContinuous _ _ hh

lemma axialPositiveFluxMarginal_integral (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialPositiveFluxMarginal μ i : Measure AxisCircle))=
      ∫ z,(1+((z.2 : Cover) i))*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1+((z.2 : Cover) i))) :=
    (continuous_const.add (normal_component_continuous i)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (by have hh := (abs_le.mp (normal_component_abs_le_one z.2 i)).1; linarith),smul_eq_mul]

lemma axialAreaMarginal_integral (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialAreaMarginal μ i : Measure AxisCircle))=
      ∫ z,f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  exact integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable

lemma axialNormalDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialNormalDensity μ i) :=
  Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv

lemma axialNormalDensity_pairing {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialNormalDensity μ i t*f t)=
      ∫ z,((z.2 : Cover) i)*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPositiveFluxMarginal_absolutelyContinuous i ha
  have hi (η : FiniteMeasure AxisCircle) : Integrable f (η : Measure AxisCircle) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
    (hf.comp (normal_axisCircle_continuous i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi'' : Integrable (fun z : NormalBundle ↦ (1+((z.2 : Cover) i))*f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
    ((continuous_const.add (normal_component_continuous i)).mul (hf.comp (normal_axisCircle_continuous i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [axialNormalDensity,sub_mul]
  rw [integral_sub ((integrable_toReal_rnDeriv_mul_iff hp).mpr (hi _))
    ((integrable_toReal_rnDeriv_mul_iff ha).mpr (hi _)),
    integral_toReal_rnDeriv_mul hp,integral_toReal_rnDeriv_mul ha,
    axialPositiveFluxMarginal_integral μ i hf,axialAreaMarginal_integral μ i hf,←integral_sub hi'' hi']
  apply integral_congr_ae
  filter_upwards [] with z
  ring

lemma axialSliceVolume_real_integrable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Integrable (fun t ↦ (axialSliceVolume E i t).toReal) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (axialSliceVolume_measurable hE i).ennreal_toReal.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using axialSliceVolume_le_one E i t)

theorem axialSliceVolume_weak_derivative {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1) :
    (∫ t,axialNormalDensity μ i t*hp.lift t)=
      ∫ t,(axialSliceVolume E i t).toReal*(real_periodic_deriv hp).lift t := by
  rw [axialNormalDensity_pairing i ha (continuous_periodic_lift hp hψ.continuous)]
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ ψ (x i) • (EuclideanSpace.single i 1 : Cover)) :=
    (hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul contDiff_const
  have hFp : ∀ m x,ψ ((x+latticeVector m) i) • (EuclideanSpace.single i 1 : Cover)=ψ (x i) • EuclideanSpace.single i 1 :=
    fun m x ↦ by rw [axial_scalar_periodic hp i m x]
  obtain ⟨M,_,hM⟩ := periodic_bounded hF.continuous hFp
  have hh := normalMeasure_flux hμ hF hFp (show 0<M+1 by linarith [hM 0])
    (fun x ↦ (hM x).trans (by linarith : M≤M+1))
  simp only [normalTest,ContinuousMap.coe_mk,real_inner_smul_right,EuclideanSpace.inner_single_right,
    axial_field_divergence (hψ.differentiable (by simp))] at hh
  have hd := continuous_periodic_lift (real_periodic_deriv hp) (hψ.continuous_deriv (by simp))
  have hvol := axialVolumeMarginal_integral E i hd
  rw [axialVolumeMarginal_eq_withDensity hE i,
    integral_withDensity_eq_integral_toReal_smul (axialSliceVolume_measurable hE i)
      (ae_of_all _ fun t ↦ lt_of_le_of_lt (axialSliceVolume_le_one E i t) ENNReal.one_lt_top)] at hvol
  simp only [smul_eq_mul,Function.Periodic.lift_coe] at hvol ⊢
  rw [hvol]
  simp only [starRingEnd_apply,star_trivial,one_mul] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_integrable_mul_continuous {h f : AxisCircle → ℝ} (hi : Integrable h)
    (hf : Continuous f) : Integrable (fun t ↦ h t*f t) := by
  let F : C(AxisCircle,ℝ) := ⟨f,hf⟩
  exact hi.mul_bdd hf.aestronglyMeasurable (ae_of_all _ fun t ↦ F.norm_coe_le_norm t)

lemma circle_integral_eq_interval {f : AxisCircle → ℝ} (hf : AEStronglyMeasurable f volume) :
    (∫ t,f t)=∫ t in (0 : ℝ)..1,f (t : AxisCircle) := by
  have hm : Measurable (fun t : ℝ ↦ (t : AxisCircle)) := (AddCircle.continuous_mk' (1 : ℝ)).measurable
  have hh := congrArg (fun η : Measure AxisCircle ↦ ∫ t,f t ∂η) axisCircleLebesgue_eq_volume
  change (∫ t,f t ∂Measure.map _ _)=_ at hh
  have hf' : AEStronglyMeasurable f (Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1))) := by
    change AEStronglyMeasurable f (axisCircleLebesgue : Measure AxisCircle)
    rwa [axisCircleLebesgue_eq_volume]
  rw [integral_map hm.aemeasurable hf'] at hh
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
  exact hh.symm

lemma circle_intervalIntegrable {f : AxisCircle → ℝ} (hf : Integrable f volume) :
    IntervalIntegrable (fun t : ℝ ↦ f (t : AxisCircle)) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
  exact ((show MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1)) volume from
    by simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0).integrable_comp hf.aestronglyMeasurable).mpr hf

lemma circle_lift_smoothing_integral_tendsto {h : AxisCircle → ℝ} (hi : Integrable h)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    let F : ℝ → ℝ := fun t ↦ f (t : AxisCircle)
    let hp : Function.Periodic F 1 := fun t ↦ by dsimp only [F]; rw [AddCircle.coe_add_period]
    Tendsto (fun n ↦ ∫ t,h t*(circleSmoothApprox_periodic hp n).lift t) atTop
      (𝓝 (∫ t,h t*f t)) := by
  intro F hp
  have hF : Continuous F := hf.comp (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨C,hC⟩ := (isCompact_univ.image hf).isBounded.exists_norm_le
  have hb (t : AxisCircle) : ‖f t‖≤C := hC _ ⟨t,mem_univ _,rfl⟩
  have hb' (t : ℝ) : ‖F t‖≤C := hb _
  apply tendsto_integral_of_dominated_convergence (fun t ↦ ‖h t‖*C)
  · intro n
    exact hi.aestronglyMeasurable.mul (continuous_periodic_lift (circleSmoothApprox_periodic hp n)
      (circleSmoothApprox_contDiff hF n).continuous).aestronglyMeasurable
  · exact hi.norm.mul_const C
  · intro n
    filter_upwards [] with t
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    induction t using Quotient.inductionOn with | h t =>
      exact circleSmoothApprox_bound hb' n t
  · filter_upwards [] with t
    induction t using Quotient.inductionOn with | h t =>
      exact tendsto_const_nhds.mul (circleSmoothApprox_tendsto hF t)

lemma integrable_circle_eq_zero_of_continuous_pairing {h : AxisCircle → ℝ}
    (hm : Measurable h) (hi : Integrable h)
    (hz : ∀ f : AxisCircle → ℝ,Continuous f → (∫ t,h t*f t)=0) : h=ᵐ[volume]0 := by
  let η := volume.withDensity (fun t ↦ ENNReal.ofReal (h t))
  let θ := volume.withDensity (fun t ↦ ENNReal.ofReal (-h t))
  have : IsFiniteMeasure η := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  have : IsFiniteMeasure θ := isFiniteMeasure_withDensity_ofReal hi.neg.hasFiniteIntegral
  have he : η=θ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    change (∫ t,f t ∂volume.withDensity _)=(∫ t,f t ∂volume.withDensity _)
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul (show Measurable (fun t ↦ ENNReal.ofReal (-h t)) from hm.neg.ennreal_ofReal) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal',smul_eq_mul]
    have hip : Integrable (fun t ↦ max (h t) 0*f t) := by
      exact circle_integrable_mul_continuous (hi.sup (integrable_const (0 : ℝ))) f.continuous
    have hin : Integrable (fun t ↦ max (-h t) 0*f t) := by
      exact circle_integrable_mul_continuous (hi.neg.sup (integrable_const (0 : ℝ))) f.continuous
    apply sub_eq_zero.mp
    rw [←integral_sub hip hin]
    convert hz f f.continuous using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards [] with t
    rcases le_total 0 (h t) with ht|ht
    · rw [max_eq_left ht,max_eq_right (neg_nonpos.mpr ht),zero_mul,sub_zero]
    · rw [max_eq_right ht,max_eq_left (neg_nonneg.mpr ht),zero_mul,zero_sub]; ring
  have hae := (withDensity_eq_iff_of_sigmaFinite hm.ennreal_ofReal.aemeasurable hm.neg.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hae] with t ht
  have hh := congrArg ENNReal.toReal ht
  simp only [ENNReal.toReal_ofReal',Pi.neg_apply] at hh
  change h t=0
  rcases le_total 0 (h t) with hle|hle
  · rw [max_eq_left hle,max_eq_right (neg_nonpos.mpr hle)] at hh; exact hh
  · rw [max_eq_right hle,max_eq_left (neg_nonneg.mpr hle)] at hh; linarith

theorem integrable_circle_constant_of_weak_derivative_zero {h : AxisCircle → ℝ}
    (hm : Measurable h) (hi : Integrable h)
    (hw : ∀ (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1),
      (∫ t,h t*(real_periodic_deriv hp).lift t)=0) :
    h=ᵐ[volume](fun _ ↦ ∫ t,h t) := by
  let c : ℝ := ∫ t,h t
  have hs : ∀ (f : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) f → ∀ hp : Function.Periodic f 1,
      (∫ t,(h t-c)*hp.lift t)=0 := by
    intro f hf hp
    obtain ⟨ψ,hψ,hψp,hd⟩ := smooth_periodic_centered_primitive hf hp
    have he : (real_periodic_deriv hψp).lift=(fun t : AxisCircle ↦ hp.lift t-∫ u in (0 : ℝ)..1,f u) := by
      funext t
      induction t using Quotient.inductionOn with | h t => exact hd t
    have hh := hw ψ hψ hψp
    rw [he] at hh
    have hfi : Integrable hp.lift := (continuous_periodic_lift hp hf.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hhi : Integrable (fun t ↦ h t*hp.lift t) := circle_integrable_mul_continuous hi (continuous_periodic_lift hp hf.continuous)
    simp only [mul_sub] at hh
    rw [integral_sub hhi (hi.mul_const _),integral_mul_const] at hh
    simp only [sub_mul]
    rw [integral_sub hhi (hfi.const_mul c),integral_const_mul]
    have hfint : (∫ t,hp.lift t)=∫ t in (0 : ℝ)..1,f t := by
      simpa only [Function.Periodic.lift_coe] using circle_integral_eq_interval hfi.aestronglyMeasurable
    rw [hfint]
    dsimp only [c]
    linarith
  have hz : ∀ f : AxisCircle → ℝ,Continuous f → (∫ t,(h t-c)*f t)=0 := by
    intro f hf
    have ht := circle_lift_smoothing_integral_tendsto (hi.sub (integrable_const c)) hf
    apply tendsto_nhds_unique ht
    apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    exact (hs _ (circleSmoothApprox_contDiff (hf.comp (AddCircle.continuous_mk' (1 : ℝ))) n) _).symm
  have hz' := integrable_circle_eq_zero_of_continuous_pairing (hm.sub measurable_const)
    (hi.sub (integrable_const c)) hz
  filter_upwards [hz'] with t ht
  exact sub_eq_zero.mp ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma interval_primitive_absolutelyContinuous {g : ℝ → ℝ}
    (hi : ∀ a b,IntervalIntegrable g volume a b) (a b c : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ s in c..t,g s) a b := by
  have he : (fun t ↦ ∫ s in c..t,g s)=(fun t ↦ (∫ s in c..a,g s)+(∫ s in a..t,g s)) := by
    funext t
    exact (intervalIntegral.integral_add_adjacent_intervals (hi c a) (hi a t)).symm
  rw [he]
  exact (show ContDiff ℝ 1 (fun _ : ℝ ↦ ∫ s in c..a,g s) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval.add
    ((hi a b).absolutelyContinuousOnInterval_intervalIntegral (by simp))

lemma circle_ac_primitive {g : AxisCircle → ℝ} (hi : Integrable g) (hz : (∫ t,g t)=0) :
    ∃ (P : ℝ → ℝ) (hp : Function.Periodic P 1),Continuous P ∧
      (∀ a b,AbsolutelyContinuousOnInterval P a b) ∧
      (∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt P (g (t : AxisCircle)) t) ∧
      ∀ (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : Function.Periodic ψ 1),
        (∫ t,hp.lift t*(real_periodic_deriv hψp).lift t)=-(∫ t,g t*hψp.lift t) := by
  let G : ℝ → ℝ := fun t ↦ g (t : AxisCircle)
  have hGp : Function.Periodic G 1 := fun t ↦ by dsimp only [G]; rw [AddCircle.coe_add_period]
  have hGi (a b : ℝ) : IntervalIntegrable G volume a b :=
    hGp.intervalIntegrable₀ (by norm_num) (circle_intervalIntegrable hi) a b
  let P : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t,G s
  have hPc : Continuous P := intervalIntegral.continuous_primitive hGi 0
  have hP0 : P 0=0 := intervalIntegral.integral_same
  have hP1 : P 1=0 := (circle_integral_eq_interval hi.aestronglyMeasurable).symm.trans hz
  have hPp : Function.Periodic P 1 := by
    intro t
    change (∫ s in (0 : ℝ)..t+1,G s)=∫ s in (0 : ℝ)..t,G s
    rw [hGp.intervalIntegral_add_eq_add 0 t hGi]
    rw [zero_add]
    change P t+P 1=P t
    rw [hP1,add_zero]
  have hPac (a b : ℝ) : AbsolutelyContinuousOnInterval P a b :=
    interval_primitive_absolutelyContinuous hGi a b 0
  have hPd : ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt P (G t) t := by
    filter_upwards [(hGi 0 1).ae_hasDerivAt_integral] with t ht hti
    exact ht (by simpa using hti) 0 (by simp)
  refine ⟨P,hPp,hPc,hPac,hPd,?_⟩
  intro ψ hψ hψp
  have hψc := continuous_periodic_lift hψp hψ.continuous
  have hdc := continuous_periodic_lift (real_periodic_deriv hψp) (hψ.continuous_deriv (by simp))
  have hPc' := continuous_periodic_lift hPp hPc
  rw [circle_integral_eq_interval (show AEStronglyMeasurable (fun t ↦ hPp.lift t*(real_periodic_deriv hψp).lift t) volume from (hPc'.mul hdc).aestronglyMeasurable),
    circle_integral_eq_interval (circle_integrable_mul_continuous hi hψc).aestronglyMeasurable]
  simp only [Function.Periodic.lift_coe]
  have hparts := (hPac 0 1).integral_mul_deriv_eq_deriv_mul
    (hψ.of_le (by simp) : ContDiff ℝ 1 ψ).contDiffOn.absolutelyContinuousOnInterval
  rw [hP1,hP0,zero_mul,zero_mul,sub_self,zero_sub] at hparts
  rw [hparts]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hPd] with t ht hti
  rw [(ht (by simpa using uIoc_subset_uIcc hti)).deriv]

theorem circle_weak_integrable_has_ac_representative {u g : AxisCircle → ℝ}
    (hu : Measurable u) (hui : Integrable u) (hgi : Integrable g)
    (hw : ∀ (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1),
      (∫ t,g t*hp.lift t)=(∫ t,u t*(real_periodic_deriv hp).lift t)) :
    ∃ (f : ℝ → ℝ) (hp : Function.Periodic f 1),Continuous f ∧
      (∀ a b,AbsolutelyContinuousOnInterval f a b) ∧ u=ᵐ[volume]hp.lift ∧
      ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt f (-g (t : AxisCircle)) t := by
  have hg0 : (∫ t,g t)=0 := by
    have hp : Function.Periodic (fun _ : ℝ ↦ (1 : ℝ)) 1 := fun _ ↦ rfl
    have hh := hw (fun _ ↦ 1) contDiff_const hp
    have he (t : AxisCircle) : hp.lift t=1 := by
      induction t using Quotient.inductionOn with | h t => rfl
    have hd (t : AxisCircle) : (real_periodic_deriv hp).lift t=0 := by
      induction t using Quotient.inductionOn with | h t => exact deriv_const t 1
    simpa only [he,hd,mul_one,mul_zero,integral_zero] using hh
  obtain ⟨P,hPp,hPc,hPac,hPd,hPw⟩ := circle_ac_primitive hgi hg0
  have hPlc := continuous_periodic_lift hPp hPc
  have hPi : Integrable hPp.lift := hPlc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hzero : ∀ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1),
      (∫ t,(u t+hPp.lift t)*(real_periodic_deriv hp).lift t)=0 := by
    intro ψ hψ hp
    have hc := continuous_periodic_lift (real_periodic_deriv hp) (hψ.continuous_deriv (by simp))
    simp only [add_mul]
    rw [integral_add (circle_integrable_mul_continuous hui hc) (circle_integrable_mul_continuous hPi hc),
      hPw ψ hψ hp,hw ψ hψ hp,add_neg_cancel]
  let c := ∫ t,u t+hPp.lift t
  have hae := integrable_circle_constant_of_weak_derivative_zero (hu.add hPlc.measurable)
    (hui.add hPi) hzero
  let f : ℝ → ℝ := fun t ↦ c-P t
  have hfp : Function.Periodic f 1 := fun t ↦ by dsimp only [f]; rw [hPp t]
  refine ⟨f,hfp,continuous_const.sub hPc,?_,?_,?_⟩
  · intro a b
    exact (show ContDiff ℝ 1 (fun _ : ℝ ↦ c) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval.sub (hPac a b)
  · filter_upwards [hae] with t ht
    have he : hfp.lift t=c-hPp.lift t := by
      induction t using Quotient.inductionOn with | h t => rfl
    rw [he]
    change u t+hPp.lift t=c at ht
    linarith
  · filter_upwards [hPd] with t ht hti
    exact (ht hti).const_sub c

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSlice_point_continuous (i : Fin 3) (y : TransverseProduct) :
    Continuous (fun t : AxisCircle ↦ (torusAxialSplit i).symm (t,y)) := by
  change Continuous (fun t : AxisCircle ↦ WithLp.toLp 2 (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  exact (Fin.forall_iff_succAbove (P := fun j : Fin 3 ↦ Continuous (fun t : AxisCircle ↦ (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y) j)) i).mpr ⟨by simp only [Fin.insertNth_apply_same]; exact continuous_id,fun k ↦ by simp only [Fin.insertNth_apply_succAbove]; exact continuous_const⟩ j

lemma isMinimizerAt_boundary_slice_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) (t : AxisCircle) :
    volume (axialSlice (frontier (openRepresentative E)) i t)=0 := by
  let T : Set Torus := {z | z i=t}
  have hT : MeasurableSet T := measurableSet_eq_fun (torus_axis_measurePreserving i).measurable measurable_const
  have ht : (spatialNormalMeasure μ : Measure Torus) T=0 := by
    have hh := ha (axisCircle_singleton_null t)
    change Measure.map _ _ {t}=0 at hh
    rw [Measure.map_apply (normal_axisCircle_continuous i).measurable (measurableSet_singleton t)] at hh
    change Measure.map normalProjection _ T=0
    rw [Measure.map_apply normalProjection_continuous.measurable hT]
    exact hh
  have hh := isMinimizerAt_boundary_area_absolutelyContinuous hV hE hmin hμ ht
  rw [Measure.restrict_apply hT] at hh
  have hs := axialSlice_hausdorff_null i t (hT.inter isClosed_frontier.measurableSet) hh
  have he : axialSlice (T∩frontier (openRepresentative E)) i t=axialSlice (frontier (openRepresentative E)) i t := by
    ext y
    simp [axialSlice,T]
  rwa [he] at hs

lemma axialSliceVolume_continuous_of_boundary_null {U : Set Torus} (hU : MeasurableSet U)
    (i : Fin 3) (hn : ∀ t : AxisCircle,volume (axialSlice (frontier U) i t)=0) :
    Continuous (fun t ↦ (axialSliceVolume U i t).toReal) := by
  let F : AxisCircle → TransverseProduct → ℝ := fun t y ↦ U.indicator (fun _ ↦ (1 : ℝ)) ((torusAxialSplit i).symm (t,y))
  have he (t : AxisCircle) : (∫ y,F t y)=(axialSliceVolume U i t).toReal := by
    have hf : F t=(axialSlice U i t).indicator 1 := by
      funext y
      by_cases hy : (torusAxialSplit i).symm (t,y)∈U <;> simp [F,axialSlice,hy]
    rw [hf,integral_indicator_one (axialSlice_measurable hU i t)]
    rfl
  rw [show (fun t ↦ (axialSliceVolume U i t).toReal)=(fun t ↦ ∫ y,F t y) from funext (fun t ↦ (he t).symm)]
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_of_dominated (bound := fun _ ↦ (1 : ℝ))
  · apply Eventually.of_forall
    intro s
    exact (measurable_const.indicator hU |>.comp ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro s
    apply ae_of_all
    intro y
    exact (norm_indicator_le_norm_self (s := U) (fun _ ↦ (1 : ℝ)) ((torusAxialSplit i).symm (s,y))).trans (by norm_num)
  · exact integrable_const 1
  · have hnb : ∀ᵐ y : TransverseProduct,(torusAxialSplit i).symm (t,y)∉frontier U := by
      rw [ae_iff]
      simpa only [not_not,axialSlice] using hn t
    filter_upwards [hnb] with y hy
    change ContinuousAt (fun s ↦ U.indicator (fun _ ↦ (1 : ℝ)) ((torusAxialSplit i).symm (s,y))) t
    exact ContinuousAt.comp (f := fun s ↦ (torusAxialSplit i).symm (s,y)) (g := U.indicator (fun _ ↦ (1 : ℝ))) (continuous_const.continuousOn.continuousAt_indicator hy) (axialSlice_point_continuous i y).continuousAt

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ActualAxialFlux
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

theorem isMinimizerAt_slice_absolutelyContinuous_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (∀ a b,AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal) a b) ∧
    ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt
      (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal)
      (-axialNormalDensity μ i (t : AxisCircle)) t := by
  have hU : MeasurableSet (openRepresentative E) := (isOpen_openRepresentative E).measurableSet
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hc := axialSliceVolume_continuous_of_boundary_null hU i
    (isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha)
  obtain ⟨f,hp,hfc,hfac,hae,hd⟩ := circle_weak_integrable_has_ac_representative
    (axialSliceVolume_measurable hU i).ennreal_toReal (axialSliceVolume_real_integrable hU i)
    (axialNormalDensity_integrable μ i)
    (fun ψ hψ hψp ↦ axialSliceVolume_weak_derivative hU hμU i ha hψ hψp)
  have he := (hc.ae_eq_iff_eq (volume : Measure AxisCircle) (continuous_periodic_lift hp hfc)).mp hae
  have he' : (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal)=f := by
    funext t
    exact congrFun he (t : AxisCircle)
  rw [he']
  exact ⟨hfac,hd⟩

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous_oai := @OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous_oai
