-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:12:53.433011+00:00
-- url     : https://prove2.me/submissions/52ef2a87-c521-4002-adb0-d07e275f93c5

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_axialSurface_density_eq_flux
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_global_normal
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_missing_neighbor_flux_unrestricted
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_lower_density
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary
import Theorems.Thm_OAI_CubicTorus_normal_transverse_near_reflection_height

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

lemma fderiv_component {F : Cover → Cover} {x : Cover} (hF : DifferentiableAt ℝ F x)
    (i : Fin 3) (v : Cover) :
    fderiv ℝ (fun y ↦ F y i) x v = fderiv ℝ F x v i := by
  have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ F y i) x = _ at hh
  rw [hh]
  rfl

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
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
open Laplacian
namespace CubicTorus

lemma directionalFlux_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F)
    (i : Fin 3) (g : Cover → ℝ) : directionalFlux E i g = directionalFlux F i g := by
  exact setIntegral_congr_set (liftSet_congr_ae h)

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

end Periodic
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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma regularizedNormal_denom_pos (v : Cover) :
    0<‖v‖^2+(1-Real.smoothTransition (4*‖v‖^2)) := by
  by_cases h : v=0
  · simp [h]
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr h))
      (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma regularizedNormal_contDiff {R : Cover → Cover}
    (hR : ContDiff ℝ (⊤ : ℕ∞) R) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedNormal R) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ‖R x‖^2) := hR.norm_sq ℝ
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ ‖R x‖^2+(1-Real.smoothTransition (4*‖R x‖^2))) :=
    hq.add (contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_const.mul hq)))
  exact ((hd.sqrt (fun x ↦ (regularizedNormal_denom_pos _).ne')).inv
    (fun x ↦ (Real.sqrt_pos.mpr (regularizedNormal_denom_pos _)).ne')).smul hR

lemma regularizedNormal_eq {R : Cover → Cover} {x : Cover} (h : (1/4 : ℝ)≤‖R x‖^2) :
    regularizedNormal R x=‖R x‖⁻¹ • R x := by
  unfold regularizedNormal
  rw [Real.smoothTransition.one_of_one_le (by linarith),sub_self,add_zero,
    Real.sqrt_sq (norm_nonneg _)]

lemma regularizedNormal_unit_near {R : Cover → Cover} (hR : Continuous R) {x : Cover}
    (hx : (1/4 : ℝ)<‖R x‖^2) :
    ∀ᶠ y in 𝓝 x,‖regularizedNormal R y‖=1 := by
  have hnear : ∀ᶠ y in 𝓝 x,(1/4 : ℝ)<‖R y‖^2 :=
    (hR.norm.pow 2).continuousAt.eventually (lt_mem_nhds hx)
  filter_upwards [hnear] with y hy
  have hn : 0<‖R y‖ := lt_of_not_ge fun h ↦ by
    have hz := le_antisymm h (norm_nonneg _)
    rw [hz] at hy
    norm_num at hy
  rw [regularizedNormal_eq hy.le,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
    inv_mul_cancel₀ hn.ne']

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

lemma regularizedNormal_eventuallyEq {N : Cover → Cover} {x : Cover}
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) : regularizedNormal N=ᶠ[𝓝 x]N := by
  filter_upwards [hu] with y hy
  rw [regularizedNormal_eq (by rw [hy]; norm_num),hy,inv_one,one_smul]

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

end Periodic
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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_stationary_tubular_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) :
    ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H := by
  obtain ⟨N,hN,hp,hn⟩ := isMinimizerAt_global_normal hV hE hmin hμ
  have hH := weakCMC_normal_extension hCMC hN hp hn
  have hpoint (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      ‖N x‖=1 ∧ divergence N x=H := by
    constructor
    · apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hN.continuous.norm
        continuous_const (fun m y ↦ by rw [hp]) (fun _ _ ↦ rfl) _ x hx
      filter_upwards [hn] with z hz
      rw [hz.1,z.2.property]
    · exact isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ (continuous_divergence hN)
        continuous_const (divergence_periodic hp) (fun _ _ ↦ rfl) hH x hx
  have hR := regularizedNormal_contDiff hN
  have hrp : ∀ m x,regularizedNormal N (x+latticeVector m)=regularizedNormal N x := by
    intro m x
    simp only [regularizedNormal,hp]
  have he : ∀ᵐ z ∂(μ : Measure NormalBundle),regularizedNormal N=ᶠ[𝓝 (z.1 : Cover)]N := by
    filter_upwards [hn] with z hz
    exact regularizedNormal_eventuallyEq hz.2
  refine ⟨regularizedNormal N,hR,hrp,?_,?_⟩
  · filter_upwards [hn,he] with z hz hze
    exact hze.eq_of_nhds.trans hz.1
  · intro x hx
    refine ⟨regularizedNormal_unit_near hN.continuous (by rw [(hpoint x hx).1]; norm_num),?_⟩
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (continuous_divergence hR) (continuous_divergence hN)
      (divergence_periodic hrp) (divergence_periodic hp) _ x hx |>.trans (hpoint x hx).2
    filter_upwards [he] with z hz
    simp only [divergence_eq_coverTrace,hz.fderiv_eq]

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

lemma torus_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Torus ↦ x i) torusVolume (volume : Measure AxisCircle) := by
  have he := measurePreserving_eval (fun _ : Fin 3 ↦ (volume : Measure AxisCircle)) i
  rw [←volume_pi] at he
  exact he.comp torus_to_product_measurePreserving

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

lemma circle_integrable_mul_continuous {h f : AxisCircle → ℝ} (hi : Integrable h)
    (hf : Continuous f) : Integrable (fun t ↦ h t*f t) := by
  let F : C(AxisCircle,ℝ) := ⟨f,hf⟩
  exact hi.mul_bdd hf.aestronglyMeasurable (ae_of_all _ fun t ↦ F.norm_coe_le_norm t)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalTransverseLength
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

lemma normalTransverseLength_nonneg (i : Fin 3) (z : NormalBundle) :
    0≤normalTransverseLength i z := Real.sqrt_nonneg _

lemma normalTransverseLength_sq (i : Fin 3) (z : NormalBundle) :
    (normalTransverseLength i z)^2+((z.2 : Cover) i)^2=1 := by
  rw [normalTransverseLength,Real.sq_sqrt (sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i))]
  ring

lemma axialPerimeterMarginal_absolutelyContinuous {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (axialPerimeterMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := ha hz
  change Measure.map _ _ s=0 at hh ⊢
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh ⊢
  exact withDensity_absolutelyContinuous _ _ hh

lemma axialPerimeterDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialPerimeterDensity μ i) := Measure.integrable_toReal_rnDeriv

lemma axialPerimeterDensity_pairing_bounded {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Measurable f) (_hb : ∀ t,|f t|≤1) :
    (∫ t,axialPerimeterDensity μ i t*f t)=
      ∫ z,normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPerimeterMarginal_absolutelyContinuous i ha
  change (∫ t,((axialPerimeterMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal*f t)=_
  rw [integral_toReal_rnDeriv_mul hp]
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (normalTransverseLength_continuous i).measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (normalTransverseLength_nonneg i z),smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma bounded_real_locallyIntegrable {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) : LocallyIntegrable f volume := by
  apply (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).locallyIntegrable.mono hf.aestronglyMeasurable
  exact ae_of_all _ fun t ↦ by simpa only [Real.norm_eq_abs,abs_one] using hb t

lemma circleSmoothApprox_bounded_contDiff {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (circleSmoothApprox f n) :=
  (circleMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (circleMollifier n).contDiff_normed
    (bounded_real_locallyIntegrable hf hb)

lemma circleSmoothApprox_nonneg {f : ℝ → ℝ} (hf : ∀ t,0≤f t) (n : ℕ) (t : ℝ) :
    0 ≤ circleSmoothApprox f n t := by
  rw [circleSmoothApprox,convolution_def]
  exact integral_nonneg fun x ↦ mul_nonneg ((circleMollifier n).nonneg_normed x) (hf (t-x))

lemma circleSmoothApprox_bounded_ae_tendsto {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) :
    ∀ᵐ t : ℝ,Tendsto (fun n ↦ circleSmoothApprox f n t) atTop (𝓝 (f t)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    circleMollifier_tendsto (K := 2) _ (bounded_real_locallyIntegrable hf hb)
  exact Eventually.of_forall fun n ↦ by dsimp [circleMollifier]; ring_nf; rfl

lemma circleSmoothApprox_lift_ae_tendsto {f : AxisCircle → ℝ} (hf : Measurable f)
    (hb : ∀ t,|f t|≤1) :
    let F : ℝ → ℝ := fun t ↦ f (t : AxisCircle)
    let hp : Function.Periodic F 1 := fun t ↦ by dsimp only [F]; rw [AddCircle.coe_add_period]
    ∀ᵐ t : AxisCircle,Tendsto (fun n ↦ (circleSmoothApprox_periodic hp n).lift t) atTop (𝓝 (f t)) := by
  intro F hp
  have hfm : Measurable F := hf.comp (AddCircle.continuous_mk' (1 : ℝ)).measurable
  have hh := ae_restrict_of_ae (s := Ioc (0 : ℝ) 1) (circleSmoothApprox_bounded_ae_tendsto hfm (fun t ↦ hb _))
  have hmp : MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [←hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable (measurableSet_tendsto_fun
    (fun n ↦ (continuous_periodic_lift (circleSmoothApprox_periodic hp n)
      (circleSmoothApprox_bounded_contDiff hfm (fun t ↦ hb _) n).continuous).measurable) hf)).mpr
  simpa only [Function.Periodic.lift_coe] using hh

theorem integrable_circle_nonneg_of_smooth_pairing {h : AxisCircle → ℝ} (hi : Integrable h)
    (hw : ∀ (ψ : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) ψ → ∀ hp : Function.Periodic ψ 1,
      (∀ t,0≤ψ t) → 0≤∫ t,h t*hp.lift t) : 0≤ᵐ[volume] h := by
  apply ae_nonneg_of_forall_setIntegral_nonneg hi
  intro s hs _
  let f : AxisCircle → ℝ := s.indicator (fun _ ↦ (1 : ℝ))
  let F : ℝ → ℝ := fun t ↦ f (t : AxisCircle)
  have hf : Measurable f := measurable_const.indicator hs
  have hb (t : AxisCircle) : |f t|≤1 := by
    by_cases ht : t∈s <;> simp [f,ht]
  have hn (t : ℝ) : 0≤F t := by apply indicator_nonneg; intro _ _; norm_num
  have hp : Function.Periodic F 1 := fun t ↦ by dsimp only [F]; rw [AddCircle.coe_add_period]
  have hc n := circleSmoothApprox_bounded_contDiff (hf.comp (AddCircle.continuous_mk' (1 : ℝ)).measurable)
    (fun t ↦ hb _) n
  have hl : Tendsto (fun n ↦ ∫ t,h t*(circleSmoothApprox_periodic hp n).lift t) atTop
      (𝓝 (∫ t,h t*f t)) := by
    apply tendsto_integral_of_dominated_convergence (fun t ↦ ‖h t‖)
    · intro n
      exact hi.aestronglyMeasurable.mul (continuous_periodic_lift (circleSmoothApprox_periodic hp n)
        (hc n).continuous).aestronglyMeasurable
    · exact hi.norm
    · intro n
      filter_upwards [] with t
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      induction t using Quotient.inductionOn with | h t =>
        exact circleSmoothApprox_bound (fun t ↦ by simpa only [Real.norm_eq_abs] using hb (t : AxisCircle)) n t
    · filter_upwards [circleSmoothApprox_lift_ae_tendsto hf hb] with t ht
      exact tendsto_const_nhds.mul ht
  have hh : 0≤∫ t,h t*f t := ge_of_tendsto hl (Eventually.of_forall fun n ↦
    hw _ (hc n) (circleSmoothApprox_periodic hp n) (circleSmoothApprox_nonneg hn n))
  have he : (fun t ↦ h t*f t)=s.indicator h := by
    funext t
    by_cases ht : t∈s <;> simp [f,ht]
  rwa [he,integral_indicator hs] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSliceIntegral_indicator {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (f : Torus → ℝ) (t : AxisCircle) :
    axialSliceIntegral E i f t=∫ y,E.indicator f ((torusAxialSplit i).symm (t,y)) := by
  rw [axialSliceIntegral,←integral_indicator (axialSlice_measurable hE i t)]
  congr 1

lemma axialSliceIntegral_integrable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {f : Torus → ℝ} (hf : Integrable f torusVolume) : Integrable (axialSliceIntegral E i f) := by
  have hg := (torusAxialSplit_measurePreserving i).symm.integrable_comp_of_integrable (hf.indicator hE)
  have hh := hg.integral_prod_left
  simpa only [Function.comp_apply,←axialSliceIntegral_indicator hE] using hh

lemma axialSliceIntegral_pairing {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {f : Torus → ℝ} (hf : Continuous f) {ψ : AxisCircle → ℝ} (hψ : Continuous ψ) :
    (∫ t,ψ t*axialSliceIntegral E i f t)=∫ z in E,ψ (z i)*f z ∂torusVolume := by
  have hi : Integrable (fun z : Torus ↦ ψ (z i)*f z) torusVolume :=
    ((hψ.comp (PiLp.continuous_apply 2 _ i)).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg := (torusAxialSplit_measurePreserving i).symm.integrable_comp_of_integrable (hi.indicator hE)
  rw [←integral_indicator hE,←(torusAxialSplit_measurePreserving i).symm.integral_comp'
    (E.indicator (fun z : Torus ↦ ψ (z i)*f z))]
  change _=∫ z,((E.indicator (fun z : Torus ↦ ψ (z i)*f z)) ∘ (torusAxialSplit i).symm) z ∂volume.prod volume
  rw [integral_prod _ hg]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [axialSliceIntegral_indicator hE,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : (torusAxialSplit i).symm (t,y)∈E <;> simp [hy]

lemma normal_transverse_inner_bound (i : Fin 3) (z : NormalBundle) (v : Cover)
    (hv : v i=0) (hb : ‖v‖≤1) : ⟪(z.2 : Cover),v⟫≤normalTransverseLength i z := by
  let n : Cover := (z.2 : Cover)-((z.2 : Cover) i) • EuclideanSpace.single i 1
  have hn : ‖n‖=normalTransverseLength i z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (normalTransverseLength_nonneg i z)).mp
    have hz : ‖(z.2 : Cover)‖=1 := z.2.property
    have hs := normalTransverseLength_sq i z
    dsimp only [n]
    rw [norm_sub_sq_real,real_inner_smul_right,EuclideanSpace.inner_single_right,norm_smul,
      PiLp.norm_single,Real.norm_eq_abs,Real.norm_eq_abs,abs_one,mul_one,hz]
    simp only [conj_trivial,one_mul] at *
    nlinarith [sq_abs ((z.2 : Cover) i)]
  have he : ⟪n,v⟫=⟪(z.2 : Cover),v⟫ := by
    simp [n,inner_sub_left,real_inner_smul_left,EuclideanSpace.inner_single_left,hv]
  rw [←he]
  calc
    _ ≤ ‖n‖*‖v‖ := real_inner_le_norm _ _
    _ ≤ ‖n‖ := mul_le_of_le_one_right (norm_nonneg _) hb
    _ = _ := hn

lemma axialPerimeterDensity_pairing_continuous {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialPerimeterDensity μ i t*f t)=
      ∫ z,normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPerimeterMarginal_absolutelyContinuous i ha
  change (∫ t,((axialPerimeterMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal*f t)=_
  rw [integral_toReal_rnDeriv_mul hp]
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (normalTransverseLength_continuous i).measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (normalTransverseLength_nonneg i z),smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axial_weight_divergence {i : Fin 3} {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFi : ∀ x,F x i=0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Cover) :
    divergence (fun y : Cover ↦ ψ (y i) • F y) x=ψ (x i)*divergence F x := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ ψ (y i)) x :=
    ((hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).differentiable (by simp)).differentiableAt
  rw [divergence_smul_function hd
    (hF.differentiable (by simp)).differentiableAt,inner_gradient_left,
    axial_scalar_fderiv (hψ.differentiable (by simp)),hFi,mul_zero,add_zero]

theorem axialSliceIntegral_weighted_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {F : Cover → Cover} (hF : AdmissibleField F) (hFi : ∀ x,F x i=0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : Function.Periodic ψ 1)
    (hn : ∀ t,0≤ψ t) :
    (∫ t,hp.lift t*axialSliceIntegral E i (fun z ↦ divergence F (representative z)) t)≤
      ∫ t,hp.lift t*axialPerimeterDensity μ i t := by
  let G : Cover → Cover := fun x ↦ ψ (x i) • F x
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul hF.1
  have hGp : ∀ m x,G (x+latticeVector m)=G x := by
    intro m x
    dsimp only [G]
    rw [axial_scalar_periodic hp i m x,hF.2.1]
  obtain ⟨C,hC,hCb⟩ := periodic_bounded hG.continuous hGp
  have hflux := normalMeasure_flux hμ hG hGp (show 0<C+1 by linarith) (fun x ↦ (hCb x).trans (by linarith))
  have hd : Continuous (fun z : Torus ↦ divergence F (representative z)) :=
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  have hp' := continuous_periodic_lift hp hψ.continuous
  rw [axialSliceIntegral_pairing hE i hd hp']
  have he : (fun z : Torus ↦ hp.lift (z i)*divergence F (representative z))=
      (fun z : Torus ↦ divergence G (representative z)) := by
    funext z
    rw [axial_weight_divergence hF.1 hFi hψ]
    congr 1
    have hh := congrArg (fun a : Torus ↦ hp.lift (a i)) (quotientMap_representative z)
    exact hh.symm
  rw [he,setIntegral_lift (continuous_divergence hG) (divergence_periodic hGp) hE,←hflux]
  simp_rw [mul_comm (hp.lift _) (axialPerimeterDensity μ i _)]
  rw [axialPerimeterDensity_pairing_continuous i ha hp']
  apply integral_mono
  · exact (normalTest G hG.continuous).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((normalTransverseLength_continuous i).mul (hp'.comp (normal_axisCircle_continuous i))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover),ψ ((z.1 : Cover) i) • F z.1⟫≤_
    simp only [real_inner_smul_right,Function.Periodic.lift_coe]
    rw [mul_comm (normalTransverseLength i z)]
    exact mul_le_mul_of_nonneg_left (normal_transverse_inner_bound i z _ (hFi _) (hF.2.2 _)) (hn _)

theorem axialSliceIntegral_ae_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {F : Cover → Cover} (hF : AdmissibleField F) (hFi : ∀ x,F x i=0) :
    axialSliceIntegral E i (fun z ↦ divergence F (representative z))≤ᵐ[volume]axialPerimeterDensity μ i := by
  have hd : Continuous (fun z : Torus ↦ divergence F (representative z)) :=
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  have hdI := hd.integrable_of_hasCompactSupport (μ := torusVolume) (HasCompactSupport.of_compactSpace _)
  have hs := axialSliceIntegral_integrable hE i hdI
  have hi := axialPerimeterDensity_integrable μ i
  have hh := integrable_circle_nonneg_of_smooth_pairing (hi.sub hs) (by
    intro ψ hψ hp hn
    have hc := continuous_periodic_lift hp hψ.continuous
    simp only [Pi.sub_apply,sub_mul]
    rw [integral_sub (circle_integrable_mul_continuous hi hc) (circle_integrable_mul_continuous hs hc)]
    apply sub_nonneg.mpr
    simpa only [mul_comm] using axialSliceIntegral_weighted_le hE hμ i ha hF hFi hψ hp hn)
  filter_upwards [hh] with t ht
  exact sub_nonneg.mp ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeAxisEmbedding_norm (i : Fin 3) (y : Plane) : ‖planeAxisEmbedding i y‖=‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succAbove _ i]
  simp

lemma planeAxisProjection_norm_le (i : Fin 3) (x : Cover) : ‖planeAxisProjection i x‖≤‖x‖ := by
  have hh : ‖planeAxisProjection i x‖^2≤‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succAbove _ i]
    simp only [planeAxisProjection_apply]
    nlinarith [sq_nonneg ‖x i‖]
  nlinarith [norm_nonneg (planeAxisProjection i x),norm_nonneg x]

lemma liftPlanarField_admissible (i : Fin 3) {G : Plane → Plane}
    (hG : PlanarAdmissibleField G) : AdmissibleField (liftPlanarField i G) := by
  refine ⟨(planeAxisEmbedding i).contDiff.comp (hG.1.comp (planeAxisProjection i).contDiff),?_,?_⟩
  · intro n x
    unfold liftPlanarField
    rw [map_add]
    exact congrArg (planeAxisEmbedding i) (hG.2.1 (fun j ↦ n (i.succAbove j)) _)
  · intro x
    rw [liftPlanarField,planeAxisEmbedding_norm]
    exact hG.2.2 _

lemma divergence_liftPlanarField (i : Fin 3) {G : Plane → Plane}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Cover) :
    divergence (liftPlanarField i G) x=planeDivergence G (planeAxisProjection i x) := by
  have hd := (planeAxisEmbedding i).hasFDerivAt.comp x
    (((hG.differentiable (by simp) (planeAxisProjection i x)).hasFDerivAt).comp x
      (planeAxisProjection i).hasFDerivAt)
  change HasFDerivAt (liftPlanarField i G) _ x at hd
  rw [divergence,hd.fderiv,Fin.sum_univ_succAbove _ i]
  simp [ContinuousLinearMap.comp_apply,planeDivergence,Fin.sum_univ_two]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeAxisAt_contDiff (i : Fin 3) (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (planeAxisAt i a) :=
  contDiff_const.add (planeAxisEmbedding i).contDiff

lemma planeAxisAt_hasFDerivAt (i : Fin 3) (a : ℝ) (y : Plane) :
    HasFDerivAt (planeAxisAt i a) (planeAxisEmbedding i) y := by
  exact (planeAxisEmbedding i).hasFDerivAt.const_add (a • EuclideanSpace.single i (1 : ℝ))

lemma tracePlanarField_admissible (i : Fin 3) (a : ℝ) {F : Cover → Cover}
    (hF : AdmissibleField F) : PlanarAdmissibleField (tracePlanarField i a F) := by
  refine ⟨(planeAxisProjection i).contDiff.comp (hF.1.comp (planeAxisAt_contDiff i a)),?_,?_⟩
  · intro n y
    have he : planeAxisAt i a (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=
        planeAxisAt i a y+latticeVector (i.insertNth (α := fun _ : Fin 3 ↦ ℤ) 0 n) := by
      ext k
      rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩ <;>
        simp [latticeVector,planeAxisAt,map_add,add_assoc]
    unfold tracePlanarField
    rw [he,hF.2.1]
  · intro y
    exact (planeAxisProjection_norm_le i _).trans (hF.2.2 _)

lemma planeDivergence_tracePlanarField (i : Fin 3) (a : ℝ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFi : ∀ x,F x i=0) (y : Plane) :
    planeDivergence (tracePlanarField i a F) y=divergence F (planeAxisAt i a y) := by
  have hd := (planeAxisProjection i).hasFDerivAt.comp y
    (((hF.differentiable (by simp) (planeAxisAt i a y)).hasFDerivAt).comp y
      (planeAxisAt_hasFDerivAt i a y))
  change HasFDerivAt (tracePlanarField i a F) _ y at hd
  have hz : (fderiv ℝ F (planeAxisAt i a y) (EuclideanSpace.single i 1)) i=0 := by
    rw [←fderiv_component (hF.differentiable (by simp) _) i]
    simp only [hFi]
    simp
  rw [planeDivergence,hd.fderiv,divergence,Fin.sum_univ_succAbove _ i,hz]
  simp [ContinuousLinearMap.comp_apply,Fin.sum_univ_two]

lemma planeAxisProjection_representative (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    planeAxisProjection i (representative ((torusAxialSplit i).symm (t,y)))=planarRepresentative y := by
  ext j
  simp [representative,planarRepresentative]

lemma representative_axialSplit (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    representative ((torusAxialSplit i).symm (t,y))=
      planeAxisAt i (((AddCircle.equivIco (1 : ℝ) 0) t) : ℝ) (planarRepresentative y) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩ <;>
    simp [representative,planarRepresentative]

theorem axialTestPerimeter_eq_planar (E : Set Torus) (i : Fin 3) (t : AxisCircle) :
    axialTestPerimeter E i t=planarTorusPerimeter (axialSlice E i t) := by
  apply le_antisymm
  · refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ?_
    let a : ℝ := ((AddCircle.equivIco (1 : ℝ) 0) t : ℝ)
    have hb : ENNReal.ofReal (∫ y in axialSlice E i t,
        planeDivergence (tracePlanarField i a F) (planarRepresentative y))≤
        planarTorusPerimeter (axialSlice E i t) :=
      le_iSup_of_le (tracePlanarField i a F)
        (le_iSup_of_le (tracePlanarField_admissible i a hF) le_rfl)
    apply le_trans _ hb
    apply le_of_eq
    congr 1
    unfold axialSliceIntegral
    apply integral_congr_ae
    filter_upwards [] with y
    rw [planeDivergence_tracePlanarField i a hF.1 hFi,representative_axialSplit]
  · refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
    have hb : ENNReal.ofReal (axialSliceIntegral E i
        (fun z ↦ divergence (liftPlanarField i G) (representative z)) t)≤axialTestPerimeter E i t :=
      le_iSup_of_le (liftPlanarField i G)
        (le_iSup_of_le (liftPlanarField_admissible i hG)
          (le_iSup_of_le (liftPlanarField_same i G) le_rfl))
    apply le_trans _ hb
    apply le_of_eq
    congr 1
    unfold axialSliceIntegral
    apply integral_congr_ae
    filter_upwards [] with y
    rw [divergence_liftPlanarField i hG.1,planeAxisProjection_representative]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaDensity
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

lemma axialSecondDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialSecondDensity μ i) := Measure.integrable_toReal_rnDeriv

lemma axialSurfaceMarginal_ac_of_area {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (axialSurfaceMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := ha hz
  change Measure.map _ _ s=0 at hh ⊢
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh ⊢
  exact withDensity_absolutelyContinuous _ _ hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSecondDensity_pairing_bounded {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Measurable f) :
    (∫ t,axialSecondDensity μ i t*f t)=
      ∫ z,(normalTransverseLength i z)^2*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  simp only [axialSecondDensity]
  rw [integral_toReal_rnDeriv_mul (axialSurfaceMarginal_ac_of_area i ha)]
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2)) :=
    (continuous_const.sub ((normal_component_continuous i).pow 2)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i)),smul_eq_mul]
  have hh := normalTransverseLength_sq i z
  congr 1
  linarith

lemma axial_density_local_comparison {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {S : Set AxisCircle} (hS : MeasurableSet S) {c : ℝ}
    (hc : ∀ᵐ z ∂(μ : Measure NormalBundle),(((z.1 : Cover) i) : AxisCircle)∈S →
      c*normalTransverseLength i z≤(normalTransverseLength i z)^2) :
    ∀ᵐ t,t∈S → c*axialPerimeterDensity μ i t≤axialSecondDensity μ i t := by
  have hh : (fun t ↦ c*axialPerimeterDensity μ i t)≤ᵐ[volume.restrict S]axialSecondDensity μ i := by
    apply ae_le_of_forall_setIntegral_le ((axialPerimeterDensity_integrable μ i).const_mul c).integrableOn
      (axialSecondDensity_integrable μ i).integrableOn
    intro T hT ht
    rw [Measure.restrict_restrict hT]
    let f : AxisCircle → ℝ := (T∩S).indicator (fun _ ↦ 1)
    have hf : Measurable f := measurable_const.indicator (hT.inter hS)
    have hfb (t : AxisCircle) : |f t|≤1 := by
      by_cases ht : t∈T∩S <;> simp [f,ht]
    have hp := axialPerimeterDensity_pairing_bounded i ha hf hfb
    have hq := axialSecondDensity_pairing_bounded i ha hf
    have he (g : AxisCircle → ℝ) : (fun t ↦ g t*f t)=(T∩S).indicator g := by
      funext t
      by_cases ht : t∈T∩S <;> simp [f,ht]
    rw [he,integral_indicator (hT.inter hS)] at hp hq
    rw [integral_const_mul,hp,hq,←integral_const_mul]
    have hfi : AEStronglyMeasurable (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
      (hf.comp (normal_axisCircle_continuous i).measurable).aestronglyMeasurable
    have hFint : Integrable (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
      Integrable.of_bound hfi 1 (ae_of_all _ fun z ↦ hfb _)
    have hbounded (g : NormalBundle → ℝ) (hg : Continuous g) :
        Integrable (fun z ↦ g z*f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) := by
      let G : C(NormalBundle,ℝ) := ⟨g,hg⟩
      exact hFint.bdd_mul hg.aestronglyMeasurable (ae_of_all _ fun z ↦ G.norm_coe_le_norm z)
    apply integral_mono_ae ((hbounded _ (normalTransverseLength_continuous i)).const_mul c)
      (hbounded _ ((normalTransverseLength_continuous i).pow 2))
    filter_upwards [hc] with z hz
    by_cases ht : (((z.1 : Cover) i) : AxisCircle)∈T∩S
    · simp only [f,indicator_of_mem ht,mul_one]
      exact hz ht.2
    · simp [f,ht]
  exact (ae_restrict_iff' hS).mp hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSliceIntegral_continuous_of_boundary_null {U : Set Torus} (hU : MeasurableSet U)
    (i : Fin 3) (hn : ∀ t : AxisCircle,volume (axialSlice (frontier U) i t)=0)
    {f : Torus → ℝ} (hf : Continuous f) : Continuous (axialSliceIntegral U i f) := by
  let g : C(Torus,ℝ) := ⟨f,hf⟩
  let C := ‖g‖
  have hC (z : Torus) : ‖f z‖ ≤ C := g.norm_coe_le_norm z
  rw [show axialSliceIntegral U i f=(fun t ↦ ∫ y,U.indicator f ((torusAxialSplit i).symm (t,y))) from
    funext (axialSliceIntegral_indicator hU i f)]
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_of_dominated (bound := fun _ ↦ max C 0)
  · apply Eventually.of_forall
    intro s
    exact (hf.measurable.indicator hU |>.comp ((torusAxialSplit i).symm.measurable.comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro s
    apply ae_of_all
    intro y
    exact (norm_indicator_le_norm_self _ _).trans ((hC _).trans (le_max_left _ _))
  · exact integrable_const _
  · have hnb : ∀ᵐ y : TransverseProduct,(torusAxialSplit i).symm (t,y)∉frontier U := by
      rw [ae_iff]
      simpa only [not_not,axialSlice] using hn t
    filter_upwards [hnb] with y hy
    exact ContinuousAt.comp (f := fun s ↦ (torusAxialSplit i).symm (s,y))
      (g := U.indicator f) (hf.continuousOn.continuousAt_indicator hy)
      (axialSlice_point_continuous i y).continuousAt

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_continuous_le_of_local_ae {f g : AxisCircle → ℝ}
    (hf : Continuous f) (hg : Continuous g) {S : Set AxisCircle} (hS : IsOpen S)
    {t : AxisCircle} (ht : t∈S) (ha : ∀ᵐ s,s∈S → f s≤g s) : f t≤g t := by
  by_contra! hbad
  let A : Set AxisCircle := S∩{s | g s<f s}
  have hAo : IsOpen A := hS.inter (isOpen_lt hg hf)
  have hpos := hAo.measure_pos volume ⟨t,ht,hbad⟩
  have hz : volume A=0 := by
    have hh : ∀ᵐ s : AxisCircle,s∉A := by
      filter_upwards [ha] with s hs
      intro hm
      exact (not_lt_of_ge (hs hm.1)) hm.2
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hh
  rw [hz] at hpos
  exact lt_irrefl _ hpos

theorem reflection_seam_planar_perimeter_le_flux {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {t : AxisCircle} (ht : -t=t) :
    planarTorusPerimeter (axialSlice (openRepresentative E) i t)≤
      ENNReal.ofReal (actualAxialFlux (openRepresentative E) μ H i t) := by
  let O := openRepresentative E
  have hO : MeasurableSet O := (isOpen_openRepresentative E).measurableSet
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμO := hμ.congr_ae hOE.symm
  have hHO : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux O D.coordinate D.function := by
    intro D
    rw [hH]
    congr 1
    exact directionalFlux_congr_ae hOE.symm D.coordinate D.function
  have hnull := isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha
  have hvc := axialSliceVolume_continuous_of_boundary_null hO i hnull
  have hfluxc : Continuous (actualAxialFlux O μ H i) :=
    continuous_const.add (continuous_const.mul (hvc.sub continuous_const))
  rw [←axialTestPerimeter_eq_planar]
  refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ENNReal.ofReal_le_ofReal ?_
  let I := axialSliceIntegral O i (fun z ↦ divergence F (representative z))
  have hd : Continuous (fun z : Torus ↦ divergence F (representative z)) :=
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  have hIc : Continuous I := axialSliceIntegral_continuous_of_boundary_null hO i hnull hd
  have hI := axialSliceIntegral_ae_le hO hμO i ha hF hFi
  have hq := axialSurface_density_eq_flux hO hHO i
  have hc (c : ℝ) (hc : c∈Ioo 0 1) : c*I t≤actualAxialFlux O μ H i t := by
    obtain ⟨S,hSo,htS,hSn⟩ := normal_transverse_near_reflection_height hV hE hmin i hR hμ hN hp hae ht hc
    have hs := axial_density_local_comparison i ha hSo.measurableSet hSn
    apply circle_continuous_le_of_local_ae (continuous_const.mul hIc) hfluxc hSo htS
    filter_upwards [hI,hs,hq] with s hIs hss hqs
    intro hsS
    calc
      c*I s ≤ c*axialPerimeterDensity μ i s := mul_le_mul_of_nonneg_left hIs hc.1.le
      _ ≤ axialSecondDensity μ i s := hss hsS
      _ = actualAxialFlux O μ H i s := hqs
  have hclosed : IsClosed {c : ℝ | c*I t≤actualAxialFlux O μ H i t} :=
    isClosed_le (continuous_id.mul continuous_const) continuous_const
  have hsub := closure_minimal (show Ioo (0 : ℝ) 1⊆{c : ℝ | c*I t≤actualAxialFlux O μ H i t} from hc) hclosed
  have hmem : (1 : ℝ)∈closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ)≠1)]
    norm_num
  simpa only [mem_ofPred_eq,one_mul] using hsub hmem

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisFixedHeights_neg_eq {t : AxisCircle} (ht : t∈axisFixedHeights) : -t=t := by
  rcases ht with rfl|ht
  · simp
  have he : t=((1/2 : ℝ) : AxisCircle) := by simpa only [mem_singleton_iff] using ht
  rw [he]
  apply neg_eq_iff_add_eq_zero.mpr
  rw [←AddCircle.coe_add]
  norm_num [AddCircle.coe_period]

theorem isMinimizerAt_missing_neighbor_seam_bound_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    planarTorusPerimeter (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))≤
      ENNReal.ofReal (H*(axialSliceVolume (openRepresentative E) i (octantHeight b i 0 : AxisCircle)).toReal) := by
  obtain ⟨N,hN,hp,hae,_⟩ := isMinimizerAt_stationary_tubular_normal hV hE hmin hμ hCMC
  have hH := Periodic.coordinateCMC_of_global hμ hCMC
  have hfix : -(octantHeight b i 0 : AxisCircle)=(octantHeight b i 0 : AxisCircle) := by
    unfold octantHeight
    cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · norm_num [AddCircle.coe_period]
    · exact axisFixedHeights_neg_eq (by simp [axisFixedHeights])
  have hh := reflection_seam_planar_perimeter_le_flux hV hE hmin i (hR i) hμ hH ha hN hp hae hfix
  have hf := isMinimizerAt_missing_neighbor_flux_unrestricted hV hE hmin hR b hd hμ hH i hv
  have hvol : torusVolume.real (openRepresentative E)=V := by
    rw [measureReal_def,measure_congr (isMinimizerAt_openRepresentative_ae hV hE hmin),
      hmin.2.1,ENNReal.toReal_ofReal hV.1.le]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [actualAxialFlux,hf,hvol]
  ring

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound_oai := @OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound_oai
