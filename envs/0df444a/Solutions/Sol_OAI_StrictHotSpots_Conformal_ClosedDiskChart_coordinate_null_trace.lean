-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:30:01.884359+00:00
-- url     : https://prove2.me/submissions/0956524c-0304-4d25-b658-f0e2c3ffc4bb

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_boundary_gradient_integral_zero
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_lipschitzMultipliedGradient_closed
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_lipschitzMultipliedGradient_nonneg
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_lipschitz_multiplier_kernel
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_operator_norm_lt_one
import Theorems.Thm_OAI_StrictHotSpots_H10_subcritical
import Theorems.Thm_OAI_StrictHotSpots_Hodge_vector_equality_interior_pointwise
import Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_full_embedding_coordinate_sum

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology




open MeasureTheory Filter
open scoped Topology ENNReal





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology
namespace StrictHotSpots

lemma eq_zero_of_inner_smoothTest_eq_zero {Ω : Set Plane} (hΩ : IsOpen Ω)
    (u : Lp ℝ 2 (volume.restrict Ω))
    (h : ∀ φ : smoothTestSpace Ω, inner ℝ (H1.value (smoothTestToH1 hΩ φ)) u = 0) :
    u = 0 := by
  have hl := (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hh := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict Ω) (hl.locallyIntegrableOn Ω)
    (fun φ hp hc hs => show (∫ x in Ω, φ x • u x) = 0 from by
      have ht := h ⟨φ,hp,hc,hs⟩
      have hv : H1.value (smoothTestToH1 hΩ ⟨φ,hp,hc,hs⟩) =
          (test_memLp (Ω := Ω) hp hc).toLp φ := rfl
      rw [hv, L2.inner_def] at ht
      convert ht using 1
      apply integral_congr_ae
      filter_upwards [(test_memLp (Ω := Ω) hp hc).coeFn_toLp] with x hx
      simp only [hx, smul_eq_mul, RCLike.inner_apply, conj_trivial]
      ring)
  apply Lp.ext
  filter_upwards [hh, ae_restrict_mem hΩ.measurableSet, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
    with x hx hΩx hz
  rw [hz]
  exact hx hΩx

end StrictHotSpots







open scoped InnerProductSpace


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace


open MeasureTheory
open scoped InnerProductSpace ENNReal


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Variational
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section H10InclusionCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots

lemma dense_smoothTestToH10 {Ω : Set Plane} (hΩ : IsOpen Ω) :
    DenseRange (smoothTestToH10 hΩ) := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hu : (u : H1 Ω) ∈ closure (Set.range (smoothTestToH1 hΩ)) := u.property
  obtain ⟨v,⟨f,rfl⟩,hv⟩ := Metric.mem_closure_iff.mp hu ε hε
  exact ⟨smoothTestToH10 hΩ f, ⟨f,rfl⟩, hv⟩

end StrictHotSpots
end H10InclusionCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryEnergy
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section BoundaryRRepresentationScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma fullBoundaryN_eq (s t : Boundary) : fullBoundaryN hC hν s t =
    boundaryInteraction s t + fullBoundaryR hC hν s t := by
  unfold fullBoundaryN fullBoundaryR firstInteraction secondInteraction tailInteraction
  ring

end StrictHotSpots.PlaneGreen
end BoundaryRRepresentationScalarSupportLayer

end
end LipschitzBoundaryScalarSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Potentials
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport

noncomputable section




section PlaneDifferentialInteriorSupportLayer

open Set MeasureTheory InnerProductSpace
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge

lemma expand (x : Plane) : c 0 x • e 0 + c 1 x • e 1 = x := by
  simpa only [Fin.sum_univ_two, OrthonormalBasis.repr_apply_apply, real_inner_comm] using planeBasis.sum_repr x
lemma basis_inner (i j : Fin 2) : inner ℝ (e i) (e j) = if i=j then 1 else 0 :=
  planeBasis.inner_eq_ite i j
lemma inner_two (x y : Plane) : inner ℝ x y = c 0 x*c 0 y+c 1 x*c 1 y := by
  simpa only [Fin.sum_univ_two,real_inner_comm (e 0) y,real_inner_comm (e 1) y] using
    (planeBasis.sum_inner_mul_inner x y).symm

lemma rot_apply (x : Plane) : rot x = c 0 x • e 1-c 1 x • e 0 := by
  simp only [rot,sub_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,real_inner_comm]
lemma c_rot (x : Plane) : c 0 (rot x) = -c 1 x ∧ c 1 (rot x) = c 0 x := by
  rw [rot_apply]
  simp only [c,inner_sub_left,inner_smul_left,conj_trivial,basis_inner]
  norm_num
lemma D_smooth {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 2) : ContDiff ℝ ∞ (D i φ) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const
lemma D_compact {φ : Plane → ℝ} (hc : HasCompactSupport φ) (i : Fin 2) : HasCompactSupport (D i φ) :=
  hc.fderiv_apply ℝ (e i)
lemma D_support (φ : Plane → ℝ) (i : Fin 2) : tsupport (D i φ) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset ℝ (e i)
lemma gradient_c (φ : Plane → ℝ) (i : Fin 2) (x : Plane) : c i (gradient φ x) = D i φ x :=
  inner_gradient_left
lemma D_D {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (i j : Fin 2) (x : Plane) :
    D i (D j φ) x = D j (D i φ) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ φ)).differentiable (by simp) x
  change fderiv ℝ (fun y => fderiv ℝ φ y (e j)) x (e i) =
    fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e j)
  rw [fderiv_clm_apply hd (differentiableAt_const _),fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) _ _

lemma inner_rot_gradient (Z : Plane) (φ : Plane → ℝ) (x : Plane) :
    inner ℝ Z (rot (gradient φ x)) = c 1 Z*D 0 φ x-c 0 Z*D 1 φ x := by
  rw [inner_two,(c_rot _).1,(c_rot _).2,gradient_c,gradient_c]
  ring
end StrictHotSpots.Hodge


end PlaneDifferentialInteriorSupportLayer



end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Hodge
attribute [-instance] _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section

section HodgeOrthogonalityInteriorSupportLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots
namespace Hodge

lemma weakCurl_gradient {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (hv : HasH1Gradient Ω v g) : WeakCurlZero Ω g := by
  intro φ hφ hk hs
  have h0 := hv.2.2 (D 0 φ) (D_smooth hφ 0) (D_compact hk 0) ((D_support φ 0).trans hs) (e 1)
  have h1 := hv.2.2 (D 1 φ) (D_smooth hφ 1) (D_compact hk 1) ((D_support φ 1).trans hs) (e 0)
  change (∫ x in Ω, v x * D 1 (D 0 φ) x) = -(∫ x in Ω, c 1 (g x)*D 0 φ x) at h0
  change (∫ x in Ω, v x * D 0 (D 1 φ) x) = -(∫ x in Ω, c 0 (g x)*D 1 φ x) at h1
  simp_rw [D_D hφ 1 0] at h0
  have hi := (hv.2.1.inner_const (e 1)).integrable_mul (test_derivative_memLp hφ hk (e 0))
  have hj := (hv.2.1.inner_const (e 0)).integrable_mul (test_derivative_memLp hφ hk (e 1))
  change IntegrableOn (fun x => c 1 (g x)*D 0 φ x) Ω at hi
  change IntegrableOn (fun x => c 0 (g x)*D 1 φ x) Ω at hj
  simp_rw [inner_rot_gradient]
  rw [integral_sub hi hj]
  linarith

lemma rotL_ae {Ω : Set Plane} (u : V2 Ω) : rotL Ω u =ᵐ[volume.restrict Ω] fun x => rot (u x) :=
  rot.coeFn_compLpL u

lemma weakCurl_iff {Ω : Set Plane} (ho : IsOpen Ω) (Z : V2 Ω) :
    WeakCurlZero Ω Z ↔ ∀ j : H10 ho, inner ℝ Z (rotL Ω (H10.grad ho j)) = 0 := by
  constructor
  · intro hz j
    apply isClosed_property (dense_smoothTestToH10 ho)
      (isClosed_eq (continuous_const.inner ((rotL Ω).continuous.comp (H10.grad ho).continuous)) continuous_const) _ j
    intro f
    rw [L2.inner_def]
    have he : H10.grad ho (smoothTestToH10 ho f) =ᵐ[volume.restrict Ω] gradient f.val :=
      (test_gradient_memLp f.property.1 f.property.2.1).coeFn_toLp
    calc
      _ = ∫ x in Ω, inner ℝ (Z x) (rot (gradient f.val x)) := by
        apply integral_congr_ae
        filter_upwards [rotL_ae (H10.grad ho (smoothTestToH10 ho f)),he] with x hx hy
        change inner ℝ (Z x) ((rotL Ω (H10.grad ho (smoothTestToH10 ho f))) x) = _
        rw [hx,hy]
      _ = 0 := hz f.val f.property.1 f.property.2.1 f.property.2.2
  · intro hz φ hφ hk hs
    let f : smoothTestSpace Ω := ⟨φ,hφ,hk,hs⟩
    have h := hz (smoothTestToH10 ho f)
    rw [L2.inner_def] at h
    have he : H10.grad ho (smoothTestToH10 ho f) =ᵐ[volume.restrict Ω] gradient φ :=
      (test_gradient_memLp hφ hk).coeFn_toLp
    convert h using 1
    apply integral_congr_ae
    filter_upwards [rotL_ae (H10.grad ho (smoothTestToH10 ho f)),he] with x hx hy
    rw [hx,hy]

lemma grad_rotGrad_orthogonal {Ω : Set Plane} (ho : IsOpen Ω) (v : H1 Ω) (j : H10 ho) :
    inner ℝ (H1.grad v) (rotL Ω (H10.grad ho j)) = 0 :=
  (weakCurl_iff ho (H1.grad v)).mp (weakCurl_gradient (H1.hasH1Gradient v)) j

end Hodge
end StrictHotSpots

end HodgeOrthogonalityInteriorSupportLayer


end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section

section VectorSobolevActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


lemma coordinateL_ae (i : Fin 2) (v : V2 Ω) :
    coordinateL Ω i v =ᵐ[volume.restrict Ω] fun x => c i (v x) := by
  filter_upwards [(innerSL ℝ (e i)).coeFn_compLpL v] with x hx
  apply hx.trans
  change inner ℝ (e i) (v x) = inner ℝ (v x) (e i)
  exact real_inner_comm _ _


lemma axisL_ae (i : Fin 2) (u : Lp ℝ 2 (volume.restrict Ω)) :
    axisL Ω i u =ᵐ[volume.restrict Ω] fun x => u x • e i :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)).coeFn_compLpL u

lemma scalar_pair_L2 (u v : Lp ℝ 2 (volume.restrict Ω)) :
    inner ℝ u v = ∫ x in Ω, u x*v x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [RCLike.inner_apply,RCLike.conj_to_real]
    exact mul_comm _ _

lemma partialL_compact_integration_by_parts (ho : IsOpen Ω) (i : Fin 2)
    (u : H1 Ω) (φ : smoothTestSpace Ω) :
    inner ℝ (H1.value u) (partialL i (smoothTestToH10 ho φ).val) =
      -inner ℝ (partialL i u) (H10.value ho (smoothTestToH10 ho φ)) := by
  have hv : H10.value ho (smoothTestToH10 ho φ) =ᵐ[volume.restrict Ω] φ.val :=
    (test_memLp φ.property.1 φ.property.2.1).coeFn_toLp
  have hg : H10.grad ho (smoothTestToH10 ho φ) =ᵐ[volume.restrict Ω] gradient φ.val :=
    (test_gradient_memLp φ.property.1 φ.property.2.1).coeFn_toLp
  rw [scalar_pair_L2,scalar_pair_L2]
  have hl : (∫ x in Ω, H1.value u x*partialL i (smoothTestToH10 ho φ).val x) =
      ∫ x in Ω, H1.value u x*(fderiv ℝ φ.val x) (e i) := by
    apply integral_congr_ae
    filter_upwards [coordinateL_ae i (H10.grad ho (smoothTestToH10 ho φ)),hg] with x hx hy
    exact congrArg (fun a : ℝ => H1.value u x*a)
      (hx.trans ((congrArg (c i) hy).trans (gradient_c _ _ _)))
  have hr : (∫ x in Ω, partialL i u x*H10.value ho (smoothTestToH10 ho φ) x) =
      ∫ x in Ω, inner ℝ (H1.grad u x) (e i)*φ.val x := by
    apply integral_congr_ae
    filter_upwards [coordinateL_ae i (H1.grad u),hv] with x hx hy
    exact congrArg₂ (fun a b : ℝ => a*b) hx hy
  exact hl.trans (((H1.hasH1Gradient u).2.2 φ.val φ.property.1 φ.property.2.1
    φ.property.2.2 (e i)).trans (congrArg Neg.neg hr).symm)



lemma partialL_integration_by_parts (ho : IsOpen Ω) (i : Fin 2) (u : H1 Ω) (v : H10 ho) :
    inner ℝ (H1.value u) (partialL i v.val) =
      -inner ℝ (partialL i u) (H10.value ho v) := by
  apply isClosed_property (dense_smoothTestToH10 ho) _ _ v
  · exact isClosed_eq
      (continuous_const.inner ((coordinateL Ω i).continuous.comp (H10.grad ho).continuous))
      ((continuous_const.inner (H10.value ho).continuous).neg)
  · exact partialL_compact_integration_by_parts ho i u

lemma axis_coordinate_pair (i : Fin 2) (u : Lp ℝ 2 (volume.restrict Ω)) (v : V2 Ω) :
    inner ℝ (axisL Ω i u) v = inner ℝ u (coordinateL Ω i v) := by
  rw [L2.inner_def,scalar_pair_L2]
  apply integral_congr_ae
  filter_upwards [axisL_ae i u,coordinateL_ae i v] with x hx hy
  rw [hx,hy,real_inner_smul_left]
  exact congrArg (fun t : ℝ => u x*t) (real_inner_comm _ _)

lemma coordinateL_rot_zero (v : V2 Ω) :
    coordinateL Ω 0 (rotL Ω v) = -coordinateL Ω 1 v := by
  apply Lp.ext
  filter_upwards [coordinateL_ae 0 (rotL Ω v),rotL_ae v,
    coordinateL_ae 1 v,Lp.coeFn_neg (coordinateL Ω 1 v)] with x h0 hr h1 hn
  rw [h0,hr,hn,Pi.neg_apply,h1,(c_rot _).1]

lemma coordinateL_rot_one (v : V2 Ω) :
    coordinateL Ω 1 (rotL Ω v) = coordinateL Ω 0 v := by
  apply Lp.ext
  filter_upwards [coordinateL_ae 1 (rotL Ω v),rotL_ae v,
    coordinateL_ae 0 v] with x h0 hr h1
  rw [h0,hr,h1,(c_rot _).2]

lemma axis_sum_pair (a b : Lp ℝ 2 (volume.restrict Ω)) (v : V2 Ω) :
    inner ℝ (axisL Ω 0 a+axisL Ω 1 b) v =
      inner ℝ a (coordinateL Ω 0 v)+inner ℝ b (coordinateL Ω 1 v) := by
  rw [inner_add_left,axis_coordinate_pair,axis_coordinate_pair]

lemma axis_sum_rot_pair (a b : Lp ℝ 2 (volume.restrict Ω)) (v : V2 Ω) :
    inner ℝ (axisL Ω 0 a+axisL Ω 1 b) (rotL Ω v) =
      -inner ℝ a (coordinateL Ω 1 v)+inner ℝ b (coordinateL Ω 0 v) := by
  rw [axis_sum_pair,coordinateL_rot_zero,coordinateL_rot_one,inner_neg_right]

lemma partialL_test_curl (ho : IsOpen Ω) (X : Fin 2 → H1 Ω) (v : H10 ho) :
    inner ℝ (vectorValue X) (rotL Ω (H10.grad ho v)) =
      -inner ℝ (curlL X) (H10.value ho v) := by
  calc
    _ = -inner ℝ (H1.value (X 0)) (partialL 1 v.val)+
        inner ℝ (H1.value (X 1)) (partialL 0 v.val) := axis_sum_rot_pair _ _ _
    _ = -(-inner ℝ (partialL 1 (X 0)) (H10.value ho v))+
        (-inner ℝ (partialL 0 (X 1)) (H10.value ho v)) :=
      congrArg₂ (fun a b : ℝ => -a+b) (partialL_integration_by_parts ho 1 (X 0) v)
        (partialL_integration_by_parts ho 0 (X 1) v)
    _ = _ := by simp only [curlL,inner_sub_left]; ring

lemma vectorValue_zero_trace_normal (ho : IsOpen Ω) (X : Fin 2 → H10 ho) (u : H1 Ω) :
    inner ℝ (vectorValue (fun i => (X i).val)) (H1.grad u) =
      -inner ℝ (divergenceL (fun i => (X i).val)) (H1.value u) := by
  have h0 : inner ℝ (H1.value (X 0).val) (partialL 0 u) =
      -inner ℝ (partialL 0 (X 0).val) (H1.value u) := by
    have hh := partialL_integration_by_parts ho 0 u (X 0)
    change inner ℝ (H1.value u) (partialL 0 (X 0).val) =
      -inner ℝ (partialL 0 u) (H1.value (X 0).val) at hh
    linarith only [hh,real_inner_comm (H1.value u) (partialL 0 (X 0).val),
      real_inner_comm (H1.value (X 0).val) (partialL 0 u)]
  have h1 : inner ℝ (H1.value (X 1).val) (partialL 1 u) =
      -inner ℝ (partialL 1 (X 1).val) (H1.value u) := by
    have hh := partialL_integration_by_parts ho 1 u (X 1)
    change inner ℝ (H1.value u) (partialL 1 (X 1).val) =
      -inner ℝ (partialL 1 u) (H1.value (X 1).val) at hh
    linarith only [hh,real_inner_comm (H1.value u) (partialL 1 (X 1).val),
      real_inner_comm (H1.value (X 1).val) (partialL 1 u)]
  calc
    _ = inner ℝ (H1.value (X 0).val) (partialL 0 u)+
        inner ℝ (H1.value (X 1).val) (partialL 1 u) := axis_sum_pair _ _ _
    _ = -inner ℝ (partialL 0 (X 0).val) (H1.value u)+
        -inner ℝ (partialL 1 (X 1).val) (H1.value u) := congrArg₂ (·+·) h0 h1
    _ = _ := by simp only [divergenceL,inner_add_left,neg_add_rev]; ring
end StrictHotSpots.Hodge
end VectorSobolevActualCompatibleLayer

section VectorDefectEnergyActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}

lemma axis_sum_ae (a b : Lp ℝ 2 (volume.restrict Ω)) :
    axisL Ω 0 a+axisL Ω 1 b =ᵐ[volume.restrict Ω] fun x => a x • e 0+b x • e 1 := by
  filter_upwards [axisL_ae 0 a,axisL_ae 1 b,Lp.coeFn_add (axisL Ω 0 a) (axisL Ω 1 b)]
    with x ha hb hs
  exact hs.trans (congrArg₂ (fun u v : Plane => u+v) ha hb)

end StrictHotSpots.Hodge
end VectorDefectEnergyActualCompatibleLayer

section TangentVectorClassActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


lemma vectorValue_add (X Y : Fin 2 → H1 Ω) :
    vectorValue (X+Y)=vectorValue X+vectorValue Y := by
  simp only [vectorValue,Pi.add_apply,map_add]
  abel
lemma partialL_add (i : Fin 2) (u v : H1 Ω) : partialL i (u+v)=partialL i u+partialL i v := by
  simp only [partialL,map_add]
lemma divergenceL_add (X Y : Fin 2 → H1 Ω) :
    divergenceL (X+Y)=divergenceL X+divergenceL Y := by
  simp only [divergenceL,Pi.add_apply,partialL_add]
  abel

lemma TangentWeak.add {X Y : Fin 2 → H1 Ω} (hX : TangentWeak X) (hY : TangentWeak Y) :
    TangentWeak (X+Y) := by
  intro u
  rw [vectorValue_add,divergenceL_add,inner_add_left,inner_add_left,hX u,hY u]
  ring
lemma tangentWeak_zero_trace (ho : IsOpen Ω) (X : Fin 2 → H10 ho) :
    TangentWeak (fun i => (X i).val) := vectorValue_zero_trace_normal ho X


lemma TangentWeak.of_class (ho : IsOpen Ω) {X Y : Fin 2 → H1 Ω}
    (hY : TangentWeak Y) (hXY : ∀ i, ∃ w : H10 ho, X i-Y i=w.val) : TangentWeak X := by
  choose w hw using hXY
  have he : X=Y+fun i => (w i).val := by
    funext i
    exact (sub_eq_iff_eq_add.mp (hw i)).trans (add_comm _ _)
  rw [he]
  exact hY.add (tangentWeak_zero_trace ho w)

end StrictHotSpots.Hodge
end TangentVectorClassActualCompatibleLayer

section NormalMultiplierActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff ENNReal
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}

lemma divergenceL_ae (X : Fin 2 → H1 Ω) : divergenceL X =ᵐ[volume.restrict Ω]
    fun x => c 0 (H1.grad (X 0) x)+c 1 (H1.grad (X 1) x) := by
  filter_upwards [coordinateL_ae 0 (H1.grad (X 0)),coordinateL_ae 1 (H1.grad (X 1)),
    Lp.coeFn_add (partialL 0 (X 0)) (partialL 1 (X 1))] with x h0 h1 ha
  exact ha.trans (congrArg₂ (fun a b : ℝ => a+b) h0 h1)
lemma vectorValue_ae (X : Fin 2 → H1 Ω) : vectorValue X =ᵐ[volume.restrict Ω]
    fun x => H1.value (X 0) x • e 0+H1.value (X 1) x • e 1 := axis_sum_ae _ _

lemma divergence_multiplier_algebra (b u v : ℝ) (A B C : Plane) :
    c 0 (b • A+u • C)+c 1 (b • B+v • C) =
      b*(c 0 A+c 1 B)+inner ℝ (u • e 0+v • e 1) C := by
  have h0 : inner ℝ (e 0) C = inner ℝ C (e 0) := real_inner_comm _ _
  have h1 : inner ℝ (e 1) C = inner ℝ C (e 1) := real_inner_comm _ _
  simp only [c,inner_add_left,real_inner_smul_left,h0,h1]
  ring

variable {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω))
    (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))

lemma normal_pair_integral (X : Fin 2 → H1 Ω) (u : H1 Ω) :
    inner ℝ (vectorValue X) (H1.grad u)+inner ℝ (divergenceL X) (H1.value u) =
      ∫ x in Ω, inner ℝ (vectorValue X x) (H1.grad u x)+divergenceL X x*H1.value u x := by
  have hi := integrable_inner_of_memLp (Lp.memLp (vectorValue X)) (Lp.memLp (H1.grad u))
  have hj := (Lp.memLp (divergenceL X)).integrable_mul (Lp.memLp (H1.value u))
  exact (congrArg₂ (fun a b : ℝ => a+b) (L2.inner_def _ _) (scalar_pair_L2 _ _)).trans
    (integral_add hi hj).symm

lemma normal_multiplier_algebra (b u F : ℝ) (V G C : Plane) :
    inner ℝ (b • V) G+(b*F+inner ℝ V C)*u =
      inner ℝ V (b • G+u • C)+F*(b*u) := by
  simp only [real_inner_smul_left,inner_add_right,real_inner_smul_right]
  ring

end StrictHotSpots.Hodge
end NormalMultiplierActualCompatibleLayer

section GradientVectorEnergyActualCompatibleLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal Topology
namespace StrictHotSpots
namespace Hodge
variable {Ω : Set Plane}

lemma scalar_eq_zero_of_H10_pair (ho : IsOpen Ω) (f : Lp ℝ 2 (volume.restrict Ω))
    (h : ∀ v : H10 ho, inner ℝ f (H10.value ho v)=0) : f=0 := by
  apply eq_zero_of_inner_smoothTest_eq_zero ho f
  intro φ
  exact (real_inner_comm _ _).trans (h (smoothTestToH10 ho φ))

lemma vectorValue_test_normal (ho : IsOpen Ω) (X : Fin 2 → H1 Ω) (v : H10 ho) :
    inner ℝ (vectorValue X) (H10.grad ho v) =
      -inner ℝ (divergenceL X) (H10.value ho v) := by
  calc
    _ = inner ℝ (H1.value (X 0)) (partialL 0 v.val)+
        inner ℝ (H1.value (X 1)) (partialL 1 v.val) := axis_sum_pair _ _ _
    _ = -inner ℝ (partialL 0 (X 0)) (H10.value ho v)+
        -inner ℝ (partialL 1 (X 1)) (H10.value ho v) :=
      congrArg₂ (·+·) (partialL_integration_by_parts ho 0 (X 0) v)
        (partialL_integration_by_parts ho 1 (X 1) v)
    _ = _ := by simp only [divergenceL,inner_add_left,neg_add_rev]; ring

lemma gradient_curl_zero (ho : IsOpen Ω) (X : Fin 2 → H1 Ω) (u : H1 Ω)
    (hX : vectorValue X=H1.grad u) : curlL X=0 := by
  apply scalar_eq_zero_of_H10_pair ho
  intro v
  have hh := partialL_test_curl ho X v
  have hz := grad_rotGrad_orthogonal ho u v
  rw [hX] at hh
  linarith only [hh,hz]


lemma inner_add_smul_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) (μ t : ℝ) (ha : t = -inner ℝ a c) (hb : t = μ*inner ℝ b c) :
    inner ℝ (a+μ • b) c=0 := by
  rw [inner_add_left, real_inner_smul_left]
  linarith only [ha,hb]

lemma gradient_divergence (ho : IsOpen Ω) (μ : ℝ) (X : Fin 2 → H1 Ω) (u : H1 Ω)
    (hX : vectorValue X=H1.grad u) (hu : NeumannEuler μ u) :
    divergenceL X=(-μ) • H1.value u := by
  have hz : divergenceL X+μ • H1.value u=0 := by
    apply scalar_eq_zero_of_H10_pair ho
    intro v
    have hh := vectorValue_test_normal ho X v
    have he := hu v.val
    rw [hX] at hh
    change inner ℝ (H1.grad u) (H10.grad ho v)=
      μ*inner ℝ (H1.value u) (H10.value ho v) at he
    exact inner_add_smul_zero (divergenceL X) (H1.value u) (H10.value ho v) μ
      (inner ℝ (H1.grad u) (H10.grad ho v)) hh he
  exact (eq_neg_of_add_eq_zero_left hz).trans (neg_smul μ (H1.value u)).symm

lemma gradient_tangent (ho : IsOpen Ω) (μ : ℝ) (X : Fin 2 → H1 Ω) (u : H1 Ω)
    (hX : vectorValue X=H1.grad u) (hu : NeumannEuler μ u) : TangentWeak X := by
  have hd := gradient_divergence ho μ X u hX hu
  intro w
  rw [hX,hd,real_inner_smul_left,hu w]
  ring

lemma gradient_form_algebra {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (μ : ℝ) (g : E) (v : F) (he : inner ℝ g g=μ*inner ℝ v v) :
    inner ℝ ((-μ) • v) ((-μ) • v)+inner ℝ (0:F) (0:F)-μ*inner ℝ g g=0 := by
  simp only [real_inner_smul_left,real_inner_smul_right,inner_zero_left,he]
  ring



theorem gradient_vector_null (ho : IsOpen Ω) (μ : ℝ) (X : Fin 2 → H1 Ω) (u : H1 Ω)
    (hX : vectorValue X=H1.grad u) (hu : NeumannEuler μ u) :
    TangentWeak X ∧ vectorForm μ X X=0 := by
  refine ⟨gradient_tangent ho μ X u hX hu,?_⟩
  have hd := gradient_divergence ho μ X u hX hu
  have hc := gradient_curl_zero ho X u hX
  unfold vectorForm
  rw [hd,hc,hX]
  exact gradient_form_algebra μ (H1.grad u) (H1.value u) (hu u)
end Hodge
end StrictHotSpots
end GradientVectorEnergyActualCompatibleLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots
namespace Hodge
variable {Ω : Set Plane} {u : Plane → ℝ}




lemma eigenGradientField_value_ae (hΩ : AdmissibleDomain Ω)
    (hu : InFirstNeumannEigenspace Ω u) (i : Fin 2) :
    H1.value (eigenGradientField hΩ hu i) =ᵐ[volume.restrict Ω]
      fun x => fderivWithin ℝ u (closure Ω) x (e i) :=
  (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2
    (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (e i))).1.coeFn_toLp

lemma eigenGradientField_vector (hΩ : AdmissibleDomain Ω)
    (hu : InFirstNeumannEigenspace Ω u) :
    vectorValue (eigenGradientField hΩ hu)=H1.grad hu.2.1.toH1 := by
  apply Lp.ext
  filter_upwards [axis_sum_ae (H1.value (eigenGradientField hΩ hu 0))
    (H1.value (eigenGradientField hΩ hu 1)),eigenGradientField_value_ae hΩ hu 0,
    eigenGradientField_value_ae hΩ hu 1,hu.2.1.2.1.coeFn_toLp,
    ae_restrict_mem hΩ.2.1.measurableSet] with x hv h0 h1 hg hx
  change (vectorValue (eigenGradientField hΩ hu)) x = _ at hv
  change (H1.grad hu.2.1.toH1) x = gradient u x at hg
  have he (i : Fin 2) : fderivWithin ℝ u (closure Ω) x (e i)=c i (gradient u x) := by
    rw [fderivWithin_of_mem_nhds (mem_of_superset (hΩ.2.1.mem_nhds hx) subset_closure)]
    exact (gradient_c u i x).symm
  exact hv.trans ((congrArg₂ (fun a b : ℝ => a • e 0+b • e 1)
    (h0.trans (he 0)) (h1.trans (he 1))).trans ((expand _).trans hg.symm))

lemma eigen_NeumannEuler (hu : InFirstNeumannEigenspace Ω u) :
    NeumannEuler (firstPositiveNeumannValue Ω) hu.2.1.toH1 := by
  intro w
  have hl : inner ℝ (H1.grad hu.2.1.toH1) (H1.grad w) =
      ∫ x in Ω, inner ℝ (gradient u x) (H1.grad w x) := by
    refine (L2.inner_def _ _).trans (integral_congr_ae ?_)
    filter_upwards [hu.2.1.2.1.coeFn_toLp] with x hx
    exact congrArg (fun v : Plane => inner ℝ v (H1.grad w x)) hx
  have hr : inner ℝ (H1.value hu.2.1.toH1) (H1.value w) =
      ∫ x in Ω, u x*H1.value w x := by
    refine (scalar_pair_L2 _ _).trans (integral_congr_ae ?_)
    filter_upwards [hu.2.1.1.coeFn_toLp] with x hx
    exact congrArg (fun v : ℝ => v*H1.value w x) hx
  exact hl.trans ((hu.2.2.2 _ _ (H1.hasH1Gradient w)).trans
    (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t) hr).symm)




theorem eigenGradientField_null (hΩ : AdmissibleDomain Ω)
    (hu : InFirstNeumannEigenspace Ω u) :
    TangentWeak (eigenGradientField hΩ hu) ∧
      vectorForm (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu)
        (eigenGradientField hΩ hu)=0 :=
  gradient_vector_null hΩ.2.1 (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu)
    hu.2.1.toH1 (eigenGradientField_vector hΩ hu) (eigen_NeumannEuler hu)
end Hodge
end StrictHotSpots
end
end ActualVectorSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzH1

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots


namespace H1
variable {Ω : Set Plane} (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b)

lemma lipschitzMul_value_ae (u : H1 Ω) : H1.value (lipschitzMul ho hΩ hb u) =ᵐ[volume.restrict Ω]
    fun x => b x*H1.value u x :=
  ((H1.hasH1Gradient u).mul_lipschitz ho hΩ hb).1.coeFn_toLp

lemma lipschitzMul_grad_ae (u : H1 Ω) : H1.grad (lipschitzMul ho hΩ hb u) =ᵐ[volume.restrict Ω]
    fun x => b x • H1.grad u x+H1.value u x • gradient b x :=
  ((H1.hasH1Gradient u).mul_lipschitz ho hΩ hb).2.1.coeFn_toLp
end H1

end StrictHotSpots
end
end LipschitzH1

section PhysicalHelmholtz

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PhysicalHelmholtz
variable {Ω : Set Plane} (ho : IsOpen Ω)

attribute [local instance] OAI.StrictHotSpots.PhysicalHelmholtz.instNormedAddCommGroupSubtypeH1AmbientMemSubmoduleRealH1H10
lemma extension_class (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) (a : H1 Ω) :
    ∃ w : H10 ho, extension ho hb hμ hl hD a-a=w.val := by
  exact ⟨correction ho hb hμ hl hD a,add_sub_cancel_left _ _⟩

end StrictHotSpots.PhysicalHelmholtz
end
end PhysicalHelmholtz

section LipschitzVectorMultiplier

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane} (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
variable {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b)

lemma vectorValue_lipschitzMul_ae (X : Fin 2 → H1 Ω) :
    vectorValue (fun i => H1.lipschitzMul ho hbound hb (X i)) =ᵐ[volume.restrict Ω]
      fun x => b x • vectorValue X x := by
  let M := H1.lipschitzMul ho hbound hb
  filter_upwards [vectorValue_ae (fun i => M (X i)),vectorValue_ae X,
    H1.lipschitzMul_value_ae ho hbound hb (X 0),H1.lipschitzMul_value_ae ho hbound hb (X 1)]
      with x hV hX h0 h1
  apply hV.trans
  exact (congrArg₂ (fun a d : ℝ => a • e 0+d • e 1) h0 h1).trans
    (by rw [hX]; module)

lemma divergenceL_lipschitzMul_ae (X : Fin 2 → H1 Ω) :
    divergenceL (fun i => H1.lipschitzMul ho hbound hb (X i)) =ᵐ[volume.restrict Ω]
      fun x => b x*divergenceL X x+inner ℝ (vectorValue X x) (gradient b x) := by
  let M := H1.lipschitzMul ho hbound hb
  filter_upwards [divergenceL_ae (fun i => M (X i)),divergenceL_ae X,vectorValue_ae X,
    H1.lipschitzMul_grad_ae ho hbound hb (X 0),H1.lipschitzMul_grad_ae ho hbound hb (X 1)]
      with x hD hX hV h0 h1
  apply hD.trans
  exact (congrArg₂ (fun A B : Plane => c 0 A+c 1 B) h0 h1).trans
    ((divergence_multiplier_algebra _ _ _ _ _ _).trans
      (congrArg₂ (fun d : ℝ => fun V : Plane => b x*d+inner ℝ V (gradient b x)) hX hV).symm)


lemma normal_pair_lipschitzMul (X : Fin 2 → H1 Ω) (u : H1 Ω) :
    inner ℝ (vectorValue (fun i => H1.lipschitzMul ho hbound hb (X i))) (H1.grad u)+
      inner ℝ (divergenceL (fun i => H1.lipschitzMul ho hbound hb (X i))) (H1.value u) =
    inner ℝ (vectorValue X) (H1.grad (H1.lipschitzMul ho hbound hb u))+
      inner ℝ (divergenceL X) (H1.value (H1.lipschitzMul ho hbound hb u)) := by
  refine Eq.trans (normal_pair_integral _ _) (Eq.trans ?_ (normal_pair_integral _ _).symm)
  apply integral_congr_ae
  filter_upwards [vectorValue_lipschitzMul_ae ho hbound hb X,divergenceL_lipschitzMul_ae ho hbound hb X,
    H1.lipschitzMul_grad_ae ho hbound hb u,H1.lipschitzMul_value_ae ho hbound hb u] with x hV hD hG hu
  exact (congrArg₂ (fun V : Plane => fun F : ℝ =>
    inner ℝ V (H1.grad u x)+F*H1.value u x) hV hD).trans
      ((normal_multiplier_algebra _ _ _ _ _ _).trans
        (congrArg₂ (fun G : Plane => fun v : ℝ => inner ℝ (vectorValue X x) G+divergenceL X x*v) hG hu).symm)


theorem TangentWeak.lipschitzMul {X : Fin 2 → H1 Ω} (hX : TangentWeak X) :
    TangentWeak (fun i => H1.lipschitzMul ho hbound hb (X i)) := by
  intro u
  have he := normal_pair_lipschitzMul ho hbound hb X u
  have hz := hX (H1.lipschitzMul ho hbound hb u)
  linarith only [he,hz]


end StrictHotSpots.Hodge
end
end LipschitzVectorMultiplier

section PhysicalMultiplierLimit

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

lemma lipschitzMultipliedGradient_class {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) (i : Fin 2) :
    ∃ w : H10 hΩ.2.1, lipschitzMultipliedGradient hΩ hμ hl hD hu hb i-
      H1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (eigenGradientField hΩ hu i)=w.val :=
  PhysicalHelmholtz.extension_class hΩ.2.1 hΩ.2.2.1 hμ.le hl hD _

lemma lipschitzMultipliedGradient_tangent {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) :
    TangentWeak (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) :=
  TangentWeak.of_class hΩ.2.1 ((eigenGradientField_null hΩ hu).1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb)
    (lipschitzMultipliedGradient_class hΩ hμ hl hD hu hb)

end StrictHotSpots.Conformal.ClosedDiskChart

end
end PhysicalMultiplierLimit

section LipschitzMultiplierKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

include hΩ hu in
lemma closedGradient_trace_continuous :
    Continuous (fun s : Boundary => closedGradient Ω u (c.F s)) := by
  apply (closedGradient_continuous hΩ.2.1 hΩ.2.2.2.2 hu.1).comp_continuous
    (c.lipschitz.continuous.comp continuous_subtype_val)
  intro s
  exact c.maps_closed (boundary_mem_closed s)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end LipschitzMultiplierKernel

section HilbertMultiplierSum

noncomputable section
open Set MeasureTheory Metric Function
open scoped InnerProductSpace Topology
namespace StrictHotSpots.HilbertMultipliers

lemma nonnegative_coordinate_energy_zero {ι : Type*} {E : ι → ℝ}
    (hs : HasSum E 0) (hE : ∀ i, 0 ≤ E i) (i : ι) : E i = 0 := by
  apply le_antisymm _ (hE i)
  simpa only [hs.tsum_eq] using hs.summable.le_tsum i (fun j _ => hE j)

end StrictHotSpots.HilbertMultipliers
end
end HilbertMultiplierSum


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedSolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section BoundaryCoordinateExtension

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped NNReal Topology InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



theorem boundary_scalar_extension {f : Boundary → ℝ} {B : ℝ≥0} (hf : LipschitzWith B f) :
    ∃ (g : Plane → ℝ) (A : ℝ≥0), LipschitzWith A g ∧ ∀ s : Boundary, g (c.F s) = f s := by
  classical
  let f' (x : Plane) := if h : ‖x‖ = 1 then f ⟨x,h⟩ else 0
  have hl : LipschitzOnWith B f' {x : Plane | ‖x‖ = 1} := by
    intro x hx y hy
    change ‖x‖ = 1 at hx
    change ‖y‖ = 1 at hy
    simpa only [f',dite_eq_left hx,dite_eq_left hy,Subtype.edist_eq] using hf ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,he⟩ := hl.extend_real
  refine ⟨g ∘ c.G,B*c.InvLip,hg.comp c.inverse_lipschitz,?_⟩
  intro s
  change g (c.G (c.F s)) = f s
  rw [c.left_inverse s (c.source_eq.symm ▸ (by simp only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_closedBall_zero_iff,s.property,le_refl]))]
  exact (he s.property).symm.trans (by simp only [f',dite_eq_left s.property])
end StrictHotSpots.Conformal.ClosedDiskChart
namespace StrictHotSpots.HilbertMultipliers
lemma coordinate_lipschitz {H S ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [PseudoMetricSpace S] (e : HilbertBasis ι ℝ H) {b : S → H} {B : ℝ≥0}
    (hb : LipschitzWith B b) (i : ι) : LipschitzWith B (fun s => inner ℝ (e i) (b s)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,← inner_sub_right]
  calc
    |inner ℝ (e i) (b s-b t)| ≤ ‖e i‖*‖b s-b t‖ := abs_real_inner_le_norm _ _
    _ = ‖b s-b t‖ := by rw [e.orthonormal.1 i,one_mul]
    _ ≤ B*dist s t := by simpa only [dist_eq_norm] using hb.dist_le_mul s t
end StrictHotSpots.HilbertMultipliers
end
end BoundaryCoordinateExtension


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Eigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedNullGradient

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

include c




theorem lipschitzMultipliedGradient_null {u : Plane → ℝ}
    (hu : InFirstNeumannEigenspace Ω u) {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b)
    (hz : vectorForm (firstPositiveNeumannValue Ω)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) = 0) :
    ∃ (v : Plane → ℝ) (Y : Plane → Plane), InInteriorNeumannEigenspace Ω v ∧
      ContinuousOn Y (closure Ω) ∧ EqOn (gradient v) Y Ω ∧
      EqOn Y (fun x => b x • closedGradient Ω u x) (frontier Ω) := by
  obtain ⟨Y,hY,ht,hae⟩ := c.lipschitzMultipliedGradient_closed hΩ hμ hl hD hu hb
  let X := lipschitzMultipliedGradient hΩ hμ hl hD hu hb
  have hE : firstPositiveNeumannValue Ω * ‖vectorValue X‖^2 =
      ‖divergenceL X‖^2 + ‖curlL X‖^2 := by
    change vectorForm (firstPositiveNeumannValue Ω) X X = 0 at hz
    simp only [vectorForm,real_inner_self_eq_norm_sq] at hz
    linarith
  obtain ⟨v,hv,he⟩ := vector_equality_interior_pointwise hΩ.2.1 hΩ.1 hΩ.2.2.2.1
    hΩ.2.2.1 hμ hl hD (vectorValue X) (divergenceL X) (curlL X)
    (lipschitzMultipliedGradient_tangent hΩ hμ hl hD hu hb)
    (partialL_test_curl hΩ.2.1 X) hE Y (hY.mono subset_closure) hae
  exact ⟨v,Y,hv,hY,he,ht⟩
end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedNullGradient

section ClosedEigenRepresentative

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace Topology NNReal
namespace StrictHotSpots

lemma InInteriorNeumannEigenspace.congr_on {Ω : Set Plane} (ho : IsOpen Ω)
    {u v : Plane → ℝ} (hu : InInteriorNeumannEigenspace Ω u) (he : EqOn u v Ω) :
    InInteriorNeumannEigenspace Ω v := by
  have hg : EqOn (gradient u) (gradient v) Ω := by
    intro x hx
    unfold gradient
    rw [(show u =ᶠ[𝓝 x] v from eventually_of_mem (ho.mem_nhds hx) (fun y hy => he hy)).fderiv_eq]
  have hae : u =ᵐ[volume.restrict Ω] v := (ae_restrict_iff' ho.measurableSet).mpr (Eventually.of_forall he)
  have hgae : gradient u =ᵐ[volume.restrict Ω] gradient v :=
    (ae_restrict_iff' ho.measurableSet).mpr (Eventually.of_forall hg)
  refine ⟨hu.1.congr he.symm,hu.2.1.congr hae hgae,(integral_congr_ae hae).symm.trans hu.2.2.1,?_⟩
  intro f g hf
  calc
    _ = ∫ x in Ω, ⟪gradient u x, g x⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [hgae] with x hx
      rw [hx]
    _ = _ := hu.2.2.2 f g hf
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]

namespace Conformal.ClosedDiskChart
open DiskH10
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

include c




theorem exists_lipschitz_potential (hb : Bornology.IsBounded Ω)
    {v : Plane → ℝ} (hv : ContDiffOn ℝ ∞ v Ω) {Y : Plane → Plane}
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω) :
    ∃ (V : Plane → ℝ) (A : ℝ≥0), LipschitzWith A V ∧ EqOn v V Ω := by
  obtain ⟨M,hM⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hY
  let A : ℝ≥0 := ⟨c.bound * max M 0,mul_nonneg c.bound_pos.le (le_max_right _ _)⟩
  have hd : ∀ x ∈ disk, DifferentiableAt ℝ (c.pullDatum v) x := fun x hx =>
    ((c.pullDatum_smooth hv).differentiableOn (by simp) x hx).differentiableAt (isOpen_ball.mem_nhds hx)
  have hbound (x : Plane) (hx : x ∈ disk) : ‖fderiv ℝ (c.pullDatum v) x‖₊ ≤ A := by
    change ‖fderiv ℝ (c.pullDatum v) x‖ ≤ c.bound * max M 0
    have hn : ‖gradient (c.pullDatum v) x‖ = ‖fderiv ℝ (c.pullDatum v) x‖ := by
      simp only [gradient,LinearIsometryEquiv.norm_map]
    rw [← hn,c.pullDatum_grad_norm (hv.differentiableOn (by simp)) hx,
      he (c.diskMap.map_source hx)]
    exact mul_le_mul (c.bounded_deriv x (c.source_eq.symm ▸ hx))
      ((hM _ (subset_closure (c.diskMap.map_source hx))).trans (le_max_left _ _))
      (norm_nonneg _) c.bound_pos.le
  have hLip : LipschitzOnWith A (c.pullDatum v) disk :=
    (convex_ball (0:Plane) 1).lipschitzOnWith_of_nnnorm_fderiv_le hd hbound
  obtain ⟨f,hf,hef⟩ := hLip.extend_real
  refine ⟨f ∘ c.G,A*c.InvLip,hf.comp c.inverse_lipschitz,?_⟩
  intro x hx
  have hG : c.G x ∈ disk := by
    rw [← c.diskMap_inverse_agrees hx]
    exact c.diskMap.map_target hx
  have hh := hef hG
  change v (c.F (c.G x)) = f (c.G x) at hh
  exact (congrArg v (c.right_inverse x (subset_closure hx))).symm.trans hh



theorem null_eigenfunction_lipschitz (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {v : Plane → ℝ} (hv : InInteriorNeumannEigenspace Ω v) {Y : Plane → Plane}
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω) :
    ∃ (V : Plane → ℝ) (A : ℝ≥0), LipschitzWith A V ∧
      InInteriorNeumannEigenspace Ω V ∧ EqOn (gradient V) Y Ω := by
  obtain ⟨V,A,hV,hvV⟩ := c.exists_lipschitz_potential hb hv.1 hY he
  refine ⟨V,A,hV,hv.congr_on ho hvV,?_⟩
  intro x hx
  have hg : gradient V x = gradient v x := by
    unfold gradient
    rw [(show V =ᶠ[𝓝 x] v from eventually_of_mem (ho.mem_nhds hx) (fun y hy => (hvV hy).symm)).fderiv_eq]
  exact hg.trans (he hx)
end Conformal.ClosedDiskChart
end StrictHotSpots
end
end ClosedEigenRepresentative

section PhysicalCoordinateNull

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10 Hodge HilbertMultipliers
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)




theorem coordinate_null_trace_oai (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0)
    (p : disk) (hz : gradient u (c.F p) = 0) [IsFiniteMeasure c.potential]
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Countable ι]
    (e : HilbertBasis ι ℝ H) {b : Boundary → H} {B : ℝ≥0} (hb : LipschitzWith B b)
    (hid : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel c.densityBound_ne_top
      (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) p s t) :
    ∀ i, ∃ (v : Plane → ℝ) (Y : Plane → Plane), InInteriorNeumannEigenspace Ω v ∧
      ContinuousOn v (closure Ω) ∧ ContinuousOn Y (closure Ω) ∧ EqOn (gradient v) Y Ω ∧
      ∀ s : Boundary, Y (c.F s) = inner ℝ (e i) (b s) • closedGradient Ω u (c.F s) := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  have hμ := firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne
  obtain ⟨L,_hL,hl,hD⟩ := H10.subcritical hΩ.2.1 hΩ.1 hΩ.2.2.1
  have hext (i : ι) := c.boundary_scalar_extension (coordinate_lipschitz e hb i)
  choose f A hf ht using hext
  let X (i : ι) := lipschitzMultipliedGradient hΩ hμ hl hD hu (hf i)
  let E (i : ι) := vectorForm (firstPositiveNeumannValue Ω) (X i) (X i)
  have hE (i : ι) : E i = (1/2:ℝ)*∫ z : Boundary × Boundary,
      fullBoundaryN c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2 *
      (inner ℝ (e i) (b z.1-b z.2))^2 *
      inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
        ∂boundaryMeasure.prod boundaryMeasure := by
    rw [show E i = _ from c.lipschitz_multiplier_kernel hΩ hu hμ hl hD (hf i)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simp only [fullBoundaryN_eq,inner_sub_right,ht]
  have hsum := full_embedding_coordinate_sum c.densityBound_ne_top (c.density_bound hμ.le) e p
    (c.operator_norm_lt_one hΩ.2.2.1 hΩ.1 hμ) hb.continuous hid (c.closedGradient_trace_continuous hΩ hu)
  have hzero := c.boundary_gradient_integral_zero hΩ hu hne p hz
  rw [hzero,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero] at hsum
  have hs : HasSum E 0 := by
    convert hsum using 1
    exact funext hE
  have hzE (i : ι) : E i = 0 := nonnegative_coordinate_energy_zero hs
    (fun i => lipschitzMultipliedGradient_nonneg hΩ hu hμ hl hD (hf i)) i
  intro i
  obtain ⟨v,Y,hv,hY,hvY,hYt⟩ := c.lipschitzMultipliedGradient_null hΩ hμ hl hD hu (hf i) (hzE i)
  obtain ⟨V,D,hV,hVE,hVY⟩ := c.null_eigenfunction_lipschitz hΩ.2.1 hΩ.2.2.1 hv hY hvY
  refine ⟨V,Y,hVE,hV.continuous.continuousOn,hY,hVY,?_⟩
  intro s
  rw [hYt (c.maps_boundary (by simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_sphere_zero_iff_norm] using s.property))]
  simp only [ht]
end StrictHotSpots.Conformal.ClosedDiskChart
end
end PhysicalCoordinateNull

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace_oai.{u_1, u_2} := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace_oai.{u_1, u_2}
