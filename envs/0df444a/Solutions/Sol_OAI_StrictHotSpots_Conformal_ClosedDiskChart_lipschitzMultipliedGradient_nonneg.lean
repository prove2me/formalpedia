-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:32:58.773611+00:00
-- url     : https://prove2.me/submissions/71bf48ee-a4cf-4fd9-97ac-8f6449da5f65

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Hodge_vectorForm_nonneg

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

lemma lipschitzMultipliedGradient_nonneg_oai {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) :
    0 ≤ vectorForm (firstPositiveNeumannValue Ω)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) :=
  vectorForm_nonneg hΩ.2.1 hΩ.1 hΩ.2.2.2.1 hΩ.2.2.1 hμ hl hD _
    (lipschitzMultipliedGradient_tangent hΩ hμ hl hD hu hb)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end LipschitzMultiplierKernel


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_nonneg_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_nonneg_oai
