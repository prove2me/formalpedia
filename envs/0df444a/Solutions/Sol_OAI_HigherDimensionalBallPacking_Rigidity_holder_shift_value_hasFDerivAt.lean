-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.holder_shift_value_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:04:41.235511+00:00
-- url     : https://prove2.me/submissions/f83897b1-c922-434c-8089-67066f2604e6

import Mathlib
import Definitions.Def_OAIQ10Bp004

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCompactness
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderGraph_isClosed _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSubmodule_isClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {K E : Type*} [MetricSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma holder_norm_le_of_estimate (α : ℝ) (u : HolderSpace K E α) {A H : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (h0 : ∀ x, ‖holderValue α u x‖ ≤ A)
    (h1 : ∀ x y, ‖holderValue α u x-holderValue α u y‖ ≤ H*(dist x y)^α) :
    ‖u‖ ≤ max A H := by
  change max ‖u.val.1‖ ‖u.val.2‖ ≤ _
  apply max_le_max
  · exact (BoundedContinuousFunction.norm_le hA).mpr h0
  · apply (BoundedContinuousFunction.norm_le hH).mpr
    intro z
    have hh := h1 z.val.1 z.val.2
    rw [holderSpace_relation α u _ _ z.property,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (mul_comm _ _))
      (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α)



end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_OrbitRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.hdiffHolderGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.hdiffHolderSpace
omit [CompleteSpace E] in
 theorem holder_hasFDerivAt (α : ℝ) (hα : 0<α)
    (F : X → HolderSpace ℂ E α) (D : X → HolderSpace ℂ (X →L[ℝ] E) α)
    (hD : ∀ y z, HasFDerivAt (fun x => holderValue α (F x) z) (holderValue α (D y) z) y)
    (x : X) (hc : ContinuousAt D x) : HasFDerivAt F (holderTranspose α (D x)) x := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro c hcpos
  obtain ⟨ε,hε,hεc⟩ := Metric.mem_nhds_iff.mp (hc (Metric.ball_mem_nhds (D x) hcpos))
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  have hb (w : X) (hw : w∈Metric.ball x ε) : ‖D w-D x‖ ≤ c := by
    simpa only [dist_eq_norm] using (show dist (D w) (D x) < c from hεc hw).le
  apply (holder_norm_le_of_estimate α _ (by positivity) (by positivity) _ _).trans_eq (max_self _)
  · intro z
    change ‖holderValue α (F y) z-holderValue α (F x) z-holderValue α (D x) z (y-x)‖≤_
    apply (convex_ball x ε).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun w _ => (hD w z).hasFDerivWithinAt) _ (Metric.mem_ball_self hε) hy
    intro w hw
    have hh := ((holderValue α (D w-D x)).norm_coe_le_norm z).trans (holderValue_norm α _)
    exact hh.trans (hb w hw)
  · intro z w
    have hh := (convex_ball x ε).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun t _ => ((hD t z).sub (hD t w)).hasFDerivWithinAt)
      (C := c*(dist z w)^α) (φ := holderValue α (D x) z-holderValue α (D x) w) ?_
      (Metric.mem_ball_self hε) hy
    · change ‖(holderValue α (F y) z-holderValue α (F x) z-holderValue α (D x) z (y-x))-
        (holderValue α (F y) w-holderValue α (F x) w-holderValue α (D x) w (y-x))‖≤_
      convert hh using 1
      · congr 1
        simp only [sub_apply,Pi.sub_apply]
        abel
      · ring
    · intro t ht
      have he := holderSpace_estimate α hα (D t-D x) z w
      have heq : (holderValue α (D t) z-holderValue α (D t) w)-
          (holderValue α (D x) z-holderValue α (D x) w)=
          holderValue α (D t-D x) z-holderValue α (D t-D x) w := by
        simp only [map_sub,BoundedContinuousFunction.sub_apply]
        abel
      rw [heq]
      exact he.trans (mul_le_mul_of_nonneg_right (hb t ht) (Real.rpow_nonneg (dist_nonneg) _))

 theorem holder_shift_value_hasFDerivAt_oai (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α) (x : ℂ)
    (hc : ContinuousAt (fun h : ℂ => holderShift α h (c1HolderDeriv α f)) x) :
    HasFDerivAt (fun h : ℂ => holderShift α h (c1HolderValue α f))
      (holderTranspose α (holderShift α x (c1HolderDeriv α f))) x := by
  apply holder_hasFDerivAt α hα _ _ _ x hc
  intro y z
  exact (c1Holder_hasFDerivAt α f (z+y)).comp y ((hasFDerivAt_id y).const_add z)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.holder_shift_value_hasFDerivAt_oai := @OAI.HigherDimensionalBallPacking.Rigidity.holder_shift_value_hasFDerivAt_oai
