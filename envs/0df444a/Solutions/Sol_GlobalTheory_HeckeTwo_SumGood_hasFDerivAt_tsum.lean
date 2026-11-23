-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.SumGood.hasFDerivAt_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:40.999641+00:00
-- url     : https://prove2.me/submissions/b0d038b9-0544-4bce-81ce-154b8a06efe7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.SumGood
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] {ι : Type}
namespace GlobalTheory.HeckeTwo.SumGood
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) {z : V} (hz : z ∈ U) :
    HasFDerivAt (fun y => ∑' i, f i y) (∑' i, fderiv ℝ (f i) z) z := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hz
  have hsub : Metric.closedBall z (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrU
  have hK : IsCompact (Metric.closedBall z (r / 2)) := isCompact_closedBall z (r / 2)
  obtain ⟨u1, hu1, hb1⟩ := hf.2 _ hK hsub 1
  obtain ⟨u0, hu0, hb0⟩ := hf.2 _ hK hsub 0
  have hzb : z ∈ Metric.ball z (r / 2) := Metric.mem_ball_self (by linarith)
  refine hasFDerivAt_tsum_of_isPreconnected hu1 Metric.isOpen_ball
    (convex_ball z (r / 2)).isPreconnected (fun i y hy => ?_) (fun i y hy => ?_) hzb ?_ hzb
  · have hyU : y ∈ U := hsub (Metric.ball_subset_closedBall hy)
    exact (((hf.1 i).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).hasFDerivAt
  · have := hb1 i y (Metric.ball_subset_closedBall hy)
    rwa [norm_iteratedFDeriv_one] at this
  · refine Summable.of_norm_bounded hu0 (fun i => ?_)
    have := hb0 i z (Metric.mem_closedBall_self (by linarith))
    rwa [norm_iteratedFDeriv_zero] at this
end GlobalTheory.HeckeTwo.SumGood
