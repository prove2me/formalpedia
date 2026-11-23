-- Prove2me | solution 1 for GlobalTheory.CubeFrame.differentiableOn_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:54.75194+00:00
-- url     : https://prove2.me/submissions/b1f5deff-8ef9-4512-892a-fc2a922373a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
namespace GlobalTheory.CubeFrame
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {U : Set X} {f g : X → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (h0 : ∀ x ∈ U, g x ≠ 0) : DifferentiableOn ℂ (fun x => f x / g x) U := by
  simp only [div_eq_mul_inv]
  exact hf.mul (hg.inv h0)
end GlobalTheory.CubeFrame
