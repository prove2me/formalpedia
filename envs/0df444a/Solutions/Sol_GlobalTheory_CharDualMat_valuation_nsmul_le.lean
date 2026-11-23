-- Prove2me | solution 1 for GlobalTheory.CharDualMat.valuation_nsmul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:39.609155+00:00
-- url     : https://prove2.me/submissions/ab02c7d2-f8df-4f7c-ab57-17be9a9bd17f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.CharDualMat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CharDualMat
namespace _root_.GlobalTheory.CharDualMat
theorem _root_.solution (t : k) (n : ℕ) : valuation k (n • t) ≤ valuation k t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    exact ((valuation k).map_add _ _).trans (max_le ih le_rfl)
end _root_.GlobalTheory.CharDualMat
end GlobalTheory.CharDualMat
