-- Prove2me | solution 1 for GlobalTheory.ReducedBasisBound.abs_entry_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:56:33.911562+00:00
-- url     : https://prove2.me/submissions/28405905-8efa-4540-9fcf-75ee22216643

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.ReducedBasisBound
namespace GlobalTheory.ReducedBasisBound
theorem _root_.solution {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (h : kᵀ * k = 1) (l i : Fin N) :
    |k l i| ≤ 1 := by
  have e := congrFun (congrFun h i) i
  rw [mul_apply, one_apply_eq] at e
  simp only [transpose_apply] at e
  have : k l i ^ 2 ≤ 1 := by
    rw [← e, sq]
    exact Finset.single_le_sum (f := fun l => k l i * k l i) (fun l _ => mul_self_nonneg _)
      (Finset.mem_univ l)
  exact sq_le_one_iff_abs_le_one _ |>.mp this
end GlobalTheory.ReducedBasisBound
