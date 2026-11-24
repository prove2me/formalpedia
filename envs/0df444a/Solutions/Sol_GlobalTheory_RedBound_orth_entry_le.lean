-- Prove2me | solution 1 for GlobalTheory.RedBound.orth_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:56:30.688407+00:00
-- url     : https://prove2.me/submissions/fabad377-81ac-436e-9007-b1748c13a06f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.RedBound
namespace GlobalTheory.RedBound
theorem _root_.solution {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (h : kᵀ * k = 1) (p q : Fin N) :
    |k p q| ≤ 1 := by
  have h1 : ∑ r, k r q * k r q = 1 := by
    have := congrFun (congrFun h q) q
    simpa [Matrix.mul_apply] using this
  have h2 : k p q * k p q ≤ ∑ r, k r q * k r q :=
    Finset.single_le_sum (f := fun r => k r q * k r q) (fun r _ => mul_self_nonneg _)
      (Finset.mem_univ p)
  rw [h1] at h2
  have h3 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact h2
  nlinarith [abs_nonneg (k p q)]
end GlobalTheory.RedBound
