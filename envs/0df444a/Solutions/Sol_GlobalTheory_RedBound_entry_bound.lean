-- Prove2me | solution 1 for GlobalTheory.RedBound.entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:13:55.044518+00:00
-- url     : https://prove2.me/submissions/52c4f7aa-4107-4a1d-8b47-05c1a06f5190

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
theorem _root_.solution {N : ℕ} (P Z Q : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (c : ℝ)
    (h : ∀ p q, |P i p * Z p q * Q q j| ≤ c) : |(P * Z * Q) i j| ≤ N * N * c := by
  have e : (P * Z * Q) i j = ∑ q, ∑ p, P i p * Z p q * Q q j := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [e]
  calc |∑ q, ∑ p, P i p * Z p q * Q q j| ≤ ∑ q, |∑ p, P i p * Z p q * Q q j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : Fin N, ∑ _p : Fin N, c := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => h p q)
    _ = N * N * c := by simp [Finset.sum_const, Finset.card_fin]; ring
end GlobalTheory.RedBound
