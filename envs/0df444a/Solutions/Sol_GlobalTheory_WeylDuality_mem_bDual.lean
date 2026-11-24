-- Prove2me | solution 1 for GlobalTheory.WeylDuality.mem_bDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:20.728264+00:00
-- url     : https://prove2.me/submissions/435fe226-2aec-4a38-b12b-f485db3f5148

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ))
    (P : MvPolynomial (Fin r × Fin n) ℚ) :
    P ∈ bDual r n hn ν M ↔
      P ∈ dualWeyl ℚ r n ν ∧ ∀ Q ∈ M, ∃ z : ℤ, fockQ P Q = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
  exact Iff.rfl
end GlobalTheory.WeylDuality
