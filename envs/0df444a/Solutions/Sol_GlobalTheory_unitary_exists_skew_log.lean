-- Prove2me | solution 1 for GlobalTheory.unitary_exists_skew_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:05.794937+00:00
-- url     : https://prove2.me/submissions/5ae715be-de9e-4ba5-8b48-c9307c955305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryExistsSkewLog
import Theorems.Thm_GlobalTheory_unitary_submonoid_exists_skewAdjoint_log_polynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ) (hk : kᴴ * k = 1) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  have hmem : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨hk, mul_eq_one_comm.mp hk⟩
  obtain ⟨X, p, h1, h2, h3⟩ := unitary_submonoid_exists_skewAdjoint_log_polynomial n k hmem
  exact ⟨X, p, h1, h2, h3⟩
end GlobalTheory
