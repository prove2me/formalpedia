-- Prove2me | solution 1 for GlobalTheory.l1_shift_single_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:28.902993+00:00
-- url     : https://prove2.me/submissions/12b2b3d1-c532-4c4b-87b7-39178572511f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AlgTensWtNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (ω Λ : Fin n → ℝ) (t e : ℝ) (he : |e| ≤ 1) (c : Fin n)
    (h : ∑ a, |ω a - Λ a| ≤ t) :
    ∑ a, |(ω a + if a = c then e else 0) - Λ a| ≤ t + 1 := by
  have h1 : ∀ a, |(ω a + if a = c then e else 0) - Λ a| ≤ |ω a - Λ a| + if a = c then 1 else 0 := by
    intro a
    split_ifs
    · have : ω a + e - Λ a = (ω a - Λ a) + e := by ring
      rw [this]
      exact (abs_add_le _ _).trans (by linarith)
    · simp
  calc _ ≤ ∑ a, (|ω a - Λ a| + if a = c then 1 else 0) := Finset.sum_le_sum fun a _ => h1 a
    _ = ∑ a, |ω a - Λ a| + 1 := by rw [Finset.sum_add_distrib]; simp
    _ ≤ t + 1 := by linarith
end GlobalTheory
