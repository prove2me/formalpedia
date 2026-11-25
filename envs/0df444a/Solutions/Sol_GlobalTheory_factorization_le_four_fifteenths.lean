-- Prove2me | solution 1 for GlobalTheory.factorization_le_four_fifteenths
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:58.915408+00:00
-- url     : https://prove2.me/submissions/5f25497b-3a48-45ca-a8a0-1a66bde8e48a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorizationLeFourFifteenths

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {l B : ℕ} (hl : 5 ≤ l) (hB : B ≠ 0) :
    (B.factorization l : ℝ) ≤ 4 / 15 * (B : ℝ) := by
  have h1 : l ^ B.factorization l ≤ B := Nat.ordProj_le l hB
  have h2 : 5 ^ B.factorization l ≤ l ^ B.factorization l := Nat.pow_le_pow_left hl _
  have h3 : ∀ k : ℕ, 4 * k + 1 ≤ 5 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have h4 : 4 * B.factorization l + 1 ≤ B := le_trans (h3 _) (le_trans h2 h1)
  have h5 : (4 : ℝ) * (B.factorization l : ℝ) + 1 ≤ B := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ (B.factorization l : ℝ) := Nat.cast_nonneg _
  linarith
end GlobalTheory
