-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.Emb.prod_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:52:03.450959+00:00
-- url     : https://prove2.me/submissions/fe64c739-bdbc-450e-9825-9a343567a528

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardOrthonormalFramesHermitianSpaceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsHermitianCongrToOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Emb
variable {E : Type} [CommRing E] {τ : E →+* E}
namespace GlobalTheory.CompanionTheory.UnrDens.Emb
theorem _root_.solution (x : ℝ) (hx : x ≠ 0) (n : ℕ) : ∀ m : ℕ, n ≤ m →
    ∏ i : Fin n, (x ^ (2 * (m - (i : ℕ))) / x) = x ^ (2 * m * n - n ^ 2) := by
  induction n with
  | zero => intro m _; simp
  | succ n ih =>
    intro m hnm
    obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih _ (by omega)]
    have a : 2 * (n + 1 + k) * n - n ^ 2 = n ^ 2 + 2 * n + 2 * k * n := by
      apply Nat.sub_eq_of_eq_add; ring
    have b : 2 * (n + 1 + k) * (n + 1) - (n + 1) ^ 2 = (n + 1) ^ 2 + 2 * k * (n + 1) := by
      apply Nat.sub_eq_of_eq_add; ring
    have c : n + 1 + k - n = k + 1 := by omega
    have d : x ^ (2 * (k + 1)) / x = x ^ (2 * k + 1) := by
      have : x ^ (2 * (k + 1)) = x ^ (2 * k + 1) * x := by ring
      rw [this, mul_div_cancel_right₀ _ hx]
    rw [a, b, c, d, ← pow_add]
    congr 1
    ring
end GlobalTheory.CompanionTheory.UnrDens.Emb
