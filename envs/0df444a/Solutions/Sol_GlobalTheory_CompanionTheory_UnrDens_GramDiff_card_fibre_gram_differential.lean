-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.GramDiff.card_fibre_gram_differential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:24:42.469834+00:00
-- url     : https://prove2.me/submissions/8426bc39-7a5f-4a41-a0c5-0807b5fa07ae

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatricesCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_GramDiff_diffMap_surjective
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_GramDiff_card_fibre_mul
import Theorems.Thm_GlobalTheory_T_hermitian_matrices_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.GramDiff
variable {E : Type} [CommRing E] (τ : E →+* E)
namespace GlobalTheory.CompanionTheory.UnrDens.GramDiff
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin m) (Fin n) E) (H : Matrix (Fin n) (Fin n) E), cT τ S = S → cT τ T = T → IsUnit T.det → cT τ x * S * x = T → cT τ H = H → Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} = q ^ (2 * m * n - n ^ 2) := by
  intro E _ τ q ε h m n hnm S T x H hS _ hT hx hH
  have hq : 0 < q := lt_trans Nat.zero_lt_one h.one_lt
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h.card]; positivity)
  have hM : Nat.card (Matrix (Fin m) (Fin n) E) = ((q ^ 2) ^ n) ^ m := by
    change Nat.card (Fin m → Fin n → E) = _
    rw [Nat.card_fun, Nat.card_fun, h.card]
    simp
  have hHerm : Nat.card (hermSub τ n) = q ^ (n ^ 2) := GlobalTheory.T.hermitian_matrices_card E τ q ε h n
  have hfib := card_fibre_mul (diffMap τ h.inv S hS x)
    (diffMap_surjective τ h S hS T x hT hx) ⟨H, hH⟩
  have hc : Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} =
      Nat.card {y // diffMap τ h.inv S hS x y = ⟨H, hH⟩} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [Subtype.ext_iff]
      rfl)
  have hle : n ^ 2 ≤ 2 * m * n := by nlinarith
  have hpow : ((q ^ 2) ^ n) ^ m = q ^ (n ^ 2) * q ^ (2 * m * n - n ^ 2) := by
    rw [← pow_add, Nat.add_sub_cancel' hle, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hc]
  rw [hHerm, hM, hpow, mul_comm] at hfib
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq _) hfib
end GlobalTheory.CompanionTheory.UnrDens.GramDiff
