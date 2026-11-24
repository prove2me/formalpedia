-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:27.194813+00:00
-- url     : https://prove2.me/submissions/f5afc2d9-958e-411f-adf9-19a6a511dab3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableProdPowMultiIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Summability
namespace GlobalTheory.CompanionTheory.Summability
theorem _root_.solution : ∀ (r : ℕ) (x : Fin r → ℝ), (∀ i, 0 ≤ x i) → (∀ i, x i < 1) →
    Summable (fun j : Fin r → ℕ => ∏ i, x i ^ j i) := by
  intro r
  induction r with
  | zero =>
    intro x _ _
    exact (hasSum_fintype _).summable
  | succ r ih =>
    intro x h0 h1
    let e : ℕ × (Fin r → ℕ) ≃ (Fin (r + 1) → ℕ) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun j => (j 0, Fin.tail j)
        left_inv := fun p => by simp
        right_inv := fun j => by simp }
    rw [← e.summable_iff]
    have hA : Summable (fun n : ℕ => x 0 ^ n) := summable_geometric_of_lt_one (h0 0) (h1 0)
    have hB : Summable (fun j : Fin r → ℕ => ∏ i, x i.succ ^ j i) :=
      ih (fun i => x i.succ) (fun i => h0 _) (fun i => h1 _)
    have hM := hA.mul_of_nonneg hB (fun n => pow_nonneg (h0 0) n)
      (fun j => Finset.prod_nonneg (fun i _ => pow_nonneg (h0 _) _))
    refine hM.congr ?_
    rintro ⟨n, j⟩
    simp [e, Fin.prod_univ_succ]
end GlobalTheory.CompanionTheory.Summability
