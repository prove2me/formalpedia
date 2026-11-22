-- Prove2me | solution 1 for LongGapsBetweenPrimes.card_assignment_family_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:54.094621+00:00
-- url     : https://prove2.me/submissions/ec152b25-ecba-4771-9754-c86cbfb0af0e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_assignmentCode_lt
import Theorems.Thm_LongGapsBetweenPrimes_assignmentCode_determines

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} {ι : Type*} [Fintype ι]
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (σ : ι → PrimeIndex P → Option (Fin k)) (hσ : Function.Injective σ)
    {D : ℝ} (hD : 1 ≤ D)
    (hcut : ∀ i, (assignmentProduct (fun p : PrimeIndex P => p.val) (σ i) : ℝ) ≤ D) :
    (Fintype.card ι : ℝ) ≤ 4 * D ^ 2 := by
  let f (i : ι) : Fin (⌊D⌋₊ + 1) × Fin (⌊D⌋₊ + 1) :=
    (⟨assignmentProduct (fun p : PrimeIndex P => p.val) (σ i),
      Nat.lt_succ_of_le (Nat.le_floor (hcut i))⟩,
     ⟨assignmentCode root (σ i), (assignmentCode_lt root (σ i)).trans
      (Nat.lt_succ_of_le (Nat.le_floor (hcut i)))⟩)
  have hf : Function.Injective f := by
    intro i j hij
    apply hσ
    exact assignmentCode_determines root hroot (σ i) (σ j)
      (congrArg (fun x => x.1.val) hij) (congrArg (fun x => x.2.val) hij)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod, Fintype.card_fin, ← pow_two] at hcard
  calc
    (Fintype.card ι : ℝ) ≤ ((⌊D⌋₊ : ℝ) + 1) ^ 2 := by
      exact_mod_cast hcard
    _ ≤ (2 * D) ^ 2 := by
      gcongr
      linarith [Nat.floor_le (show 0 ≤ D by linarith)]
    _ = 4 * D ^ 2 := by ring
end LongGapsBetweenPrimes
