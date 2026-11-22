-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentCode_determines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:23.880188+00:00
-- url     : https://prove2.me/submissions/641385b6-6535-4d9e-abec-7ce007d6a5c0

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_mem_assignmentPrimes
import Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_primeFactors
import Theorems.Thm_LongGapsBetweenPrimes_assignmentCode_mod

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (hroot : ∀ p, Function.Injective (root p)) (σ τ : PrimeIndex P → Option (Fin k))
    (hn : assignmentProduct (fun p : PrimeIndex P => p.val) σ =
      assignmentProduct (fun p : PrimeIndex P => p.val) τ)
    (ha : assignmentCode root σ = assignmentCode root τ) : σ = τ := by
  funext p
  have hsupp : assignmentPrimes σ = assignmentPrimes τ := by
    rw [← assignmentProduct_primeFactors σ, hn, assignmentProduct_primeFactors]
  have hp : (σ p).isSome ↔ (τ p).isSome := by
    rw [← mem_assignmentPrimes, ← mem_assignmentPrimes, hsupp]
  cases hσ : σ p <;> cases hτ : τ p
  · rfl
  · simp [hσ, hτ] at hp
  · simp [hσ, hτ] at hp
  · congr 1
    apply hroot p
    apply Fin.ext
    have hs := assignmentCode_mod root σ p (by simp [hσ])
    have ht := assignmentCode_mod root τ p (by simp [hτ])
    simpa [assignedRoot, hσ, hτ] using
      hs.symm.trans ((congrArg (· % p.val) ha).trans ht)
end LongGapsBetweenPrimes
