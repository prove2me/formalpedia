-- Prove2me | solution 1 for GlobalTheory.QFam.hasQ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:16.937832+00:00
-- url     : https://prove2.me/submissions/985f9f46-a6c8-4825-9573-b5870d5359c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups ModularForm
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n) (f τ) := by
  have key : ∀ (τ : ℍ) (n : ℕ), Complex.exp (2 * Real.pi * Complex.I * n * τ / N)
      = Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n := by
    intro τ n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [HasQ, key]
end GlobalTheory.QFam
