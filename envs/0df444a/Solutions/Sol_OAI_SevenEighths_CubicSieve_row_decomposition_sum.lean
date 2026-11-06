-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.row_decomposition_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:24.911491+00:00
-- url     : https://prove2.me/submissions/533a0f0a-63e9-4b2b-b6a3-1af1f361ccd2

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Algebra
import Theorems.Thm_OAI_SevenEighths_CubicSieve_cubic_row_decomposition

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite Rˣ]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution {ι M : Type*} [CommMonoid M]
    (S : Finset ι) (coef : ι → ℂ) (ρ : ι → M →* R)
    (χ : ι → MulChar R ℂ) (hχ : ∀ n ∈ S, χ n ^ 3 = 1)
    (a b c : M) :
    (∑ n ∈ S, coef n * χ n (ρ n (a * b ^ 2 * c ^ 3))) =
      ∑ n ∈ S,
        (coef n * star (χ n (ρ n b)) *
          (if IsUnit (ρ n c) then 1 else 0)) * χ n (ρ n a) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  have hmap : ρ n (a * b ^ 2 * c ^ 3) =
      ρ n a * (ρ n b) ^ 2 * (ρ n c) ^ 3 := by simp only [map_mul, map_pow]
  rw [hmap, cubic_row_decomposition (χ n) (hχ n hn)]
  ring
end OAI.SevenEighths.CubicSieve
