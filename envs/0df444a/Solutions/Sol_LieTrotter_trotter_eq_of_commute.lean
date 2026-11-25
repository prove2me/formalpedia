-- Prove2me | solution 1 for LieTrotter.trotter_eq_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:20:19.89782+00:00
-- url     : https://prove2.me/submissions/b6330ee9-d0d5-496c-969d-d01dcfffaf63

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Definitions.Def_LieTrotter_Commutator
public import Theorems.Thm_LieTrotter_norm_trotter_sub_le_commutator

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace Set
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution {A B : 𝔸} (h : Commute A B) (n : ℕ) (hn : 1 ≤ n) :
    (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n = exp (A + B) := by
  have hb := norm_trotter_sub_le_commutator A B n hn
  rw [h.eq, sub_self, norm_zero, zero_div, zero_mul] at hb
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
end LieTrotter
