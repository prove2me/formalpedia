-- Prove2me | solution 1 for LieTrotter.exp_pow_eq_exp_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:37:08.433742+00:00
-- url     : https://prove2.me/submissions/1bafbf5e-cbcf-42b1-b3c1-eb45df11ceee

module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NoncommRing
public import Definitions.Def_LieTrotter_Basic

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormOneClass 𝔸]
omit [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution (x : 𝔸) (n : ℕ) : exp x ^ n = exp (n • x) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih,
      ← exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
        ((Commute.refl x).smul_left (k : ℕ))
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _),
      ← succ_nsmul]
end LieTrotter
