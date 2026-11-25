-- Prove2me | solution 1 for LieTrotter.norm_pow_succ_sub_pow_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:46:33.745004+00:00
-- url     : https://prove2.me/submissions/276cf025-291c-4496-9737-01433ca55c2a

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Definitions.Def_LieTrotter_Commutator

set_option autoImplicit false
@[expose] public section
public section
open NormedSpace Set
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution {S T : 𝔸} {C : ℝ} (hS : ‖S‖ ≤ C) (hT : ‖T‖ ≤ C)
    (n : ℕ) : ‖S ^ (n + 1) - T ^ (n + 1)‖ ≤ (n + 1) * C ^ n * ‖S - T‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hS
  induction n with
  | zero => simp
  | succ n ih =>
    have hdecomp : S ^ (n + 1 + 1) - T ^ (n + 1 + 1)
        = (S ^ (n + 1) - T ^ (n + 1)) * S + T ^ (n + 1) * (S - T) := by
      rw [pow_succ S (n + 1), pow_succ T (n + 1), sub_mul, mul_sub]
      abel
    have hTn : ‖T ^ (n + 1)‖ ≤ C ^ (n + 1) :=
      (norm_pow_le' T (Nat.succ_pos n)).trans (pow_le_pow_left₀ (norm_nonneg _) hT _)
    calc ‖S ^ (n + 1 + 1) - T ^ (n + 1 + 1)‖
        ≤ ‖S ^ (n + 1) - T ^ (n + 1)‖ * ‖S‖ + ‖T ^ (n + 1)‖ * ‖S - T‖ := by
          rw [hdecomp]
          exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ((n + 1) * C ^ n * ‖S - T‖) * C + C ^ (n + 1) * ‖S - T‖ := by
          gcongr
      _ = ((n + 1 : ℕ) + 1) * C ^ (n + 1) * ‖S - T‖ := by push_cast; ring
end LieTrotter
