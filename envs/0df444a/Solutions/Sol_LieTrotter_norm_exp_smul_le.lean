-- Prove2me | solution 1 for LieTrotter.norm_exp_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:49:27.639477+00:00
-- url     : https://prove2.me/submissions/a3566923-761b-4946-8871-f734bcca2636

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Definitions.Def_LieTrotter_Commutator
public import Theorems.Thm_LieTrotter_norm_exp_le_exp_norm


set_option autoImplicit false
@[expose] public section
public section
open NormedSpace Set
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
namespace LieTrotter
theorem _root_.solution (X : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • X)‖ ≤ Real.exp (t * ‖X‖) := by
  calc ‖exp (t • X)‖ ≤ Real.exp ‖t • X‖ := norm_exp_le_exp_norm _
    _ = Real.exp (t * ‖X‖) := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
end LieTrotter
