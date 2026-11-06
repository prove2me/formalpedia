-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.primitive_gaussSum_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:17.804763+00:00
-- url     : https://prove2.me/submissions/cee356c2-9077-46bc-8be3-59680fe2c2a7

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_gaussSum_norm_sq

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
namespace OAI.SevenEighths.FiniteFourier
theorem _root_.solution (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card R : ℝ) := by
  rw [← primitive_gaussSum_norm_sq χ hχ ψ hψ, Real.sqrt_sq (norm_nonneg _)]
end OAI.SevenEighths.FiniteFourier
