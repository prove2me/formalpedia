-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.primitive_gaussSum_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:46:57.728898+00:00
-- url     : https://prove2.me/submissions/2a837269-bbec-45f1-9d95-92b298dbbdb5

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_gaussSum_mul_conjugate

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
namespace OAI.SevenEighths.FiniteFourier
theorem _root_.solution (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card R : ℝ) := by
  apply Complex.ofReal_inj.mp
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simpa only [starRingEnd_apply, mul_comm, Complex.ofReal_natCast] using
    primitive_gaussSum_mul_conjugate χ hχ ψ hψ
end OAI.SevenEighths.FiniteFourier
