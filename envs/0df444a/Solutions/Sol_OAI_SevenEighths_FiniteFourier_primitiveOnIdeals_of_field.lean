-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.primitiveOnIdeals_of_field
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:15.711792+00:00
-- url     : https://prove2.me/submissions/c64908c7-d30a-483c-a4e1-f8ee858bba12

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
namespace OAI.SevenEighths.FiniteFourier
theorem _root_.solution {F : Type*} [Field F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) : IsPrimitiveOnIdeals χ := by
  intro I hI
  have htop : I = ⊤ := (Ideal.eq_bot_or_top I).resolve_left hI
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
  exact ⟨u, by rw [htop]; trivial, hu⟩
end OAI.SevenEighths.FiniteFourier
