-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals.inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:54:06.837702+00:00
-- url     : https://prove2.me/submissions/623196b6-5f81-45c7-b920-8648bdeebda9

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
namespace IsPrimitiveOnIdeals
theorem _root_.solution {χ : MulChar R ℂ} (hχ : IsPrimitiveOnIdeals χ) :
    IsPrimitiveOnIdeals χ⁻¹ := by
  intro I hI
  obtain ⟨u, hu, hχu⟩ := hχ I hI
  refine ⟨u, hu, ?_⟩
  intro hinv
  apply hχu
  simpa only [← MulChar.star_apply', star_star, star_one] using congrArg star hinv
end IsPrimitiveOnIdeals
end OAI.SevenEighths.FiniteFourier
