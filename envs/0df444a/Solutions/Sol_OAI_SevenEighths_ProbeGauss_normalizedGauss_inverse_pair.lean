-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGauss.normalizedGauss_inverse_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:22.003873+00:00
-- url     : https://prove2.me/submissions/abf47982-ae4c-46ae-8b95-dcbc275fddd3

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Gauss
import Theorems.Thm_OAI_SevenEighths_ProbeGauss_gauss_inverse_pair

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section
namespace OAI.SevenEighths.ProbeGauss
theorem _root_.solution {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    normalizedGauss χ ψ * normalizedGauss χ⁻¹ ψ = χ (-1) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  unfold normalizedGauss
  rw [div_mul_div_comm, ← pow_two, hs, gauss_inverse_pair χ ψ hχ hψ]
  exact mul_div_cancel_right₀ _ hq
end OAI.SevenEighths.ProbeGauss
