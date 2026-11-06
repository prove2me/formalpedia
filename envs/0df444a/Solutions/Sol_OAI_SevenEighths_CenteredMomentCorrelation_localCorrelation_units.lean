-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.localCorrelation_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:05.682954+00:00
-- url     : https://prove2.me/submissions/3fcd4d03-4ec7-468c-9079-d6cbad7939c5

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_shiftCorrelation_zero
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_shiftCorrelation_nonprincipal
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_shiftCorrelation_principal
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_localCorrelation_eq_shift

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) *
      (if k = 0 then (Fintype.card F : ℂ) - 1
       else if χ = 1 then (Fintype.card F : ℂ) - 2 else -1) := by
  rw [localCorrelation_eq_shift χ h₁ h₂]
  by_cases hk : k = 0
  · simp [hk, shiftCorrelation_zero]
  · by_cases hχ : χ = 1
    · simp [hk, hχ, shiftCorrelation_principal (div_ne_zero hk h₁)]
    · simp [hk, hχ, shiftCorrelation_nonprincipal χ hχ (div_ne_zero hk h₁)]
end OAI.SevenEighths.CenteredMomentCorrelation
