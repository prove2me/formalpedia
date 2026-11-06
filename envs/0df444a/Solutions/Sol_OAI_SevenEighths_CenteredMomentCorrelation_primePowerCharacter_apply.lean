-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.primePowerCharacter_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:02.375698+00:00
-- url     : https://prove2.me/submissions/27c609d3-31b0-4e17-98c7-85f40b6d12ef

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_PrimePower

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open NumberField
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
attribute [local instance] OAI.SevenEighths.CenteredMomentCorrelation._p2m_local_instance_3727eb8614_14
omit [NumberField K]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) (x : 𝓞 K ⧸ P ^ c) :
    primePowerCharacter P hc χ x = χ (primePowerReduction P hc x) := rfl
end OAI.SevenEighths.CenteredMomentCorrelation
