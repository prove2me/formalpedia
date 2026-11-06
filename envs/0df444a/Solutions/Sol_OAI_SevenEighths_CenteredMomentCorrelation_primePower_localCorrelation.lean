-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.primePower_localCorrelation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:10.924684+00:00
-- url     : https://prove2.me/submissions/f81c9652-e1f1-427a-8781-4f1aa85a38ef

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_PrimePower
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePowerReduction_surjective
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePowerReduction_multiplicity
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_reduction_unit_right


set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open NumberField
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
attribute [local instance] OAI.SevenEighths.CenteredMomentCorrelation._p2m_local_instance_3727eb8614_14
variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
attribute [local instance] OAI.SevenEighths.CenteredMomentCorrelation._p2m_local_instance_3727eb8614_57
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) := by
  rw [fullCorrelation_reduction_unit_right _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  rfl
end OAI.SevenEighths.CenteredMomentCorrelation
