-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.primePower_localCorrelation_first_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:16.674958+00:00
-- url     : https://prove2.me/submissions/89db3080-631d-49d0-873c-7206e8e2ed7d

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_PrimePower
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePowerReduction_surjective
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePowerReduction_multiplicity
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_reduction_unit_left
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_localCorrelation_first_zero


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
    (hχ : orderOf χ = 6) (u : 𝓞 K ⧸ P ^ c) (v : (𝓞 K ⧸ P ^ c)ˣ)
    (k : 𝓞 K ⧸ P ^ c) (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : 𝓞 K ⧸ P ^ c) * x) (fun y => u * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hv : primePowerReduction P hc v ≠ 0 :=
    (isUnit_iff_ne_zero.mp (v.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  change (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) = _
  rw [hu, localCorrelation_first_zero _ hv, hcard, hpow]
  split_ifs <;> rfl
end OAI.SevenEighths.CenteredMomentCorrelation
