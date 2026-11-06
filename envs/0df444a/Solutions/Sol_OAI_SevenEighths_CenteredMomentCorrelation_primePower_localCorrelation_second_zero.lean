-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.primePower_localCorrelation_second_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:06.344831+00:00
-- url     : https://prove2.me/submissions/3d48a63c-9636-4b2c-b88d-df4646c3f4d1

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_PrimePower
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePower_localCorrelation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_localCorrelation_second_zero


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
    (hχ : orderOf χ = 6) (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hu : primePowerReduction P hc u ≠ 0 :=
    (isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [primePower_localCorrelation, hv, localCorrelation_second_zero _ hu, hcard, hpow]
  split_ifs <;> rfl
end OAI.SevenEighths.CenteredMomentCorrelation
