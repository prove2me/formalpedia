-- Prove2me | solution 1 for NumberField.finrank_eq_one_of_forall_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9c3cc0da-8e14-57a3-915a-478d1d862fd0

import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt

set_option autoImplicit false

open Module
attribute [local instance] FractionRing.liftAlgebra

namespace NumberField
p2m_export "NumberField" "abs_discr_gt_two discr absNorm_differentIdeal"
p2m_open "NumberField"

variable (K : Type*) [Field K] [NumberField K]

p2m_open_scoped "NumberField P2MW.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt.NumberField"

theorem differentIdeal_eq_top_of_forall_not_dvd'
    (h : ∀ P : Ideal (𝓞 K), P.IsMaximal → ¬ P ∣ differentIdeal ℤ (𝓞 K)) :
    differentIdeal ℤ (𝓞 K) = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  exact h P hPmax (Ideal.dvd_iff_le.mpr hle)

theorem natAbs_discr_eq_one_of_forall_not_dvd'
    (h : ∀ P : Ideal (𝓞 K), P.IsMaximal → ¬ P ∣ differentIdeal ℤ (𝓞 K)) :
    (discr K).natAbs = 1 := by
  have h1 : (differentIdeal ℤ (𝓞 K)).absNorm = (discr K).natAbs :=
    absNorm_differentIdeal (K := K) (𝒪 := 𝓞 K)
  rw [← h1, differentIdeal_eq_top_of_forall_not_dvd' K h, Ideal.absNorm_top]

theorem finrank_eq_one_of_forall_not_dvd'
    (h : ∀ P : Ideal (𝓞 K), P.IsMaximal → ¬ P ∣ differentIdeal ℤ (𝓞 K)) :
    finrank ℚ K = 1 := by
  by_contra hne
  have hpos : 0 < finrank ℚ K := finrank_pos
  have h1 : 1 < finrank ℚ K := by omega
  have h2 : 2 < |discr K| := abs_discr_gt_two h1
  rw [← Int.natCast_natAbs, natAbs_discr_eq_one_of_forall_not_dvd' K h] at h2
  norm_num at h2

theorem forall_not_dvd_differentIdeal_of_forall_isUnramifiedAt'
    (H : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], Algebra.IsUnramifiedAt ℤ P) :
    ∀ P : Ideal (𝓞 K), P.IsMaximal → ¬ P ∣ differentIdeal ℤ (𝓞 K) := by
  haveI : Algebra.IsAlgebraic (FractionRing ℤ) (FractionRing (𝓞 K)) :=
    isAlgebraic_of_isFractionRing (R := ℤ) (S := 𝓞 K) (FractionRing ℤ) (FractionRing (𝓞 K))
  haveI : Algebra.IsIntegral (FractionRing ℤ) (FractionRing (𝓞 K)) :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  intro P hP
  haveI := hP
  exact not_dvd_differentIdeal_iff.mpr (H P)

end NumberField

open scoped _root_.NumberField _root_.P2MW.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt.NumberField in

theorem solution
    (K : Type*) [Field K] [NumberField K]
    (H : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ K = 1 :=
  NumberField.finrank_eq_one_of_forall_not_dvd' K
    (NumberField.forall_not_dvd_differentIdeal_of_forall_isUnramifiedAt' K H)

end S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt
end P2MW
export P2MW.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt (solution)
