-- Prove2me | solution 1 for NumberField.subgroup_eq_top_of_forall_inertia_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e5b68c3d-d5fa-5790-9879-41eb21dd05a5

import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_subgroup_eq_top_of_forall_inertia_le

open scoped NumberField

attribute [local instance] Ideal.Quotient.field in
theorem solution {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] (H : Subgroup (K ≃ₐ[ℚ] K)) (hH : ∀ P : Ideal (NumberField.RingOfIntegers K), P.IsMaximal → P.inertia (K ≃ₐ[ℚ] K) ≤ H) : H = ⊤ := by
  classical

  let F : IntermediateField ℚ K := FixedPoints.intermediateField H
  haveI hHF : IsGaloisGroup H (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 K) F K

  have hunr : ∀ (p : Ideal (𝓞 F)) [p.IsMaximal], Algebra.IsUnramifiedAt ℤ p := by
    intro p hp
    have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField F)

    obtain ⟨P, hPmax, hPp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral p
      (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
        exact bot_le)
    haveI : P.LiesOver p := ⟨hPp.symm⟩

    haveI : (p.under ℤ).IsMaximal := Ideal.IsMaximal.under ℤ p
    haveI : P.LiesOver (p.under ℤ) := Ideal.LiesOver.trans P p (p.under ℤ)
    have h𝔭0 : p.under ℤ ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hp0

    have : Finite (ℤ ⧸ p.under ℤ) := Ring.HasFiniteQuotients.finiteQuotient h𝔭0
    have : Finite (𝓞 F ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp0

    have c1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[ℚ] K) (p.under ℤ) P
    have c2 := Ideal.card_inertia_eq_ramificationIdxIn (G := H) p P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p.under ℤ) P (K ≃ₐ[ℚ] K),
      ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p.under ℤ) (q := P) h𝔭0] at c1
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P H,
      ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p) (q := P) hp0] at c2

    have c3 : Nat.card (P.inertia H) = Nat.card (P.inertia (K ≃ₐ[ℚ] K)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hH P hPmax)).toEquiv

    have hne : p.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
    have he : (p.under ℤ).ramificationIdx' p = 1 := by
      have h : (p.under ℤ).ramificationIdx' P = p.ramificationIdx' P := by
        rw [← c1, ← c2, c3]
      rw [Ideal.ramificationIdx_algebra_tower' (p.under ℤ) p P] at h
      exact (mul_eq_right₀ hne).mp h
    exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.mpr
      ((Ideal.ramificationIdx'_eq_ramificationIdx (p.under ℤ) p h𝔭0).symm.trans he)

  have hF : Module.finrank ℚ F = 1 := by
    by_contra hne
    obtain ⟨p, hpmax, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := F) (𝒪 := 𝓞 F) hne
    exact hram (@hunr p hpmax)

  rw [← Subgroup.card_eq_iff_eq_top, IsGaloisGroup.card_eq_finrank H F K,
    IsGaloisGroup.card_eq_finrank (K ≃ₐ[ℚ] K) ℚ K, ← Module.finrank_mul_finrank ℚ F K, hF, one_mul]

end S_NumberField_subgroup_eq_top_of_forall_inertia_le
end P2MW
export P2MW.S_NumberField_subgroup_eq_top_of_forall_inertia_le (solution)
