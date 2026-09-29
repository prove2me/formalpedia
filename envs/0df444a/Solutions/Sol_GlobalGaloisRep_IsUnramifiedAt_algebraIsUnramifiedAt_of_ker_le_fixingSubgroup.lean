-- Prove2me | solution 1 for GlobalGaloisRep.IsUnramifiedAt.algebraIsUnramifiedAt_of_ker_le_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8f867c68-5b7a-5b38-9fb1-ffa5383ff275

import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Theorems.Thm_NumberField_exists_lift_mem_inertia_integralClosure
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GlobalGaloisRep_IsUnramifiedAt_algebraIsUnramifiedAt_of_ker_le_fixingSubgroup

open scoped NumberField

attribute [local instance] Ideal.Quotient.field in
theorem solution
    {G : Type*} [Group G] {ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G} {q : ℕ}
    (hq : q.Prime) (hunr : GlobalGaloisRep.IsUnramifiedAt ρ q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hfix : ρ.ker ≤ F.fixingSubgroup)
    (P : Ideal (NumberField.RingOfIntegers F)) [P.IsMaximal] (hqP : (q : NumberField.RingOfIntegers F) ∈ P) :
    Algebra.IsUnramifiedAt ℤ P := by
  classical
  haveI : NumberField F := NumberField.mk

  have htriv : ∀ τ ∈ P.inertia (F ≃ₐ[ℚ] F), τ = 1 := by
    intro τ hτ
    obtain ⟨σ, hστ, 𝔔, h𝔔max, hq𝔔, hσ𝔔⟩ :=
      NumberField.exists_lift_mem_inertia_integralClosure F P hqP τ hτ
    haveI := h𝔔max
    obtain ⟨A, hA, hσA⟩ :=
      ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn 𝔔 hq hq𝔔 σ hσ𝔔
    have hσker : σ ∈ ρ.ker := hunr A hA hσA
    have hσfix : σ ∈ F.fixingSubgroup := hfix hσker
    rw [← hστ]
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    have hc := AlgEquiv.restrictNormal_commutes σ F x
    change ((σ.restrictNormal F x : F) : AlgebraicClosure ℚ) = ((x : F) : AlgebraicClosure ℚ)
    have h2 : ((σ.restrictNormal F x : F) : AlgebraicClosure ℚ) =
        algebraMap F (AlgebraicClosure ℚ) (σ.restrictNormal F x) := rfl
    rw [h2, hc]
    exact (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσfix x x.2
  have hbot : P.inertia (F ≃ₐ[ℚ] F) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr htriv

  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (NumberField.RingOfIntegers.not_isField F)
  have hp0 : P.under ℤ ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0
  haveI : (P.under ℤ).IsMaximal := Ideal.IsMaximal.under ℤ P
  haveI : P.LiesOver (P.under ℤ) := ⟨rfl⟩
  have : Finite (ℤ ⧸ P.under ℤ) := Ring.HasFiniteQuotients.finiteQuotient hp0
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  have c1 := Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[ℚ] F) (P.under ℤ) P
  rw [hbot, Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P (F ≃ₐ[ℚ] F),
    Subgroup.card_bot] at c1
  exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.mpr c1.symm

end S_GlobalGaloisRep_IsUnramifiedAt_algebraIsUnramifiedAt_of_ker_le_fixingSubgroup
end P2MW
export P2MW.S_GlobalGaloisRep_IsUnramifiedAt_algebraIsUnramifiedAt_of_ker_le_fixingSubgroup (solution)
