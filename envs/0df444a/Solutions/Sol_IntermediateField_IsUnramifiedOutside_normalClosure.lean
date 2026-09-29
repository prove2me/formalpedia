-- Prove2me | solution 1 for IntermediateField.IsUnramifiedOutside.normalClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/147e8ef5-fa23-5f4e-a263-a60ed3c18489

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_IsUnramifiedOutside_normalClosure

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open scoped Pointwise

namespace IntermediateField p2m_export "IntermediateField" "smul_def mem_fixingSubgroup_iff le_iff_le fixingSubgroup fixingSubgroup_antitone mem_map normalClosure_def'' normal map normalClosure IsUnramifiedOutside" end IntermediateField
p2m_open_scoped "IntermediateField" in

private theorem IntermediateField.le_fixingSubgroup_iSup_of_forall_le_NC {ι : Sort*}
    (E : ι → IntermediateField ℚ (AlgebraicClosure ℚ))
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (h : ∀ i, H ≤ (E i).fixingSubgroup) : H ≤ (⨆ i, E i).fixingSubgroup := by
  rw [← IntermediateField.le_iff_le, iSup_le_iff]
  exact fun i => (IntermediateField.le_iff_le _ _).2 (h i)

namespace ValuationSubring p2m_export "ValuationSubring" "mem_nonunits_iff_or mem_pointwise_smul_iff_inv_smul_mem LiesOverPrime inertiaSubgroupIn conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul" end ValuationSubring
p2m_open_scoped "ValuationSubring" in

private theorem ValuationSubring.liesOverPrime_smul_NC {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ}
    (hA : A.LiesOverPrime q) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (g • A).LiesOverPrime q := by
  rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff_or] at hA ⊢
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_natCast]
  exact hA

theorem solution
    {S : Finset Nat.Primes} {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) :
    (IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)).IsUnramifiedOutside S := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ F := hF.1

  refine ⟨inferInstance, fun q hq A hA => ?_⟩

  have key : A.inertiaSubgroupIn ℚ ≤
      (⨆ g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        F.map (g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)).fixingSubgroup := by
    refine IntermediateField.le_fixingSubgroup_iSup_of_forall_le_NC _ _ fun g => ?_
    intro σ hσ

    have hA' : (g⁻¹ • A).LiesOverPrime q := ValuationSubring.liesOverPrime_smul_NC hA g⁻¹
    have hσ' : σ ∈ (g • (g⁻¹ • A)).inertiaSubgroupIn ℚ := by rwa [smul_inv_smul]
    have hmem := hF.2 q hq (g⁻¹ • A) hA'
      (ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul _ g hσ')
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (IntermediateField.mem_map F).1 hy
    have hgx := congrArg g (hmem x hx)
    simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at hgx
    simpa using hgx
  exact key.trans (IntermediateField.fixingSubgroup_antitone (IntermediateField.normalClosure_def'' F).le)

end S_IntermediateField_IsUnramifiedOutside_normalClosure
end P2MW
export P2MW.S_IntermediateField_IsUnramifiedOutside_normalClosure (solution)
