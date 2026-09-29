-- Prove2me | solution 1 for IntermediateField.adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/37d3f5be-27e5-5247-862a-4d229a2c8797

import Mathlib
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

local instance S25CYCLEV.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (k : ℕ)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    (IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))).IsUnramifiedOutside S := by
  have hp : p.Prime := Fact.out
  refine ⟨IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral,
    fun q hq A hA σ hσ => ?_⟩

  have hqp : ¬ (q : ℕ) ∣ p ^ (k + 1) := fun h => hq (by
    have h1 : (q : ℕ) = p := (Nat.prime_dvd_prime_iff_eq q.2 hp).1 (q.2.dvd_of_dvd_pow h)
    have : q = pPrime p := Subtype.ext h1
    rw [this]; exact hpS)
  have hfix : σ ζ = ζ :=
    ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one A q.2 hA hσ hqp hζ.pow_eq_one

  have hle : IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) ≤
      IntermediateField.fixedField (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ) :=
    IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 fun τ => τ.2)
  exact (IntermediateField.le_iff_le _ _).1 hle (MulAction.mem_stabilizer_iff.2 hfix)

end S_IntermediateField_adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow
end P2MW
export P2MW.S_IntermediateField_adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow (solution)
