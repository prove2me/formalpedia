-- Prove2me | solution 1 for IsLocalRing.exists_ringHom_range_comp_rangeRestrict_eq_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d94e5ffc-45eb-558f-8f30-9b6b8b4f767f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ringHom_range_comp_rangeRestrict_eq_of_surjective

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R]
    {k : Type*} [Field k] (π : R →+* k) (hπ : Function.Surjective π)
    {K : Type*} [Field K] (φ : R →+* K) :
    ∃ ρ : φ.range →+* k, ∀ r : R, ρ (φ.rangeRestrict r) = π r := by
  have hker : RingHom.ker φ ≤ RingHom.ker π := by
    have hmax : (RingHom.ker π).IsMaximal := RingHom.ker_isMaximal_of_surjective π hπ
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  refine ⟨φ.rangeRestrict.liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨π, ?_⟩, fun r => ?_⟩
  · intro x hx
    apply hker
    rw [RingHom.mem_ker] at hx ⊢
    have := congrArg Subtype.val hx
    simpa using this
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ r

end S_IsLocalRing_exists_ringHom_range_comp_rangeRestrict_eq_of_surjective
end P2MW
export P2MW.S_IsLocalRing_exists_ringHom_range_comp_rangeRestrict_eq_of_surjective (solution)
