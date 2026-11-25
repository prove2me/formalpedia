-- Prove2me | solution 1 for GroundTheory.LocalField.eq_adicCompletionAlgEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:59:30.839741+00:00
-- url     : https://prove2.me/submissions/c2fc8bc7-7945-4af2-b287-38a2e7cd04ed

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
import Theorems.Thm_GroundTheory_LocalField_ringHom_ext_adicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open IsLocalRing ValuativeRel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "𝔅" => AdicCompletion (maximalIdeal R) R
variable {S : Type*} [CommRing S] [Algebra S R]
namespace GroundTheory.LocalField
theorem _root_.solution (θ : R ≃ₐ[S] R) {τ : 𝔅 →+* 𝔅}
    (hτ : ∀ r, τ (algebraMap R 𝔅 r) = algebraMap R 𝔅 (θ r)) :
    τ = (adicCompletionAlgEquiv θ : 𝔅 →+* 𝔅) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ringHom_ext_adicCompletion hϖ (fun r ↦ ?_) ?_
  · rw [hτ]
    exact (adicCompletionAlgEquiv_algebraMap θ r).symm
  · rw [hτ, AdicCompletion.maximalIdeal_eq_map]
    refine Ideal.mem_map_of_mem _ ?_
    exact maximalIdeal_le_comap_ringEquiv θ.toRingEquiv (hϖ.maximalIdeal_eq ▸
      Ideal.mem_span_singleton_self ϖ)
end GroundTheory.LocalField
