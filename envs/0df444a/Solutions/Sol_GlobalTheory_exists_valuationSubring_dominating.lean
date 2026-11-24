-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_dominating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:57.782917+00:00
-- url     : https://prove2.me/submissions/2f53a532-ba83-4c9d-8a0f-7c8accbf507d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {V K K' : Type*} [CommRing V] [Field K] [Field K']
namespace GlobalTheory
theorem _root_.solution [IsDomain V] [ValuationRing V] [Algebra V K]
    [IsFractionRing V K] (χ : K →+* K') :
    ∃ (V' : ValuationSubring K') (ψ : V →+* V'), IsLocalHom ψ ∧
      (∀ a, (ψ a : K') = χ (algebraMap V K a)) ∧
      ∀ x : K, χ x ∈ V' ↔ x ∈ (algebraMap V K).range := by
  obtain ⟨V', h, hl⟩ := IsLocalRing.exists_factor_valuationRing (χ.comp (algebraMap V K))
  exact ⟨V', _, hl, fun _ ↦ rfl,
    @mem_iff_mem_range_of_isLocalHom _ _ _ _ _ _ _ _ _ _ χ V' _ hl fun _ ↦ rfl⟩
end GlobalTheory
