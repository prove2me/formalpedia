-- Prove2me | solution 1 for GlobalTheory.localSubring_range_le_valuationSubring_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:52.822793+00:00
-- url     : https://prove2.me/submissions/2a8645f2-94c8-4f27-b315-21d720521ef0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]
namespace GlobalTheory
theorem _root_.solution (f : R →+* L) (V : ValuationSubring L) :
    LocalSubring.range f ≤ V.toLocalSubring ↔
      (∀ r, f r ∈ V) ∧ ∀ r ∈ maximalIdeal R, f r ∈ V.nonunits := by
  have hl : IsLocalHom f.rangeRestrict := .of_surjective _ f.rangeRestrict_surjective
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r => h1 ⟨r, rfl⟩, fun r hr => ?_⟩
    refine (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f r, h1 ⟨r, rfl⟩⟩)).mpr fun hu => hr ?_
    exact hl.1 r (h2.1 _ hu)
  · rintro ⟨h1, h2⟩
    refine ⟨by rintro _ ⟨r, rfl⟩; exact h1 r, ⟨?_⟩⟩
    rintro ⟨_, r, rfl⟩ hu
    by_contra hn
    have hr : r ∈ maximalIdeal R := fun h => hn (h.map f.rangeRestrict)
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f r, h1 r⟩)).mp (h2 r hr) hu
end GlobalTheory
