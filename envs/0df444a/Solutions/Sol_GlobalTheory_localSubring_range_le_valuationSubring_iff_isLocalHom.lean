-- Prove2me | solution 1 for GlobalTheory.localSubring_range_le_valuationSubring_iff_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:25.342807+00:00
-- url     : https://prove2.me/submissions/a5c10a10-0ac4-4f2b-83d4-6a70b319c22c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff

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
theorem _root_.solution (f : R →+* L)
    (V : ValuationSubring L) :
    LocalSubring.range f ≤ V.toLocalSubring ↔
      ∃ h : ∀ r, f r ∈ V, IsLocalHom (f.codRestrict V h) := by
  rw [localSubring_range_le_valuationSubring_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ⟨fun r hu => ?_⟩⟩
    by_contra hn
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f r, h1 r⟩)).mp (h2 r hn) hu
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun r hr => ?_⟩
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f r, h1 r⟩)).mpr fun hu => hr (h2.1 r hu)
end GlobalTheory
