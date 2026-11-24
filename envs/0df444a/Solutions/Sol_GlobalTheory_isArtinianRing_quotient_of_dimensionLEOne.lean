-- Prove2me | solution 1 for GlobalTheory.isArtinianRing_quotient_of_dimensionLEOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:25.653478+00:00
-- url     : https://prove2.me/submissions/a1360705-ed4f-43b1-8bb9-84cc4a9a2dd3

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
variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
namespace GlobalTheory
theorem _root_.solution {I : Ideal A} (hI : I ≠ ⊥) :
    IsArtinianRing (A ⧸ I) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h1 : (p.comap (Ideal.Quotient.mk I)).IsMaximal := by
    refine Ring.DimensionLEOne.maximalOfPrime ?_ inferInstance
    intro h
    apply hI
    rw [eq_bot_iff, ← h]
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective h1 with h | h
  · exact absurd (h2 ▸ h) hp.ne_top
  · exact h2 ▸ h
end GlobalTheory
