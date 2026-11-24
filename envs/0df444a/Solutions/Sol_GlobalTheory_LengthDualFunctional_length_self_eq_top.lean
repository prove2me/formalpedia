-- Prove2me | solution 1 for GlobalTheory.LengthDualFunctional.length_self_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:40:06.076975+00:00
-- url     : https://prove2.me/submissions/d372b7b1-90cc-4b47-9b01-50c6d61514af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsDualNeZeroCompEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthDualFunctional
open Module
namespace GlobalTheory.LengthDualFunctional
theorem _root_.solution (R : Type u_1) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Module.length R R = ⊤ := by
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨_, hA⟩ := hne
  haveI : IsArtinianRing R := hA
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)
end GlobalTheory.LengthDualFunctional
