-- Prove2me | solution 1 for GlobalTheory.specialLinearGroup_map_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:51.275177+00:00
-- url     : https://prove2.me/submissions/f1ba0196-fafd-4dc5-ac6f-08d9fb92d6d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_liftsToDetOne_of_det_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
namespace GlobalTheory
theorem _root_.solution [Finite (MaximalSpectrum R)] (hf : Surjective f) :
    Surjective (SpecialLinearGroup.map (n := n) f) := fun A => by
  obtain ⟨B, hB, h⟩ := liftsToDetOne_of_det_eq_one hf A.2
  exact ⟨⟨B, hB⟩, Subtype.ext h⟩
end GlobalTheory
