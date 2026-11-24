-- Prove2me | solution 1 for GlobalTheory.isAffine_of_isAffine_pullback_quotient_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:20.141117+00:00
-- url     : https://prove2.me/submissions/ff1d8c5a-9171-4aa8-b979-748587716787

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_isAffine_of_isPullback_of_isNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (A : Type) [CommRing A]
    (J : Ideal A) (hJ : IsNilpotent J) (Y : Over (Spec (CommRingCat.of A)))
    (h : IsAffine (pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))) :
    IsAffine Y.left :=
  AffineThickening.isAffine_of_isPullback_of_isNilpotent J hJ _ Ideal.Quotient.mk_surjective
    Ideal.mk_ker (IsPullback.of_hasPullback _ _) h
end GlobalTheory
