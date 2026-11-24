-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinPresDescent.finiteType_of_finite_projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:36.418925+00:00
-- url     : https://prove2.me/submissions/43399bc3-027a-4fd7-acc4-acf57ebc15a4

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_FiniteTypeDescent_main__3dbb7f300c14
import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRetr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FinitePresentationOfFaithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinPresDescent
namespace GlobalTheory.CompanionTheory.FinPresDescent
theorem _root_.solution (R C D : Type*) [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D]
    [Module.Finite C D] [Module.Projective C D] (hinj : Function.Injective (algebraMap C D))
    [Algebra.FiniteType R D] : Algebra.FiniteType R C :=
  _root_.P2M_UpperTheory_Reformulated_B_FiniteTypeDescent_main__3dbb7f300c14 R C D hinj
end GlobalTheory.CompanionTheory.FinPresDescent
