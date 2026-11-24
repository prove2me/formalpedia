-- Prove2me | solution 1 for GlobalTheory.DI.frobLiftPhi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:54.630378+00:00
-- url     : https://prove2.me/submissions/88020013-72b6-4361-95e7-2a002a8eea04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehlerStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobLiftPsiNatCastMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K]
variable {Kt : Type} [CommRing Kt] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (π : Kt →+* K) (F : Kt →+* Kt)
variable {p π F}
namespace GlobalTheory.DI
theorem _root_.solution (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    frobLiftPhi hL hF (π z) = frobLiftPsi p π F hL hF z :=
  frobLiftPsi_congr hL hF (Function.surjInv_eq hL.surj _)
end GlobalTheory.DI
