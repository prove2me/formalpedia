-- Prove2me | solution 1 for GlobalTheory.Chow.isBlockHomogeneous_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:51.383813+00:00
-- url     : https://prove2.me/submissions/13c1b9da-5f90-4b8f-8264-c500d5a6d5e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*}
variable [DecidableEq β] [DecidableEq β']
namespace GlobalTheory.Chow
theorem _root_.solution [Fintype σ] (u : σ → K) (i : β) :
    IsBlockHomogeneous (linForm u i) (Pi.single i 1) :=
  IsWeightedHomogeneous.sum _ _ _ fun j _ =>
    (isWeightedHomogeneous_X K blockWeight (i, j)).C_mul _
end GlobalTheory.Chow
