-- Prove2me | solution 1 for GlobalTheory.PlaceOver.isOpen_valuation_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:42.0798+00:00
-- url     : https://prove2.me/submissions/51c981c3-5d64-4863-9e8b-804d1f2ce4bf

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapEqOfContinuousAdicCompletionIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.PlaceOver
open Filter Topology
namespace GlobalTheory.PlaceOver
theorem _root_.solution {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) :
    IsOpen {z : P.adicCompletion F | Valued.v z < 1} := by
  have h := Valued.isOpen_ball (P.adicCompletion F) 1
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using h
end GlobalTheory.PlaceOver
