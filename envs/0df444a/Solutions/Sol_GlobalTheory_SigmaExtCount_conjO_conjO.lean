-- Prove2me | solution 1 for GlobalTheory.SigmaExtCount.conjO_conjO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:48:09.905959+00:00
-- url     : https://prove2.me/submissions/fc4e6fef-4582-4dfb-8b8d-7e70dad56124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.SigmaExtCount
open GlobalTheory.UnitLemma
namespace GlobalTheory.SigmaExtCount
theorem _root_.solution (K : UQ) (o : K.O) : conjO K (conjO K o) = o :=
  IsFractionRing.injective K.O K.E (by rw [algebraMap_conjO, algebraMap_conjO, K.c_c])
end GlobalTheory.SigmaExtCount
