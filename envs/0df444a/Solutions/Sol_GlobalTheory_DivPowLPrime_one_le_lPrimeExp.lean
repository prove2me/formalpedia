-- Prove2me | solution 1 for GlobalTheory.DivPowLPrime.one_le_lPrimeExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:54.73065+00:00
-- url     : https://prove2.me/submissions/2a5de2b6-2ab5-47ee-acf2-7beb353e51d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DivPowLPrime
namespace GlobalTheory.DivPowLPrime
theorem _root_.solution (l : ℕ) : 1 ≤ lPrimeExp l := by
  unfold lPrimeExp; split_ifs <;> norm_num
end GlobalTheory.DivPowLPrime
