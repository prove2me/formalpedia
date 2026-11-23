-- Prove2me | solution 1 for GlobalTheory.DivPowLPrime.lPrime_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:34.732204+00:00
-- url     : https://prove2.me/submissions/66d730de-3e99-4404-8f67-603c3364adaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DivPowLPrime
namespace GlobalTheory.DivPowLPrime
theorem _root_.solution (l : ℕ) : lPrime l = l ^ lPrimeExp l := by
  unfold lPrime lPrimeExp; split_ifs with h <;> simp [h]
end GlobalTheory.DivPowLPrime
