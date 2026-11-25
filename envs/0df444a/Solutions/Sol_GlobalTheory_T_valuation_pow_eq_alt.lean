-- Prove2me | solution 1 for GlobalTheory.T.valuation_pow_eq_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:45.736737+00:00
-- url     : https://prove2.me/submissions/09ce1af9-5b80-44c7-b337-00d5edcb54e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValVpNatCastPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValVpNatCastPowStatement
import Theorems.Thm_GlobalTheory_val_vp_natCast_pow


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], ∀ (l : ℕ), l ≠ 0 → (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ k : ℕ, val_vp O l (algebraMap O K ((l : O) ^ k)) = ((k : ℚ) : WithTop ℚ) := by
  first | exact @GlobalTheory.val_vp_natCast_pow | exact GlobalTheory.val_vp_natCast_pow | (intros; apply GlobalTheory.val_vp_natCast_pow <;> assumption)
end _root_.GlobalTheory.T
