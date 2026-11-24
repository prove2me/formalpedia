-- Prove2me | solution 1 for GlobalTheory.T.clears_idempotent_of_trace_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:22.905835+00:00
-- url     : https://prove2.me/submissions/16cfb737-7300-4b8a-8285-d8b710142adb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfTraceDual
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfTraceDualStatement
import Theorems.Thm_GlobalTheory_DualCrit_clearsIdem_top_of_dual


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], Nat.card (E →+* K) = Module.finrank ℚ E → ∀ D : O, (∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y) → ClearsIdem K (⊤ : Ideal (OF E)) D := by
  first | exact @GlobalTheory.DualCrit.clearsIdem_top_of_dual | exact GlobalTheory.DualCrit.clearsIdem_top_of_dual | (intros; apply GlobalTheory.DualCrit.clearsIdem_top_of_dual <;> assumption)
end _root_.GlobalTheory.T
