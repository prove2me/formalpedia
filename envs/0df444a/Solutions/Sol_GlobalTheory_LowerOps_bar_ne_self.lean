-- Prove2me | solution 1 for GlobalTheory.LowerOps.bar_ne_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:52:02.992311+00:00
-- url     : https://prove2.me/submissions/f17842c8-e0cf-4503-88fb-a0418eb9d8a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegral

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
open GlobalTheory GlobalTheory.LowerOps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.LowerOps
theorem _root_.solution (σ : E →+* K) : bar σ ≠ σ := by
  intro h
  apply IsCMField.complexConj_ne_one E
  ext x
  exact σ.injective (congrArg (fun τ : E →+* K => τ x) h)
end GlobalTheory.LowerOps
