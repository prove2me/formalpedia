-- Prove2me | solution 1 for GlobalTheory.LowerOps.act_of_mem_eigK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:10:26.444506+00:00
-- url     : https://prove2.me/submissions/932c9e7d-5cf2-44c1-899b-8163b943ac57

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
theorem _root_.solution {ρ : orderC c →+* Module.End O H} {σ : E →+* K} {x : K ⊗[O] H}
    (hx : x ∈ eigK ρ σ) (a : orderC c) : (ρ a).baseChange K x = σ a • x :=
  Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx a)
end GlobalTheory.LowerOps
