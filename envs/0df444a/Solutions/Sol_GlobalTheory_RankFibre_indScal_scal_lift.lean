-- Prove2me | solution 1 for GlobalTheory.RankFibre.indScal_scal_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:10:16.243174+00:00
-- url     : https://prove2.me/submissions/196fba91-32bc-4e70-919a-f2dbbe334596

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InducedScalarIrreducible
import Theorems.Thm_GlobalTheory_RankFibre_indScal_lift_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RankFibre
theorem _root_.solution (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    indScalVal ν β a b (indScalLift ν β a b hf) = f :=
  funext (indScal_lift_apply ν β a b hf)
end GlobalTheory.RankFibre
