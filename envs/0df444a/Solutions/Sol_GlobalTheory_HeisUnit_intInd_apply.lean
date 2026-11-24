-- Prove2me | solution 1 for GlobalTheory.HeisUnit.intInd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:26:15.94905+00:00
-- url     : https://prove2.me/submissions/be505592-e0f4-410f-8cc5-b3f1f0236eb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubInvMulOutMemIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
open GlobalTheory GlobalTheory.HeisUnit
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open Classical
namespace GlobalTheory.HeisUnit
theorem _root_.solution {n d : ℕ} (M : Matrix (Fin n) (Fin d) k) :
    intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by
  classical
  simp only [intInd, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
end GlobalTheory.HeisUnit
