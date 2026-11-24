-- Prove2me | solution 1 for GlobalTheory.TwistVertex.simpleSum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:35.65931+00:00
-- url     : https://prove2.me/submissions/90d90a49-ba85-44fd-8920-cf441aab4e3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwist
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.TwistVertex
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.TwistVertex
theorem _root_.solution {u : GL (n ⊕ Fin c) k} (hu : u ∈ KO k (n ⊕ Fin c)) : simpleSum u ∈ 𝒪[k] := by
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  split_ifs
  · exact intM_of_mem_KO hu _ _
  · exact zero_mem _
end GlobalTheory.TwistVertex
