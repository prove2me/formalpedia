-- Prove2me | solution 1 for GlobalTheory.IndexCol.mem_maximalIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:43.705573+00:00
-- url     : https://prove2.me/submissions/86a06c0d-6b1e-4cc6-a27d-a552b8a8109a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndexCol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.IndexCol
theorem _root_.solution (a : 𝒪[k]) :
    a ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (a : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
end GlobalTheory.IndexCol
