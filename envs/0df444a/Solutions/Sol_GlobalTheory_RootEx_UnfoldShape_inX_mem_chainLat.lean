-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.inX_mem_chainLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:08.862293+00:00
-- url     : https://prove2.me/submissions/5112891f-c098-4d6c-b536-d969f8375a20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_chainLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n]
namespace GlobalTheory.RootEx.UnfoldShape
namespace _root_.GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {ϖ : 𝒪[k]} {L : Submodule 𝒪[k] (n → k)} {v : n → k} :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX k n c v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ c L ↔ v ∈ L := by
  rw [_root_.GlobalTheory.RootEx.UnfoldShape.mem_chainLat]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i => ⟨0, by simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX]⟩⟩⟩
end _root_.GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape
