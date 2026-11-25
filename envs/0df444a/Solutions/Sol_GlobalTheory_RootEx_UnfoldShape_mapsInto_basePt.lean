-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.mapsInto_basePt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:38.648942+00:00
-- url     : https://prove2.me/submissions/26ba0d27-6bf7-4244-af1d-eb7525c02d44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_chainLat
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_basePt_mulVec

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
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [Fintype n]
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {ϖ : 𝒪[k]} {L' : Submodule 𝒪[k] (n' → k)} {L : Submodule 𝒪[k] (n → k)}
    {x₀ : Matrix n n' k} (h : MapsInto x₀ L' L) :
    MapsInto (basePt c x₀) (chainLat ϖ (c + 1) L') (chainLat ϖ c L) := by
  intro v hv
  rw [basePt_mulVec, mem_chainLat]
  obtain ⟨h1, h2⟩ := mem_chainLat.1 hv
  exact ⟨h _ h1, fun i => h2 i.castSucc⟩
end GlobalTheory.RootEx.UnfoldShape
