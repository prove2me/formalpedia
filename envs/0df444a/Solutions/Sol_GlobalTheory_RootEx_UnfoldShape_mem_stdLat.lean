-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:11.203988+00:00
-- url     : https://prove2.me/submissions/5432bcb9-74cf-4353-a063-1c27978cedfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice

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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.UnfoldShape
namespace _root_.GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {v : ι → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.stdLat k ι ↔ ∀ i, v i ∈ 𝒪[k] := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
    Submodule.mem_one]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨v i, h⟩, rfl⟩⟩
  rintro ⟨a, ha⟩
  rw [← ha]
  exact a.2
end _root_.GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape
