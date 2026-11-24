-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.ker_resFilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:47.409855+00:00
-- url     : https://prove2.me/submissions/27ba2f03-e9d7-4c8b-b5cb-ae6e987d0935

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenSetOfLeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RankFiltrationExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
theorem _root_.solution (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n)
    (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) (Φ : (filt a b μ (Set.Iio n) κ).toSubmodule) :
    resFilt μ hmn hs Φ = 0 ↔ Φ.1 ∈ (filt a b μ (Set.Iio n) m).toSubmodule := by
  constructor
  · intro h x hx
    by_cases hκ : x.1.rank < κ
    · exact Φ.2 x hκ
    · exact congrFun (congrArg Subtype.val h) ⟨x.1, (hs _).2 ⟨not_lt.1 hκ, hx⟩⟩
  · intro h
    exact Subtype.ext (funext fun x => h _ ((hs _).1 x.2).2)
end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
