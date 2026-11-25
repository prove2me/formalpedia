-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.resFilt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:12.783429+00:00
-- url     : https://prove2.me/submissions/f3335eab-4bff-4f14-8d12-71a108f6ebdd

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
theorem _root_.solution (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n) (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m)
    (Φ : (filt a b μ (Set.Iio n) κ).toSubmodule) (x : RankIn k a b s) :
    (resFilt μ hmn hs Φ).1 x = Φ.1.1 ⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩ := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
