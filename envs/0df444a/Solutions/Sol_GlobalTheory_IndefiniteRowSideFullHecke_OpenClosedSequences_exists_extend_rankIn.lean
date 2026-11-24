-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.exists_extend_rankIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:02.735258+00:00
-- url     : https://prove2.me/submissions/799840b1-5058-4e7d-b6b6-b4157b5254cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenSetOfLeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RankFiltrationExists
import Theorems.Thm_GlobalTheory_SBExtend_exists_extension
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball


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
omit [DecidableEq a] [DecidableEq b]
namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
theorem _root_.solution {s : Set ℕ} {κ n : ℕ} (hs : ∀ r ∈ s, κ ≤ r ∧ r < n) (f : SB (RankIn k a b s)) :
    ∃ F : SB (RankIn k a b (Set.Iio n)), (∀ x : RankIn k a b (Set.Iio n), x.1.rank < κ → F.1 x = 0) ∧
      ∀ x : RankIn k a b s, F.1 ⟨x.1, (hs _ x.2).2⟩ = f.1 x := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix b a k) :=
    inferInstanceAs (TotallyDisconnectedSpace (b → a → k))
  have : LocallyCompactSpace (Matrix b a k) := inferInstanceAs (LocallyCompactSpace (b → a → k))
  obtain ⟨G, hG, hG0⟩ := GlobalTheory.SBExtend.exists_extension (Matrix b a k) {x | κ ≤ x.rank} {x | x.rank ∈ s} (isOpen_le_rank κ)
    (fun x hx => (hs _ hx).1) f
  refine ⟨⟨fun y => G.1 y.1, comp_mem_SB_of_isInducing IsInducing.subtypeVal G (isClosed_rank_lt n)
    (fun y => y.2) fun x hx _ => ⟨⟨x, hx⟩, rfl⟩⟩, fun x hx => hG0 _ (not_le.2 hx), fun x => hG x⟩
end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
