-- Prove2me | solution 1 for OAI.GreedyPacking.exists_packing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:12:11.316968+00:00
-- url     : https://prove2.me/submissions/a928a887-d715-44c3-92b8-f20416676e1a

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching

open OAI
universe uAlpha uE uV
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical
variable {α : Type uAlpha}


theorem solution (t : Finset α) (R : α → α → Prop)
    (hrefl : ∀ a ∈ t, R a a) (hsym : ∀ a ∈ t, ∀ b ∈ t, R a b → R b a)
    (M : ℕ) (hM : ∀ a ∈ t, (t.filter (R a)).card ≤ M) :
    ∃ s : Finset α, s ⊆ t ∧ (s : Set α).Pairwise (fun a b => ¬R a b) ∧ t.card ≤ M*s.card := by
  classical
  induction h : t.card using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    rcases t.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp at h; omega⟩
    · set t' := t.filter (fun b => ¬ R a b) with ht'
      have hcard : (t.filter (R a)).card + t'.card = t.card :=
        Finset.card_filter_add_card_filter_not _
      have hlt : t'.card < n := by
        have : 0 < (t.filter (R a)).card :=
          Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hrefl a ha⟩⟩
        omega
      have ht't : t' ⊆ t := Finset.filter_subset _ _
      obtain ⟨s', hs't', hs'p, hs'c⟩ := ih _ hlt t'
        (fun b hb => hrefl b (ht't hb))
        (fun b hb c hc => hsym b (ht't hb) c (ht't hc))
        (fun b hb => (Finset.card_le_card (Finset.filter_subset_filter _ ht't)).trans (hM b (ht't hb)))
        rfl
      have haS : a ∉ s' := by
        intro has
        have := (Finset.mem_filter.mp (hs't' has)).2
        exact this (hrefl a ha)
      refine ⟨insert a s', Finset.insert_subset ha (hs't'.trans ht't), ?_, ?_⟩
      · rw [Finset.coe_insert]
        refine Set.Pairwise.insert hs'p (fun b hb _ => ⟨?_, ?_⟩)
        · exact (Finset.mem_filter.mp (hs't' hb)).2
        · intro hba
          exact (Finset.mem_filter.mp (hs't' hb)).2 (hsym b (ht't (hs't' hb)) a ha hba)
      · rw [Finset.card_insert_of_notMem haS]
        have := hM a ha
        nlinarith

