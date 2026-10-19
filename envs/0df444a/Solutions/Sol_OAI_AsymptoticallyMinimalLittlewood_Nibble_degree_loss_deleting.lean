-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.degree_loss_deleting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:46:07.220977+00:00
-- url     : https://prove2.me/submissions/cab85e2e-3319-4a0c-9b37-533328a6c61f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Nibble.lean:L271-L302
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.degree_loss_deleting. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble

-- ---- from OAI.Analysis.Littlewood.Nibble ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uE uV

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset
section SetUnions
variable {I : Type uI} {E : Type uE} [DecidableEq I] [DecidableEq E]

omit [DecidableEq I] in
lemma card_biUnion_upper (S : Finset I) (A : I → Finset E) {D : ℝ}
    (hD : ∀ i ∈ S, ((A i).card : ℝ) ≤ D) :
    ((S.biUnion A).card : ℝ) ≤ S.card * D := by
  calc
    _ ≤ ∑ i ∈ S, ((A i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ S, D := Finset.sum_le_sum hD
    _ = _ := by simp

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
lemma incident_restrict (S : Finset E) (A : E → Finset V) (W : Finset V) (v : V) :
    incident (restrictEdges S A W) A v = (incident S A v).filter fun e ↦ A e ⊆ W := by
  ext e
  simp [incident, restrictEdges, and_left_comm, and_comm]

omit [Fintype E] in
lemma degree_loss_deleting (U B : Finset V) (S : Finset E) (A : E → Finset V)
    {C : ℝ} (_hC : 0 ≤ C) (hsub : ∀ e ∈ S, A e ⊆ U)
    (v : V) (hc : ∀ w ∈ B, v ≠ w → ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (hv : v ∉ B) :
    ((incident S A v).card : ℝ) - B.card*C ≤
      ((incident (restrictEdges S A (U \ B)) A v).card : ℝ) := by
  classical
  have hd : incident S A v \ incident (restrictEdges S A (U \ B)) A v ⊆
      B.biUnion (fun w ↦ incident S A v ∩ incident S A w) := by
    intro e he
    obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp he
    have hin := mem_incident S A v e |>.mp he
    have hnon : ¬ A e ⊆ U \ B := by
      intro h
      apply hn
      rw [incident_restrict]
      exact Finset.mem_filter.mpr ⟨he, h⟩
    obtain ⟨w, hw, hwB⟩ := Finset.not_subset.mp hnon
    have hwB' : w ∈ B := by simpa [Finset.mem_sdiff, hsub e hin.1 hw] using hwB
    exact Finset.mem_biUnion.mpr ⟨w, hwB', Finset.mem_inter.mpr
      ⟨he, mem_incident S A w e |>.mpr ⟨hin.1, hw⟩⟩⟩
  have hb := (show (((incident S A v \ incident (restrictEdges S A (U \ B)) A v).card) : ℝ) ≤
      (B.biUnion (fun w ↦ incident S A v ∩ incident S A w)).card from
        Nat.cast_le.mpr (Finset.card_le_card hd)).trans
    (card_biUnion_upper B _ (fun w hw ↦ hc w hw (fun h ↦ hv (h ▸ hw))))
  have hcard := Finset.card_le_card_sdiff_add_card (s := incident S A v)
    (t := incident (restrictEdges S A (U \ B)) A v)
  have hcard' : ((incident S A v).card : ℝ) ≤
    (incident S A v \ incident (restrictEdges S A (U \ B)) A v).card +
      (incident (restrictEdges S A (U \ B)) A v).card := by exact_mod_cast hcard
  linarith

namespace PackingState

end PackingState

open Filter Topology

end Hypergraph

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
open scoped BigOperators
open Finset


theorem solution.{uE,uV} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.degree_loss_deleting.{uE,uV} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.degree_loss_deleting.{uE,uV}
