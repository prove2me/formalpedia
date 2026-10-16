-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.normalize_subprob
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:33:35.596644+00:00
-- url     : https://prove2.me/submissions/2f819311-d524-473c-9df5-1f3acc413daf

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/MultiplierLaw.lean:L118-L137
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.normalize_subprob. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw

-- ---- from OAI.Combinatorics.CliqueFree.MultiplierLaw ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence
universe u
namespace WeightedGraph
open Lottery
variable {V : Type u} [Fintype V]

lemma normalize_subprob (G : SimpleGraph V) (w : V → ℝ) {L : Law (V → ℝ)}
    (hL : Positive L) (hsum : total L ≤ 1) {A : Finset V} {b : ℝ} (hb : 0 ≤ b)
    (hbL : BoundedOn L A b) :
    ∃ K : Law (V → ℝ), IsProb K ∧ BoundedOn K A b ∧
      (∀ v, expect K (fun m ↦ m v) = expect L (fun m ↦ m v)) ∧
      expectedEdges G w K = expectedEdges G w L := by
  let K : Law (V → ℝ) := (1-total L,0)::L
  refine ⟨K,⟨?_,?_⟩,?_,?_,?_⟩
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact sub_nonneg.2 hsum
    · exact hL z hz
  · simp [K,total,expect_cons]
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨fun _ ↦ ⟨le_rfl,hb⟩,fun _ _ ↦ rfl⟩
    · exact hbL z hz
  · intro v
    simp [K]
  · simp [K,expectedEdges,edgeMass,crossMass]

end WeightedGraph
end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Lottery


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.normalize_subprob.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.normalize_subprob.{u}
