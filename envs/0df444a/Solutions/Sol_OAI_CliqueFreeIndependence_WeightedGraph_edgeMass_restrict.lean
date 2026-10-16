-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:30:56.422242+00:00
-- url     : https://prove2.me/submissions/fed25c5b-dd52-4921-8b94-101e9ae116e8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/MultiplierLaw.lean:L36-L57
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_restrict. The node keeps its source
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

lemma edgeMass_restrict (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    edgeMass G (restrict A w) = crossMass G w A A / 2 := by
  classical
  unfold edgeMass crossMass restrict
  congr 1
  calc
    _ = ∑ u, ∑ v, if u ∈ A ∧ v ∈ A then (if G.Adj u v then w u*w v else 0) else 0 := by
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp [hu,hv]
    _ = _ := by
      simp only [ite_and]
      simp_rw [sum_ite_irrel]
      simp only [sum_const_zero]
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter]
      apply sum_congr rfl
      intro u hu
      rw [← sum_filter]
      simp

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


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_restrict.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_restrict.{u}
