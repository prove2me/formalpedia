-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:29:14.913429+00:00
-- url     : https://prove2.me/submissions/a0384f8a-1cb9-4709-bcfd-52c2b90aef0e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/MultiplierLaw.lean:L22-L34
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_smul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw

-- ---- from OAI.Combinatorics.CliqueFree.Optimizer ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

lemma edgeForm_self (G : SimpleGraph V) (a : V → ℝ) : edgeForm G a a = 2 * edgeMass G a := by
  simp only [edgeForm,edgeMass,crossMass]
  ring

end CliqueFreeIndependence.WeightedGraph

end

end OAI

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

lemma edgeMass_smul (G : SimpleGraph V) (w : V → ℝ) (a : ℝ) :
    edgeMass G (fun v ↦ a*w v) = a^2 * edgeMass G w := by
  have h : edgeForm G (fun v ↦ a*w v) (fun v ↦ a*w v) = a^2*edgeForm G w w := by
    unfold edgeForm
    rw [mul_sum]
    apply sum_congr rfl
    intro u _
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    split_ifs <;> ring
  rw [edgeForm_self,edgeForm_self] at h
  linarith

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


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_smul.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_smul.{u}
