-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.optimizer_deletion_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:36:27.059104+00:00
-- url     : https://prove2.me/submissions/189cab85-4279-49ef-8f0a-261c04401648

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Deletion.lean:L62-L89
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.optimizer_deletion_cost. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_smul
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_divergence
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_stationary

-- ---- from OAI.Combinatorics.CliqueFree.Deletion ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

 -- the two expressions are definitionally the sums

lemma optimizer_deletion_cost {G : SimpleGraph V} {w : V → ℝ}
    (hw : IsOptimizer G w) (A : Finset V) :
    potential G w - potential G (restrict Aᶜ w) =
      mass w A + edgeMass G (restrict A w) := by
  classical
  have hq : ∀ v, 0 ≤ restrict Aᶜ w v := by
    intro v
    simp only [restrict]
    split_ifs
    · exact hw.1 v
    · rfl
  rw [(optimizer_divergence hw _ hq).2]
  have hsum : (∑ v, (restrict Aᶜ w v * Real.log (restrict Aᶜ w v / w v) -
      restrict Aᶜ w v + w v)) = mass w A := by
    calc
      _ = ∑ v, if v ∈ A then w v else 0 := by
        apply sum_congr rfl
        intro v _
        by_cases hv : v ∈ A
        · simp [restrict,hv]
        · simp [restrict,hv, (optimizer_stationary hw v).1.ne']
      _ = mass w A := by simp [mass]
  have hdiff : restrict Aᶜ w - w = (-1 : ℝ) • restrict A w := by
    ext v
    by_cases hv : v ∈ A <;> simp [restrict,hv]
  rw [hsum, hdiff]
  have he := edgeMass_smul G (restrict A w) (-1)
  simpa only [Pi.smul_def,smul_eq_mul,neg_one_sq,one_mul] using congrArg (mass w A + ·) he

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_deletion_cost.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_deletion_cost.{u}
