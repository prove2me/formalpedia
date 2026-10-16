-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.Splitting.triangleMass_surviving_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:13:54.130442+00:00
-- url     : https://prove2.me/submissions/c40ce549-06de-4186-aaaf-5274ce6cba13

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Splitting.lean:L101-L140
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.Splitting.triangleMass_surviving_le. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_TriangleState_sum_eq

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma triangleMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    6 * triangleMass G w = ∑ u, w u * triangleAt G w u := by
  unfold triangleMass
  ring

lemma commonMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) (u v : V) :
    commonMass G w u v = ∑ z ∈ neighbors G u, if G.Adj v z then w z else 0 := by
  classical
  unfold commonMass mass
  rw [← filter_mem_eq_inter, sum_filter]
  simp only [mem_neighbors]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.TriangleState ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace TriangleState
variable {G : SimpleGraph V}
lemma sum_weight (w : V → ℝ) : (∑ t : TriangleState G, weight w t) = 6 * triangleMass G w := by
  simp only [weight]
  rw [sum_eq (fun u v z ↦ w u * w v * w z), triangleMass_eq_sum]
  simp only [triangleAt, commonMass_eq_sum, mul_sum, mul_ite, mul_zero, mul_assoc]

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}
end TriangleState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Projection ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

variable {U : Type v} [Fintype U]

lemma sum_injective_le {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (g : J → ℝ) (hg : ∀ j, 0 ≤ g j) :
    (∑ i, g (f i)) ≤ ∑ j, g j := by
  classical
  calc
    _ = ∑ j ∈ univ.image f, g j := (sum_image (fun _ _ _ _ h ↦ hf h)).symm
    _ ≤ _ := sum_le_univ_sum_of_nonneg hg

namespace EdgeProjection
variable {H : SimpleGraph U} {G : SimpleGraph V} {π : U → V}

end EdgeProjection

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Splitting ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace Splitting
variable {G : SimpleGraph V}

lemma triangleMass_surviving_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (F : EdgeState G → EdgeState G) (hF : ∀ e, (F e).src = e.src)
    (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, if Survives F good t then TriangleState.weight w t else 0) ≤
      6 * triangleMass (graph F hF good) (w ∘ EdgeState.src) := by
  classical
  let H := graph F hF good
  let S := {t : TriangleState G // Survives F good t}
  let f : S → TriangleState H := fun t ↦
    ⟨(F t.val.edge12, F t.val.edge12.rev, F t.val.edge13.rev),
      ⟨t.val.edge12, t.property.2.2.2.1, t.property.2.2.2.2.1, rfl, rfl⟩,
      ⟨t.val.edge13, t.property.2.2.2.2.2.1, t.property.2.2.2.2.2.2.1, t.property.1.symm, rfl⟩,
      ⟨t.val.edge23, t.property.2.2.2.2.2.2.2.1, t.property.2.2.2.2.2.2.2.2,
        t.property.2.1.symm, t.property.2.2.1.symm⟩⟩
  have coords (t : S) :
      (f t).first.src = t.val.first ∧ (f t).second.src = t.val.second ∧
        (f t).third.src = t.val.third := by
    change (F t.val.edge12).src = _ ∧ (F t.val.edge12.rev).src = _ ∧ (F t.val.edge13.rev).src = _
    simp only [hF]
    exact ⟨rfl, rfl, rfl⟩
  have hf : Function.Injective f := by
    intro t s hts
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (coords t).1.symm.trans ((congrArg (fun a : TriangleState H ↦ a.first.src) hts).trans (coords s).1)
    · apply Prod.ext
      · exact (coords t).2.1.symm.trans ((congrArg (fun a : TriangleState H ↦ a.second.src) hts).trans (coords s).2.1)
      · exact (coords t).2.2.symm.trans ((congrArg (fun a : TriangleState H ↦ a.third.src) hts).trans (coords s).2.2)
  calc
    _ = ∑ t : S, TriangleState.weight w t.val := by
      rw [← sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ t : S, TriangleState.weight (w ∘ EdgeState.src) (f t) := by
      apply sum_congr rfl
      intro t _
      simp only [TriangleState.weight, Function.comp_apply, (coords t).1, (coords t).2.1, (coords t).2.2]
    _ ≤ ∑ t : TriangleState H, TriangleState.weight (w ∘ EdgeState.src) t :=
      sum_injective_le f hf _ (fun t ↦ mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _))
    _ = _ := TriangleState.sum_weight _

end Splitting

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.Splitting
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.triangleMass_surviving_le.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.triangleMass_surviving_le.{u}
