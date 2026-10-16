-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.Splitting.neighborMass_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:12:01.946681+00:00
-- url     : https://prove2.me/submissions/79bc48df-af80-444a-a8aa-6bb704ce0217

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Splitting.lean:L58-L90
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.Splitting.neighborMass_le. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_projection

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

omit [Fintype V] in
lemma neighbor_injective (h : EdgeProjection H G π) (a : U) :
    Set.InjOn π (neighbors H a) := by
  intro b hb c hc heq
  exact (h.inj a b a c ((mem_neighbors _ _ _).1 hb) ((mem_neighbors _ _ _).1 hc) rfl heq).2

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

lemma neighborMass_le (w : V → ℝ) (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop)
    (K : EdgeState G → EdgeState G → ℝ) (hK0 : ∀ a e, 0 ≤ K a e)
    (hK1 : ∀ a, ∑ e, K a e = 1) {L : ℝ} (hL : 0 ≤ L)
    (hadm : ∀ e, good e → w e.dst ≤ L * K (F e) e) (a : EdgeState G) :
    neighborMass (graph F hF good) (w ∘ EdgeState.src) a ≤ L := by
  classical
  let H := graph F hF good
  let N := ↑(neighbors H a)
  have hproj := projection F hF good
  let f : N → EdgeState G := fun b ↦
    ⟨(a.src, b.val.src), hproj.map_adj _ _ ((mem_neighbors _ _ _).1 b.property)⟩
  have hf : Function.Injective f := by
    intro b c heq
    apply Subtype.ext
    apply hproj.neighbor_injective a b.property c.property
    exact congrArg (fun e : EdgeState G ↦ e.dst) heq
  have hle (b : N) : w b.val.src ≤ L * K a (f b) := by
    obtain ⟨e, he, _, ha, hb⟩ := (mem_neighbors H a b.val).1 b.property
    have hef : f b = e := by
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg EdgeState.src ha).symm.trans (hF e)
      · exact (congrArg EdgeState.src hb).symm.trans (hF e.rev)
    rw [hef, ← ha]
    have hd : b.val.src = e.dst := (congrArg EdgeState.src hb).symm.trans (hF e.rev)
    simpa only [hd] using hadm e he
  calc
    _ = ∑ b : N, w b.val.src := (sum_coe_sort (neighbors H a) (fun b ↦ w b.src)).symm
    _ ≤ ∑ b : N, L * K a (f b) := sum_le_sum (fun b _ ↦ hle b)
    _ = L * ∑ b : N, K a (f b) := (mul_sum _ _ _).symm
    _ ≤ L * ∑ e, K a e := mul_le_mul_of_nonneg_left (sum_injective_le f hf (K a) (hK0 a)) hL
    _ = L := by rw [hK1, mul_one]

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


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.neighborMass_le.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.neighborMass_le.{u}
