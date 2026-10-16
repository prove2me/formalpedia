-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.Splitting.projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:10:12.816419+00:00
-- url     : https://prove2.me/submissions/7c51e2c2-a0e2-4a4f-a36d-64d62cc8e7f0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Splitting.lean:L38-L56
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.Splitting.projection. The node keeps its source
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

omit [Fintype V] in
lemma projection (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop) :
    EdgeProjection (graph F hF good) G EdgeState.src := by
  have endpoints {a b : EdgeState G} {e : EdgeState G} (ha : F e = a) (hb : F e.rev = b) :
      a.src = e.src ∧ b.src = e.dst :=
    ⟨by rw [← ha, hF], by rw [← hb, hF]; rfl⟩
  constructor
  · rintro a b ⟨e, _, _, ha, hb⟩
    obtain ⟨hs, ht⟩ := endpoints ha hb
    rw [hs, ht]
    exact e.adj
  · rintro a b c d ⟨e, _, _, ha, hb⟩ ⟨f, _, _, hc, hd⟩ hac hbd
    obtain ⟨he1, he2⟩ := endpoints ha hb
    obtain ⟨hf1, hf2⟩ := endpoints hc hd
    have hef : e = f := Subtype.ext (Prod.ext (he1.symm.trans (hac.trans hf1))
      (he2.symm.trans (hbd.trans hf2)))
    subst f
    exact ⟨ha.symm.trans hc, hb.symm.trans hd⟩

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


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.projection.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.projection.{u}
