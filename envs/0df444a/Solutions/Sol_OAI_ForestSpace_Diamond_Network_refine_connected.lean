-- Prove2me | solution 1 for OAI.ForestSpace.Diamond.Network.refine_connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:06:55.847441+00:00
-- url     : https://prove2.me/submissions/52064441-4508-42c9-9420-25ee0adaa552

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Diamonds.lean:L91-L110
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.Diamond.Network.refine_connected. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees
import Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity
import Definitions.Def_OAI_Analysis_ForestSpace_Components
import Definitions.Def_OAI_Analysis_ForestSpace_FullDual
import Definitions.Def_OAI_Analysis_ForestSpace_Diamonds

-- ---- from OAI.Analysis.ForestSpace.Diamonds ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

namespace ForestSpace

attribute [local instance] Classical.propDecidable

namespace Diamond

namespace Network
variable (A : Network)

 theorem edge_adj (e : A.E) : A.graph.Adj (A.left e) (A.right e) :=
  ⟨e,Or.inl ⟨rfl,rfl⟩⟩

 theorem refine_adj_left (e : A.E) (j : ℕ) :
    A.refine.graph.Adj (Sum.inl (A.left e)) (Sum.inr (e,j)) := by
  exact A.refine.edge_adj (e,j,false)

 theorem refine_adj_right (e : A.E) (j : ℕ) :
    A.refine.graph.Adj (Sum.inr (e,j)) (Sum.inl (A.right e)) := by
  exact A.refine.edge_adj (e,j,true)

 theorem refine_adj_lift {u v : A.V} (huv : A.graph.Adj u v) :
    ∃ w : A.refine.V, A.refine.graph.Adj (Sum.inl u) w ∧
      A.refine.graph.Adj w (Sum.inl v) := by
  obtain ⟨e,h | h⟩ := huv
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨Sum.inr (e,0),A.refine_adj_left e 0,A.refine_adj_right e 0⟩
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨Sum.inr (e,0),(A.refine_adj_right e 0).symm,(A.refine_adj_left e 0).symm⟩

 theorem refine_walk_lift {u v : A.V} (p : A.graph.Walk u v) :
    ∃ q : A.refine.graph.Walk (Sum.inl u) (Sum.inl v), q.length = 2*p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | @cons u v w huv p ih =>
    obtain ⟨q,hq⟩ := ih
    obtain ⟨z,huz,hzv⟩ := A.refine_adj_lift huv
    refine ⟨.cons huz (.cons hzv q),?_⟩
    change q.length+1+1 = 2*(p.length+1)
    rw [hq]
    omega

 theorem refine_connected (hA : A.graph.Connected) : A.refine.graph.Connected := by
  have hOld : ∀ u v : A.V, A.refine.graph.Reachable (Sum.inl u) (Sum.inl v) := by
    intro u v
    obtain ⟨p⟩ := hA u v
    obtain ⟨q,hq⟩ := A.refine_walk_lift p
    exact ⟨q⟩
  refine @SimpleGraph.Connected.mk _ _ ?_ ?_
  · intro u v
    cases u with
    | inl u =>
      cases v with
      | inl v => exact hOld u v
      | inr v => exact (hOld u (A.left v.1)).trans (A.refine_adj_left v.1 v.2).reachable
    | inr u =>
      cases v with
      | inl v => exact (A.refine_adj_left u.1 u.2).symm.reachable.trans (hOld (A.left u.1) v)
      | inr v => exact ((A.refine_adj_left u.1 u.2).symm.reachable.trans
          (hOld (A.left u.1) (A.left v.1))).trans (A.refine_adj_left v.1 v.2).reachable
  · obtain ⟨u⟩ := hA.nonempty
    exact ⟨Sum.inl u⟩

end Network

namespace Network

section
variable (A : Network)

end

end Network

end Diamond

end ForestSpace

end

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace OAI.ForestSpace.Diamond OAI.ForestSpace.Diamond.Network
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.Diamond.Network.refine_connected := @_root_.OAI.ForestSpace.Diamond.Network.refine_connected
