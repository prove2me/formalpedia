-- Prove2me | solution 1 for OAI.DiscreteFree.PortGraph.Matched.exists_based
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:31:53.908963+00:00
-- url     : https://prove2.me/submissions/400f65cb-f24f-4461-9f5b-2d7f3b5c0c1e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/GraphWalks.lean:L112-L128
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.PortGraph.Matched.exists_based. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks

-- ---- from OAI.Analysis.LipschitzFree.GraphWalks ----
namespace OAI

/-!
# Matched graph walks and exceptional record estimates
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.PortGraph
open scoped Classical
variable {X D S : Type*} (G : PortGraph X D)
    (compatible : X → S → Prop) (trans : S → S → Prop)

end DiscreteFree.PortGraph
end

noncomputable section
namespace DiscreteFree.PortGraph
open scoped Classical
variable {X D S : Type*} (G : PortGraph X D)
    (compatible : X → S → Prop) (trans : S → S → Prop)

theorem Matched.exists_based {x : X} {j : S} {w : List D}
    (h : G.Matched compatible trans x j w) :
    ∃ p : StatePaths.Based trans j w.length, ∀ i : Fin (w.length+1),
      compatible (G.walk x (w.take i.val)) (StatePaths.vertex trans j p i) := by
  induction w generalizing x j with
  | nil =>
    refine ⟨PUnit.unit, fun i => ?_⟩
    simpa [StatePaths.vertex, PortGraph.Matched] using h
  | cons e w ih =>
    obtain ⟨hc, k, hk, hm⟩ := h
    obtain ⟨p, hp⟩ := ih hm
    refine ⟨⟨⟨k, hk⟩, p⟩, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · change compatible x j
      exact hc
    · change compatible (G.walk (G.move x e) (w.take i.val)) (StatePaths.vertex trans k p i)
      exact hp i

end DiscreteFree.PortGraph
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.PortGraph
open scoped BigOperators ENNReal
open scoped Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.PortGraph.Matched.exists_based := @_root_.OAI.DiscreteFree.PortGraph.Matched.exists_based
