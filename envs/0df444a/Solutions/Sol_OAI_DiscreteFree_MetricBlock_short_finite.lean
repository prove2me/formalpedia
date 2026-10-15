-- Prove2me | solution 1 for OAI.DiscreteFree.MetricBlock.short_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:24:37.564012+00:00
-- url     : https://prove2.me/submissions/b7a15148-0b62-4e27-9933-22221b2da4ff

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Attachment.lean:L96-L109
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.MetricBlock.short_finite. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzFree.PortGraphs ----
namespace OAI

/-!
# Port graphs, reduced walks, and capped-distance labels
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree
open scoped BigOperators Classical

namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)

end PortGraph

namespace BoundedWords
variable {D : Type*}

end BoundedWords

namespace PortGraph
variable {X D : Type*} [Fintype D] (G : PortGraph X D)

theorem near_finite (n : ℕ) (x : X) : {y : X | G.Near n x y}.Finite := by
  have h : {y : X | G.Near n x y} = Set.range
      (fun w : BoundedWords D n => G.walk x w.val) := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨⟨w, hw⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [h]
  exact Set.finite_range _

end PortGraph
end DiscreteFree

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.Attachment ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Attachment-length estimates and label compatibility
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical
namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)
end PortGraph

namespace MetricBlock
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

variable [Fintype D]

omit [Fintype C] in
theorem short_finite (n : ℕ) (u : Point G color cap R) :
    {v | ShortRelation G color cap R n u v}.Finite := by
  cases u with
  | inl x =>
    apply ((G.near_finite n x).image (Sum.inl : X → Point G color cap R)).subset
    rintro (y|a) hy
    · exact ⟨y, hy, rfl⟩
    · exact False.elim hy
  | inr a =>
    apply (Set.finite_singleton (Sum.inr a : Point G color cap R)).subset
    rintro (x|b) hb
    · exact False.elim hb
    · exact Set.mem_singleton_iff.mpr (congrArg Sum.inr hb.symm)

variable [Fact (0 < R)]

end MetricBlock
end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricBlock
open scoped BigOperators ENNReal
open scoped Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.MetricBlock.short_finite := @_root_.OAI.DiscreteFree.MetricBlock.short_finite
