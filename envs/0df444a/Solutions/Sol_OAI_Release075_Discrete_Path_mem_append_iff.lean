-- Prove2me | solution 1 for OAI.Release075.Discrete.Path.mem_append_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:58:16.686299+00:00
-- url     : https://prove2.me/submissions/b75c6ff9-43e4-4c1b-b61a-5b9c7bec4997

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean:L122-L135
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.Discrete.Path.mem_append_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric

-- ---- from OAI.GroupTheory.Hyperbolic.DiscreteMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075.Discrete

variable {V : Type} (M : Metric V)

namespace Path
variable {M} {a b c : V}

theorem mem_append_iff (p : Path M a b) (q : Path M b c) (x : V) :
    (p.append q).Mem x ↔ p.Mem x ∨ q.Mem x := by
  constructor
  · rintro ⟨i,hi,hx⟩
    by_cases h : i ≤ p.length
    · exact Or.inl ⟨i,h,(p.append_at_left q h).symm.trans hx⟩
    · refine Or.inr ⟨i-p.length,by change i ≤ p.length+q.length at hi; omega,?_⟩
      have he : p.length+(i-p.length) = i := by omega
      have hh := p.append_at_right q (i-p.length)
      rw [he] at hh
      exact hh.symm.trans hx
  · rintro (⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩)
    · exact ⟨i,by change i ≤ p.length+q.length; omega,p.append_at_left q hi⟩
    · exact ⟨p.length+i,by change p.length+i ≤ p.length+q.length; omega,p.append_at_right q i⟩

end Path

namespace Metric
variable {M}

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

end Path

end Release075.Discrete

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Path


theorem solution : type_of% @_root_.OAI.Release075.Discrete.Path.mem_append_iff := @_root_.OAI.Release075.Discrete.Path.mem_append_iff
