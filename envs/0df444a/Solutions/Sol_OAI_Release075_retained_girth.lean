-- Prove2me | solution 1 for OAI.Release075.retained_girth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:24:39.094823+00:00
-- url     : https://prove2.me/submissions/9ac33f1e-f3c6-48a5-927b-2fc6924811b1

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L558-L579
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.retained_girth. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_cycleCandidate_of_incidence
import Theorems.Thm_OAI_Release075_relationGraph_any_cycle_encoding

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

end CycleCandidate

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

end Degrees

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

/-- Deletion creates no cycle; exact girth >12 is obtained, including repeated
geometric lines with distinct labels. -/
theorem retained_girth (S : Finset V) (ω : S → Projectivization K V)
    (a : V ⊕ Retained S ω)
    (w : (relationGraph (fun z (i : Retained S ω) =>
      PuncturedIncidence i.val.val z (ω i.val))).Walk a a) (hw : w.IsCycle) : 12 < w.length := by
  by_contra hlen
  obtain ⟨s,hs,p,l,heq,hp,hl,h⟩ := relationGraph_any_cycle_encoding _ w hw
  have hs6 : s ≤ 6 := by omega
  let l' : Fin s → S := fun i => (l i).val
  have hl' : Function.Injective l' := by
    intro i j hh; apply hl; exact Subtype.ext hh
  obtain ⟨c,hc,hcl⟩ := cycleCandidate_of_incidence ω hs p l' hp hl' h
  let i : Fin s := ⟨0,by omega⟩
  have hdel : c.marks i ∈ deletedMarks S ω := by
    apply Finset.mem_biUnion.mpr
    refine ⟨s,Finset.mem_Icc.mpr ⟨hs,hs6⟩,?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,?_⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [hcl] at hdel
  exact (l i).property hdel
end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

end AlterationMean

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

end DimensionTwenty

attribute [instance] MarkedLineData.labelFintype

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.Release075.retained_girth := @_root_.OAI.Release075.retained_girth
