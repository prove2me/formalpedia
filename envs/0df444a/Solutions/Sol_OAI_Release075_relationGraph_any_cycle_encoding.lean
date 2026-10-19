-- Prove2me | solution 1 for OAI.Release075.relationGraph_any_cycle_encoding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:20:15.272985+00:00
-- url     : https://prove2.me/submissions/c92c90ae-5018-4ac3-8167-f9e91e62e8bd

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L450-L467
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.relationGraph_any_cycle_encoding. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_relationGraph_cycle_encoding

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

/-- The same encoding without a restriction on the chosen starting vertex. -/
theorem relationGraph_any_cycle_encoding {A B : Type*} (R : A → B → Prop)
    {a : A ⊕ B} (w : (relationGraph R).Walk a a) (hw : w.IsCycle) :
    ∃ (s : ℕ) (_ : 2 ≤ s) (p : Fin s → A) (l : Fin s → B),
      w.length = 2*s ∧ Function.Injective p ∧ Function.Injective l ∧
      ∀ i, R (p i) (l i) ∧ R (p (finRotate s i)) (l i) := by
  cases a with
  | inl a => exact relationGraph_cycle_encoding R w hw
  | inr b =>
    have hn : 0 < w.length := by have := hw.three_le_length; omega
    have ha := w.adj_getVert_succ hn
    rw [SimpleGraph.Walk.getVert_zero] at ha
    cases hv : w.getVert 1 with
    | inr c => rw [hv] at ha; exact ha.elim
    | inl a =>
      have hm : Sum.inl a ∈ w.support := hv ▸ w.getVert_mem_support 1
      obtain ⟨s,hs,p,l,hlen,hp,hl,h⟩ := relationGraph_cycle_encoding R (w.rotate (.inl a) hm) (hw.rotate hm)
      exact ⟨s,hs,p,l,by simpa using hlen,hp,hl,h⟩

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

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


theorem solution : type_of% @_root_.OAI.Release075.relationGraph_any_cycle_encoding := @_root_.OAI.Release075.relationGraph_any_cycle_encoding
