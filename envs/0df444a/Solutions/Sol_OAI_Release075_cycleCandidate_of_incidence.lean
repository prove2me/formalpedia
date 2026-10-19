-- Prove2me | solution 1 for OAI.Release075.cycleCandidate_of_incidence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:23:08.369172+00:00
-- url     : https://prove2.me/submissions/ee3874b6-5a05-4bfa-bd41-ea162ae62785

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L507-L529
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.cycleCandidate_of_incidence. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_line_two_points

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

/-- Rotation has no fixed point on a cycle with at least two entries. -/
theorem finRotate_ne_self {s : ℕ} (hs : 2 ≤ s) (i : Fin s) : finRotate s i ≠ i := by
  intro hi
  have hs1 : 1 < s := by omega
  have he := congrArg Fin.val hi
  have hv : (finRotate s i).val = (i.val+1)%s := by
    simp [finRotate_apply, Fin.add_def, Nat.mod_eq_of_lt hs1]
  rw [hv] at he
  by_cases h : i.val+1 < s
  · rw [Nat.mod_eq_of_lt h] at he; omega
  · have hi' : i.val+1=s := by omega
    rw [hi',Nat.mod_self] at he; omega

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Any actual simple incidence cycle yields one of the counted attempts. -/
theorem cycleCandidate_of_incidence {S : Finset V} (ω : S → Projectivization K V)
    {s : ℕ} (hs : 2 ≤ s) (p : Fin s → V) (l : Fin s → S)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (h : ∀ i, PuncturedIncidence (l i).val (p i) (ω (l i)) ∧
      PuncturedIncidence (l i).val (p (finRotate s i)) (ω (l i))) :
    ∃ c : CycleCandidate (K := K) S (finRotate s), c.Occurs ω ∧ ∀ i, c.marks i = l i := by
  have hneq (i : Fin s) : p (finRotate s i) ≠ p i := hp.ne (finRotate_ne_self hs i)
  have hex (i : Fin s) := line_two_points (l i).val (p i) (p (finRotate s i)) (ω (l i))
    (hneq i) (h i).1.2 (h i).2.2
  let t : Fin s → K := fun i => (hex i).choose
  have ht (i : Fin s) : candidateMark (finRotate s) p t i = (l i).val := (hex i).choose_spec.1.symm
  let c : CycleCandidate (K := K) S (finRotate s) :=
    ⟨(p,t),hp,hneq,(fun i => ht i ▸ (l i).property),by
      intro i j hij
      apply hl
      apply Subtype.ext
      simpa only [ht] using hij⟩
  have hc (i : Fin s) : c.marks i = l i := Subtype.ext (ht i)
  refine ⟨c,?_,hc⟩
  intro i
  rw [hc]
  exact (hex i).choose_spec.2

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


theorem solution : type_of% @_root_.OAI.Release075.cycleCandidate_of_incidence := @_root_.OAI.Release075.cycleCandidate_of_incidence
