-- Prove2me | solution 1 for OAI.Release075.relationGraph_cycle_encoding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:18:31.498548+00:00
-- url     : https://prove2.me/submissions/e91c8624-b72e-4b67-9d04-f3757e75b426

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L401-L448
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.relationGraph_cycle_encoding. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

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

theorem relationGraph_even_getVert {A B : Type*} (R : A → B → Prop) {a : A} {v : A ⊕ B}
    (w : (relationGraph R).Walk (.inl a) v) (k : ℕ) (hk : 2*k ≤ w.length) :
    ∃ b : A, w.getVert (2*k) = .inl b := by
  have h := (relationColoring R).even_length_iff_congr (w.take (2*k))
  rw [SimpleGraph.Walk.take_length, inf_eq_left.mpr hk] at h
  have he : Even (2*k) := ⟨k,by omega⟩
  have hh := h.mp he
  cases hv : w.getVert (2*k) with
  | inl b => exact ⟨b,rfl⟩
  | inr b => simp [hv,relationColoring] at hh

theorem relationGraph_odd_getVert {A B : Type*} (R : A → B → Prop) {a : A} {v : A ⊕ B}
    (w : (relationGraph R).Walk (.inl a) v) (k : ℕ) (hk : 2*k+1 ≤ w.length) :
    ∃ b : B, w.getVert (2*k+1) = .inr b := by
  obtain ⟨a',ha⟩ := relationGraph_even_getVert R w k (by omega)
  have h := w.adj_getVert_succ (by omega : 2*k < w.length)
  rw [ha] at h
  cases hv : w.getVert (2*k+1) with
  | inl b => rw [hv] at h; exact h.elim
  | inr b => exact ⟨b,rfl⟩

/-- The concrete alternating normal form of any simple bipartite cycle. -/
theorem relationGraph_cycle_encoding {A B : Type*} (R : A → B → Prop)
    {a : A} (w : (relationGraph R).Walk (.inl a) (.inl a)) (hw : w.IsCycle) :
    ∃ (s : ℕ) (_ : 2 ≤ s) (p : Fin s → A) (l : Fin s → B),
      w.length = 2*s ∧ Function.Injective p ∧ Function.Injective l ∧
      ∀ i, R (p i) (l i) ∧ R (p (finRotate s i)) (l i) := by
  have he := ((relationColoring R).even_length_iff_congr w).mpr Iff.rfl
  obtain ⟨s,hs⟩ := he
  have hlen : w.length = 2*s := by omega
  have hs2 : 2 ≤ s := by have := hw.three_le_length; omega
  let p : Fin s → A := fun i => (relationGraph_even_getVert R w i.val (by omega)).choose
  let l : Fin s → B := fun i => (relationGraph_odd_getVert R w i.val (by omega)).choose
  have hp (i : Fin s) : w.getVert (2*i.val) = .inl (p i) :=
    (relationGraph_even_getVert R w i.val (by omega)).choose_spec
  have hl (i : Fin s) : w.getVert (2*i.val+1) = .inr (l i) :=
    (relationGraph_odd_getVert R w i.val (by omega)).choose_spec
  have hpnext (i : Fin s) : w.getVert (2*i.val+2) = .inl (p (finRotate s i)) := by
    have hv : (finRotate s i).val = (i.val+1)%s := by
      have hs1 : 1 < s := by omega
      simp [finRotate_apply, Fin.add_def, Nat.mod_eq_of_lt hs1]
    by_cases hi : i.val+1 < s
    · rw [Nat.mod_eq_of_lt hi] at hv
      simpa only [hv, mul_add, mul_one] using hp (finRotate s i)
    · have hi' : i.val+1=s := by omega
      have hv' : (finRotate s i).val = 0 := by rw [hi',Nat.mod_self] at hv; exact hv
      have hzero := hp (finRotate s i)
      rw [hv',mul_zero,SimpleGraph.Walk.getVert_zero] at hzero
      rw [show 2*i.val+2=w.length by omega,SimpleGraph.Walk.getVert_length]
      exact hzero
  refine ⟨s,hs2,p,l,hlen,?_,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    have heq : w.getVert (2*i.val) = w.getVert (2*j.val) := by rw [hp,hp,hij]
    have hh := hw.getVert_injOn' (by change 2*i.val ≤ w.length-1; omega)
      (by change 2*j.val ≤ w.length-1; omega) heq
    omega
  · intro i j hij
    apply Fin.ext
    have heq : w.getVert (2*i.val+1) = w.getVert (2*j.val+1) := by rw [hl,hl,hij]
    have hh := hw.getVert_injOn' (by change 2*i.val+1 ≤ w.length-1; omega)
      (by change 2*j.val+1 ≤ w.length-1; omega) heq
    omega
  · intro i
    have h₀ := w.adj_getVert_succ (by omega : 2*i.val < w.length)
    have h₁ := w.adj_getVert_succ (by omega : 2*i.val+1 < w.length)
    rw [hp,hl] at h₀
    rw [hl,show 2*i.val+1+1=2*i.val+2 by omega,hpnext] at h₁
    exact ⟨h₀,h₁⟩

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


theorem solution : type_of% @_root_.OAI.Release075.relationGraph_cycle_encoding := @_root_.OAI.Release075.relationGraph_cycle_encoding
