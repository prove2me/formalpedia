-- Prove2me | solution 1 for NagamochiIbaraki.NodeConn.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:13:45.880614+00:00
-- url     : https://prove2.me/submissions/18b1f122-00ee-4f5c-bfcd-2de33330b022

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

/-- Invariant of FOREST used for Lemma 2.2. -/
def aux_l22_Inv {V E : Type*} (ends : E → Sym2 V) (s : State V E) : Prop :=
  (∀ v i, 1 ≤ i → ((∃ e, v ∈ ends e ∧ s.idx e = i) ↔ i ≤ s.r v)) ∧
  (∀ v ∈ s.done, ∀ e, v ∈ ends e → s.idx e ≠ 0) ∧
  (∀ x, s.cur = some x → ∀ v, v ∉ s.done → s.r v ≤ s.r x)

theorem aux_l22_init {V E : Type*} (ends : E → Sym2 V) :
    aux_l22_Inv ends (init : State V E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v i hi
    simp only [init]
    constructor
    · rintro ⟨e, -, he⟩; omega
    · intro h; omega
  · intro v hv; simp [init] at hv
  · intro x hx; simp [init] at hx

theorem aux_l22_step {V E : Type*} [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (s t : State V E)
    (hs : aux_l22_Inv ends s) (hst : Step ends s t) : aux_l22_Inv ends t := by
  obtain ⟨h1, h2, h3⟩ := hs
  rcases hst with ⟨x, hcur, hx, hmax, rfl⟩ | ⟨x, y, e, hcur, he0, hends, rfl⟩ |
      ⟨x, hcur, hall, rfl⟩
  · refine ⟨h1, h2, ?_⟩
    intro x' hx' v hv
    simp only [Option.some.injEq] at hx'
    subst hx'
    exact hmax v hv
  · have hxy : x ≠ y := by
      intro h; subst h; exact hloop e (by rw [hends]; simp)
    have hy : y ∉ s.done := by
      intro hy; exact h2 y hy e (by rw [hends]; simp) he0
    have hyx : s.r y ≤ s.r x := h3 x hcur y hy
    refine ⟨?_, ?_, ?_⟩
    · intro v i hi
      have key : (∃ e', v ∈ ends e' ∧ Function.update s.idx e (s.r y + 1) e' = i) ↔
          ((v = x ∨ v = y) ∧ i = s.r y + 1) ∨ i ≤ s.r v := by
        rw [← h1 v i hi]
        constructor
        · rintro ⟨e', hv, he'⟩
          by_cases hee : e' = e
          · subst hee
            left
            rw [hends, Sym2.mem_iff] at hv
            simp only [Function.update_self] at he'
            exact ⟨hv, he'.symm⟩
          · right; rw [Function.update_of_ne hee] at he'; exact ⟨e', hv, he'⟩
        · rintro (⟨hv, hi'⟩ | ⟨e', hv, he'⟩)
          · refine ⟨e, ?_, ?_⟩
            · rw [hends, Sym2.mem_iff]; exact hv
            · simp [hi']
          · have hee : e' ≠ e := by rintro rfl; omega
            exact ⟨e', hv, by rw [Function.update_of_ne hee]; exact he'⟩
      show (∃ e', v ∈ ends e' ∧ Function.update s.idx e (s.r y + 1) e' = i) ↔ _
      rw [key]
      by_cases hvy : v = y
      · subst hvy
        simp only [Function.update_self]
        constructor
        · rintro (⟨-, h⟩ | h) <;> omega
        · intro h
          by_cases h' : i = s.r v + 1
          · exact Or.inl ⟨by simp, h'⟩
          · exact Or.inr (by omega)
      · by_cases hvx : v = x
        · subst hvx
          dsimp only
          rw [Function.update_of_ne hvy, Function.update_self]
          split_ifs with hr
          · constructor
            · rintro (⟨-, h⟩ | h) <;> omega
            · intro h
              by_cases h' : i = s.r y + 1
              · exact Or.inl ⟨Or.inl rfl, h'⟩
              · exact Or.inr (by omega)
          · constructor
            · rintro (⟨-, h⟩ | h) <;> omega
            · intro h; exact Or.inr h
        · dsimp only
          rw [Function.update_of_ne hvy, Function.update_of_ne hvx]
          constructor
          · rintro (⟨h, -⟩ | h)
            · rcases h with h | h <;> contradiction
            · exact h
          · intro h; exact Or.inr h
    · intro v hv e' hve'
      show Function.update s.idx e (s.r y + 1) e' ≠ 0
      by_cases hee : e' = e
      · subst hee; simp
      · rw [Function.update_of_ne hee]; exact h2 v hv e' hve'
    · intro x' hx' v hv
      change s.cur = some x' at hx'
      change v ∉ s.done at hv
      rw [hcur, Option.some.injEq] at hx'
      subst hx'
      show Function.update (Function.update s.r x _) y (s.r y + 1) v ≤
        Function.update (Function.update s.r x _) y (s.r y + 1) x
      rw [Function.update_of_ne hxy, Function.update_self]
      have hv' := h3 x hcur v hv
      by_cases hvy : v = y
      · subst hvy
        rw [Function.update_self]
        split_ifs <;> omega
      · rw [Function.update_of_ne hvy]
        by_cases hvx : v = x
        · subst hvx; rw [Function.update_self]
        · rw [Function.update_of_ne hvx]
          split_ifs <;> omega
  · refine ⟨h1, ?_, ?_⟩
    · intro v hv e' hve'
      change v ∈ insert x s.done at hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hall e' hve'
      · exact h2 v hv e' hve'
    · intro x' hx'
      change (none : Option V) = some x' at hx'
      simp at hx'

end NagamochiIbaraki.NodeConn

open NagamochiIbaraki.NodeConn

theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ (v : V) (i : ℕ), 1 ≤ i → i ≤ Fintype.card E →
      ((∃ e : E, v ∈ ends e ∧ (σ k).idx e = i) ↔ i ≤ (σ k).r v) := by
  have hinv : ∀ k, k ≤ K → aux_l22_Inv ends (σ k) := by
    intro k
    induction k with
    | zero => intro _; rw [hrun.1]; exact aux_l22_init ends
    | succ n ih =>
      intro hn
      exact aux_l22_step ends hloop _ _ (ih (by omega)) (hrun.2 n (by omega))
  intro k hk v i hi _
  exact (hinv k hk).1 v i hi
