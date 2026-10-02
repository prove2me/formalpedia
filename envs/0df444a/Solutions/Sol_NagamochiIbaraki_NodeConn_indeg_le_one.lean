-- Prove2me | solution 1 for NagamochiIbaraki.NodeConn.indeg_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:18:41.85028+00:00
-- url     : https://prove2.me/submissions/389267fd-1423-48ec-9248-8001fd19a147

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

set_option autoImplicit false

namespace NagamochiIbaraki.NodeConn.P604e6b78

open NagamochiIbaraki.NodeConn

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Structural invariant of FOREST states. -/
def Inv (ends : E → Sym2 V) (s : State V E) : Prop :=
  (∀ z ∈ s.order, z ∈ s.done ∨ s.cur = some z) ∧ (∀ x, s.cur = some x → x ∈ s.order) ∧
  (∀ z ∈ s.done, ∀ e, z ∈ ends e → s.idx e ≠ 0)

lemma inv_init (ends : E → Sym2 V) : Inv ends (init : State V E) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [init]

lemma inv_step (ends : E → Sym2 V) {s t : State V E} (h : Inv ends s) (hs : Step ends s t) :
    Inv ends t := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases hs with ⟨x, hc, hxd, -, rfl⟩ | ⟨x, y, e, hc, he0, hee, rfl⟩ | ⟨x, hc, hall, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · rcases h1 z hz with h | h
        · exact Or.inl h
        · rw [hc] at h; cases h
      · rw [List.mem_singleton] at hz
        subst hz
        exact Or.inr rfl
    · intro x' hx'
      cases hx'
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact h3
  · refine ⟨h1, h2, ?_⟩
    intro z hz e' hze'
    show Function.update s.idx e (s.r y + 1) e' ≠ 0
    by_cases hee' : e' = e
    · subst hee'; simp
    · rw [Function.update_of_ne hee']; exact h3 z hz e' hze'
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases h1 z hz with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · rw [hc] at h; cases h; exact Or.inl (Finset.mem_insert_self _ _)
    · intro x' hx'; cases hx'
    · intro z hz e' hze'
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hall e' hze'
      · exact h3 z hz e' hze'

lemma inv_run (ends : E → Sym2 V) (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → Inv ends (σ k) := by
  intro k hk
  induction k with
  | zero => rw [hrun.1]; exact inv_init ends
  | succ n ih => exact inv_step ends (ih (by omega)) (hrun.2 n (by omega))

lemma order_step (ends : E → Sym2 V) {s t : State V E} (hs : Step ends s t) :
    ∃ l, t.order = s.order ++ l := by
  rcases hs with ⟨x, -, -, -, rfl⟩ | ⟨x, y, e, -, -, -, rfl⟩ | ⟨x, -, -, rfl⟩
  · exact ⟨[x], rfl⟩
  · exact ⟨[], (List.append_nil _).symm⟩
  · exact ⟨[], (List.append_nil _).symm⟩

lemma order_prefix (ends : E → Sym2 V) (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∃ l, (σ K).order = (σ k).order ++ l := by
  have key : ∀ j k, k + j ≤ K → ∃ l, (σ (k + j)).order = (σ k).order ++ l := by
    intro j
    induction j with
    | zero => intro k _; exact ⟨[], (List.append_nil _).symm⟩
    | succ n ih =>
      intro k hk
      obtain ⟨l, hl⟩ := ih k (by omega)
      obtain ⟨l', hl'⟩ := order_step ends (hrun.2 (k + n) (by omega))
      refine ⟨l ++ l', ?_⟩
      rw [show k + (n + 1) = k + n + 1 by omega, hl', hl, List.append_assoc]
  intro k hk
  have := key (K - k) k (by omega)
  rwa [show k + (K - k) = K by omega] at this

/-- The in-degree invariant for a fixed final order `O`. -/
def PA (ends : E → Sym2 V) (O : List V) (s : State V E) : Prop :=
  ∀ e u v, s.idx e ≠ 0 → ends e = s(u, v) → O.idxOf u < O.idxOf v → s.idx e ≤ s.r v

def PJ (ends : E → Sym2 V) (O : List V) (s : State V E) : Prop :=
  ∀ e₁ e₂ u₁ u₂ v, s.idx e₁ ≠ 0 → s.idx e₁ = s.idx e₂ → ends e₁ = s(u₁, v) →
    O.idxOf u₁ < O.idxOf v → ends e₂ = s(u₂, v) → O.idxOf u₂ < O.idxOf v → e₁ = e₂

lemma main_step (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (O : List V)
    {s t : State V E} (hinv : Inv ends s) (hpre : ∃ l, O = s.order ++ l)
    (hs : Step ends s t) (hA : PA ends O s) (hJ : PJ ends O s) :
    PA ends O t ∧ PJ ends O t := by
  rcases hs with ⟨x, -, -, -, rfl⟩ | ⟨x, y, e, hc, he0, hee, rfl⟩ | ⟨x, -, -, rfl⟩
  · exact ⟨hA, hJ⟩
  · have hxy : x ≠ y := by
      intro h
      apply hloop e
      rw [hee, Sym2.mk_isDiag_iff]
      exact h
    have hxo : x ∈ s.order := hinv.2.1 x hc
    have hyo : y ∉ s.order := by
      intro hy
      rcases hinv.1 y hy with hd | hc'
      · exact hinv.2.2 y hd e (by rw [hee]; exact Sym2.mem_mk_right x y) he0
      · rw [hc] at hc'; cases hc'; exact hxy rfl
    have hB : O.idxOf x < O.idxOf y := by
      obtain ⟨l, rfl⟩ := hpre
      rw [List.idxOf_append_of_mem hxo, List.idxOf_append_of_notMem hyo]
      have := List.idxOf_lt_length_of_mem hxo
      omega
    have hhead : ∀ u v, ends e = s(u, v) → O.idxOf u < O.idxOf v → v = y := by
      intro u v h hb
      rw [hee, Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · omega
    have hmono : ∀ v, s.r v ≤ Function.update
        (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x)) y (s.r y + 1) v := by
      intro v
      by_cases hvy : v = y
      · subst hvy; simp
      · rw [Function.update_of_ne hvy]
        by_cases hvx : v = x
        · subst hvx; simp only [Function.update_self]; split_ifs <;> omega
        · rw [Function.update_of_ne hvx]
    have hidx : ∀ e', e' ≠ e → Function.update s.idx e (s.r y + 1) e' = s.idx e' :=
      fun e' h => Function.update_of_ne h _ _
    constructor
    · intro e' u v hne hends hb
      show Function.update s.idx e (s.r y + 1) e' ≤ Function.update
        (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x)) y (s.r y + 1) v
      by_cases he' : e' = e
      · subst he'
        have := hhead u v hends hb
        subst this
        simp
      · rw [hidx e' he']
        have hne' : s.idx e' ≠ 0 := by
          have := hne; simp only at this; rwa [hidx e' he'] at this
        exact le_trans (hA e' u v hne' hends hb) (hmono v)
    · intro e₁ e₂ u₁ u₂ v hne heq h1 b1 h2 b2
      simp only at hne heq
      by_cases he1 : e₁ = e <;> by_cases he2 : e₂ = e
      · rw [he1, he2]
      · exfalso
        subst he1
        have hv := hhead u₁ v h1 b1
        subst hv
        rw [Function.update_self, hidx e₂ he2] at heq
        have := hA e₂ u₂ _ (by omega) h2 b2
        omega
      · exfalso
        subst he2
        have hv := hhead u₂ v h2 b2
        subst hv
        rw [Function.update_self, hidx e₁ he1] at heq
        have := hA e₁ u₁ _ (by omega) h1 b1
        omega
      · rw [hidx e₁ he1] at hne heq
        rw [hidx e₂ he2] at heq
        exact hJ e₁ e₂ u₁ u₂ v hne heq h1 b1 h2 b2
  · exact ⟨hA, hJ⟩

lemma main (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (σ : ℕ → State V E) (K : ℕ)
    (hrun : IsRun ends σ K) : ∀ k, k ≤ K → PA ends (σ K).order (σ k) ∧ PJ ends (σ K).order (σ k) := by
  intro k hk
  induction k with
  | zero =>
    rw [hrun.1]
    exact ⟨fun e u v h => (h rfl).elim, fun e₁ e₂ u₁ u₂ v h => (h rfl).elim⟩
  | succ n ih =>
    have := ih (by omega)
    obtain ⟨l, hl⟩ := order_prefix ends σ K hrun n (by omega)
    exact main_step ends hloop _ (inv_run ends σ K hrun n (by omega)) ⟨l, hl⟩
      (hrun.2 n (by omega)) this.1 this.2

end NagamochiIbaraki.NodeConn.P604e6b78

open NagamochiIbaraki.NodeConn in
theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    ∀ k, k ≤ K → ∀ (i : ℕ) (v : V), 1 ≤ i → i ≤ Fintype.card E →
      ∀ e₁ ∈ cls (σ k) i, ∀ e₂ ∈ cls (σ k) i, ∀ u₁ u₂ : V,
        ends e₁ = s(u₁, v) → scanBefore (σ K) u₁ v →
        ends e₂ = s(u₂, v) → scanBefore (σ K) u₂ v → e₁ = e₂ := by
  intro k hk i v hi _ e₁ he₁ e₂ he₂ u₁ u₂ h1 b1 h2 b2
  have H := (NagamochiIbaraki.NodeConn.P604e6b78.main ends hloop σ K hrun.1 k hk).2
  simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
  exact H e₁ e₂ u₁ u₂ v (by omega) (by rw [he₁, he₂]) h1 b1 h2 b2
