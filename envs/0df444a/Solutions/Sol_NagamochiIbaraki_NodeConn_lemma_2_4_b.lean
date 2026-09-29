-- Prove2me | solution 1 for NagamochiIbaraki.NodeConn.lemma_2_4_b
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:04:28.958667+00:00
-- url     : https://prove2.me/submissions/11a871da-e27a-4104-96ee-c71044ed7e67

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

section aux_l24b

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Invariant of FOREST used for Lemma 2.4(b). -/
def aux_l24b_Inv (ends : E → Sym2 V) (s : State V E) : Prop :=
  (∀ x, s.cur = some x → x ∉ s.done ∧ ∀ y, y ∉ s.done → s.r y ≤ s.r x) ∧
  (∀ y y', y ∉ s.done → y' ∉ s.done → ∀ c, 1 ≤ c → c ≤ s.r y → c ≤ s.r y' →
      (edgeGraph ends (cls s c)).Reachable y y') ∧
  (∀ e a b, ends e = s(a, b) → 2 ≤ s.idx e →
      (edgeGraph ends (cls s (s.idx e - 1))).Reachable a b) ∧
  (∀ v, v ∈ s.done → ∀ e, v ∈ ends e → s.idx e ≠ 0)

theorem aux_l24b_mono (ends : E → Sym2 V) (s t : State V E)
    (h : ∀ e, s.idx e ≠ 0 → t.idx e = s.idx e) (c : ℕ) (hc : 1 ≤ c) :
    edgeGraph ends (cls s c) ≤ edgeGraph ends (cls t c) := by
  unfold edgeGraph
  apply SimpleGraph.fromEdgeSet_mono
  apply Set.image_mono
  intro e he
  simp only [cls, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he ⊢
  rw [h e (by omega)]
  exact he

theorem aux_l24b_init (ends : E → Sym2 V) : aux_l24b_Inv ends (init : State V E) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp [init] at hx
  · intro y y' _ _ c hc hcy _
    simp only [init] at hcy
    omega
  · intro e a b _ h2
    simp only [init] at h2
    omega
  · intro v hv
    simp [init] at hv

theorem aux_l24b_step (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (s t : State V E) (hs : aux_l24b_Inv ends s) (hst : Step ends s t) :
    aux_l24b_Inv ends t := by
  obtain ⟨hA, hB, hC, hD⟩ := hs
  rcases hst with ⟨x, hcur, hxd, hmax, rfl⟩ | ⟨x, y, e, hcur, he0, hends, rfl⟩ |
      ⟨x, hcur, hall, rfl⟩
  · -- select
    refine ⟨?_, hB, hC, hD⟩
    intro z hz
    simp only [Option.some.injEq] at hz
    subst hz
    exact ⟨hxd, hmax⟩
  · -- scan
    have hxy : x ≠ y := by
      intro hxy
      apply hloop e
      rw [hends, hxy]
      exact Sym2.mk_isDiag_iff.mpr rfl
    have hxd : x ∉ s.done := (hA x hcur).1
    have hrxy : ∀ z, z ∉ s.done → s.r z ≤ s.r x := (hA x hcur).2
    have hyd : y ∉ s.done := by
      intro hy
      exact hD y hy e (by rw [hends]; exact Sym2.mem_mk_right x y) he0
    set t : State V E := { s with
      idx := Function.update s.idx e (s.r y + 1),
      r := Function.update
        (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
        y (s.r y + 1) } with ht
    have htidx_e : t.idx e = s.r y + 1 := by
      simp [ht]
    have htidx_ne : ∀ e', e' ≠ e → t.idx e' = s.idx e' := by
      intro e' hne
      simp [ht, Function.update_of_ne hne]
    have hmono : ∀ c, 1 ≤ c → edgeGraph ends (cls s c) ≤ edgeGraph ends (cls t c) := by
      intro c hc
      apply aux_l24b_mono ends s t _ c hc
      intro e' he'
      by_cases hee : e' = e
      · subst hee; exact absurd he0 he'
      · exact htidx_ne e' hee
    have hry : t.r y = s.r y + 1 := by simp [ht]
    have hrx : t.r x = if s.r x = s.r y then s.r x + 1 else s.r x := by
      simp [ht, Function.update_of_ne hxy]
    have hro : ∀ z, z ≠ x → z ≠ y → t.r z = s.r z := by
      intro z hzx hzy
      simp [ht, Function.update_of_ne hzx, Function.update_of_ne hzy]
    have htdone : t.done = s.done := rfl
    have htcur : t.cur = s.cur := rfl
    have hadj : (edgeGraph ends (cls t (s.r y + 1))).Adj x y := by
      rw [edgeGraph, SimpleGraph.fromEdgeSet_adj]
      refine ⟨⟨e, ?_, hends⟩, hxy⟩
      simp [cls, htidx_e]
    have key : ∀ z, z ∉ s.done → ∀ c, 1 ≤ c → c ≤ t.r z →
        (edgeGraph ends (cls t c)).Reachable z x := by
      intro z hz c hc hcz
      by_cases hzx : z = x
      · subst hzx; exact SimpleGraph.Reachable.refl _
      by_cases hzy : z = y
      · subst hzy
        rw [hry] at hcz
        by_cases hle : c ≤ s.r z
        · exact (hB z x hz hxd c hc hle (le_trans hle (hrxy z hz))).mono (hmono c hc)
        · have hc' : c = s.r z + 1 := by omega
          subst hc'
          exact hadj.symm.reachable
      · rw [hro z hzx hzy] at hcz
        exact (hB z x hz hxd c hc hcz (le_trans hcz (hrxy z hz))).mono (hmono c hc)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      rw [htcur, hcur] at hz
      simp only [Option.some.injEq] at hz
      subst hz
      refine ⟨hxd, ?_⟩
      intro y' hy'
      rw [htdone] at hy'
      by_cases hy'x : y' = x
      · subst hy'x; exact le_refl _
      by_cases hy'y : y' = y
      · subst hy'y
        rw [hry, hrx]
        have := hrxy y' hyd
        split_ifs <;> omega
      · rw [hro y' hy'x hy'y, hrx]
        have := hrxy y' hy'
        split_ifs <;> omega
    · intro y1 y2 h1 h2 c hc h1c h2c
      rw [htdone] at h1 h2
      exact (key y1 h1 c hc h1c).trans (key y2 h2 c hc h2c).symm
    · intro e' a b hab h2
      by_cases hee : e' = e
      · subst hee
        rw [htidx_e] at h2 ⊢
        have hr1 : 1 ≤ s.r y := by omega
        have hyx := key y hyd (s.r y) hr1 (by rw [hry]; omega)
        rw [show s.r y + 1 - 1 = s.r y by omega]
        rw [hends] at hab
        rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; subst h2; exact hyx.symm
        · subst h1; subst h2; exact hyx
      · rw [htidx_ne e' hee] at h2 ⊢
        exact (hC e' a b hab h2).mono (hmono _ (by omega))
    · intro v hv e' hve'
      rw [htdone] at hv
      by_cases hee : e' = e
      · subst hee; rw [htidx_e]; omega
      · rw [htidx_ne e' hee]; exact hD v hv e' hve'
  · -- finish
    refine ⟨?_, ?_, hC, ?_⟩
    · intro z hz
      simp at hz
    · intro y y' hy hy' c hc h1 h2
      simp only [Finset.mem_insert, not_or] at hy hy'
      exact hB y y' hy.2 hy'.2 c hc h1 h2
    · intro v hv e he
      simp only [Finset.mem_insert] at hv
      rcases hv with hv | hv
      · subst hv; exact hall e he
      · exact hD v hv e he

theorem aux_l24b_run (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → aux_l24b_Inv ends (σ k) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [hrun.1]
    exact aux_l24b_init ends
  | succ n ih =>
    intro hn
    exact aux_l24b_step ends hloop _ _ (ih (by omega)) (hrun.2 n (by omega))

theorem aux_l24b_down1 (ends : E → Sym2 V) (s : State V E)
    (hC : ∀ e a b, ends e = s(a, b) → 2 ≤ s.idx e →
      (edgeGraph ends (cls s (s.idx e - 1))).Reachable a b)
    (j : ℕ) (hj : 2 ≤ j) (u v : V) (h : (edgeGraph ends (cls s j)).Reachable u v) :
    (edgeGraph ends (cls s (j - 1))).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih =>
    refine ih.trans ?_
    rw [edgeGraph, SimpleGraph.fromEdgeSet_adj] at hbc
    obtain ⟨⟨e, he, hends⟩, _⟩ := hbc
    simp only [cls, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he
    have := hC e _ _ hends (by omega)
    rw [he] at this
    exact this

theorem aux_l24b_down (ends : E → Sym2 V) (s : State V E)
    (hC : ∀ e a b, ends e = s(a, b) → 2 ≤ s.idx e →
      (edgeGraph ends (cls s (s.idx e - 1))).Reachable a b)
    (i : ℕ) (hi : 1 ≤ i) (u v : V) :
    ∀ n, (edgeGraph ends (cls s (i + n))).Reachable u v →
      (edgeGraph ends (cls s i)).Reachable u v := by
  intro n
  induction n with
  | zero => intro h; simpa using h
  | succ n ih =>
    intro h
    apply ih
    have := aux_l24b_down1 ends s hC (i + (n + 1)) (by omega) u v h
    rw [show i + (n + 1) - 1 = i + n by omega] at this
    exact this

end aux_l24b

end NagamochiIbaraki.NodeConn

open NagamochiIbaraki.NodeConn

theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ (i j : ℕ) (u v : V), 1 ≤ i → i < j → j ≤ Fintype.card E →
      (edgeGraph ends (cls (σ k) j)).Reachable u v →
        (edgeGraph ends (cls (σ k) i)).Reachable u v := by
  intro k hk i j u v hi hij _ h
  have hinv := aux_l24b_run ends hloop σ K hrun k hk
  have := aux_l24b_down ends (σ k) hinv.2.2.1 i hi u v (j - i)
  rw [show i + (j - i) = j by omega] at this
  exact this h
