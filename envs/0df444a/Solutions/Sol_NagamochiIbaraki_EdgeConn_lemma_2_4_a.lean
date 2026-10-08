-- Prove2me | solution 1 for NagamochiIbaraki.EdgeConn.lemma_2_4_a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:20:11.789966+00:00
-- url     : https://prove2.me/submissions/a0bde3f6-a282-45c2-a646-7dfa206d6a53

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NI24aHelpers

open NagamochiIbaraki.EdgeConn

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

def Inv (ends : E → Sym2 V) (s : State V E) : Prop :=
  (∀ x, s.cur = some x → x ∉ s.done ∧ ∀ z, z ∉ s.done → s.r z ≤ s.r x) ∧
  (∀ i, 1 ≤ i → ∀ y z, y ∉ s.done → z ∉ s.done → i ≤ s.r y → i ≤ s.r z →
      (edgeGraph ends (cls s i)).Reachable y z) ∧
  (∀ e, s.idx e ≠ 0 → ∀ i, 1 ≤ i → i < s.idx e → ∀ a b, ends e = s(a, b) →
      (edgeGraph ends (cls s i)).Reachable a b) ∧
  (∀ v, v ∈ s.done → ∀ e, v ∈ ends e → s.idx e ≠ 0)

lemma edgeGraph_mono' (ends : E → Sym2 V) {F G : Finset E} (h : F ⊆ G) :
    edgeGraph ends F ≤ edgeGraph ends G := by
  unfold edgeGraph
  exact SimpleGraph.fromEdgeSet_mono (Set.image_mono (by exact_mod_cast h))

lemma cls_mono {s t : State V E} (h : ∀ e, s.idx e ≠ 0 → t.idx e = s.idx e) {i : ℕ}
    (hi : 1 ≤ i) : cls s i ⊆ cls t i := by
  intro e he
  simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  rw [h e (by omega)]
  exact he

lemma reach_mono (ends : E → Sym2 V) {s t : State V E}
    (h : ∀ e, s.idx e ≠ 0 → t.idx e = s.idx e) {i : ℕ} (hi : 1 ≤ i) {a b : V}
    (hr : (edgeGraph ends (cls s i)).Reachable a b) :
    (edgeGraph ends (cls t i)).Reachable a b :=
  hr.mono (edgeGraph_mono' ends (cls_mono h hi))

lemma adj_of (ends : E → Sym2 V) (s : State V E) (e : E) (i : ℕ) (x y : V)
    (hi : s.idx e = i) (he : ends e = s(x, y)) (hxy : x ≠ y) :
    (edgeGraph ends (cls s i)).Adj x y := by
  unfold edgeGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨⟨e, ?_, he⟩, hxy⟩
  simp [cls, hi]

lemma inv_init (ends : E → Sym2 V) : Inv ends (init : State V E) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx; simp [init] at hx
  · intro i hi y z _ _ hy _; simp [init] at hy; omega
  · intro e he; simp [init] at he
  · intro v hv; simp [init] at hv

lemma inv_step (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (s t : State V E) (hs : Inv ends s) (hst : Step ends s t) : Inv ends t := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rcases hst with ⟨x, hcur, hxd, hmax, rfl⟩ | ⟨x, y, e, hcur, he0, hends, rfl⟩ |
      ⟨x, hcur, hall, rfl⟩
  · refine ⟨?_, h2, h3, h4⟩
    intro x' hx'
    simp only [Option.some.injEq] at hx'
    subst hx'
    exact ⟨hxd, hmax⟩
  · have hxy : x ≠ y := by
      intro h; apply hloop e; rw [hends, h]; exact Sym2.mk_isDiag_iff.mpr rfl
    obtain ⟨hxd, hmax⟩ := h1 x hcur
    have hyd : y ∉ s.done := by
      intro hy; exact h4 y hy e (by rw [hends]; exact Sym2.mem_mk_right x y) he0
    have hmono : ∀ e', s.idx e' ≠ 0 →
        (Function.update s.idx e (s.r y + 1)) e' = s.idx e' := by
      intro e' he'
      have : e' ≠ e := by rintro rfl; exact he' he0
      simp [this]
    have hrx : (Function.update
        (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
        y (s.r y + 1)) x = (if s.r x = s.r y then s.r x + 1 else s.r x) := by
      simp [hxy]
    have hry : (Function.update
        (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
        y (s.r y + 1)) y = s.r y + 1 := by
      simp
    have hrz : ∀ z, z ≠ x → z ≠ y → (Function.update
        (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
        y (s.r y + 1)) z = s.r z := by
      intro z hzx hzy
      simp [hzx, hzy]
    have hyx := hmax y hyd
    -- key claim
    have claim : ∀ i, 1 ≤ i → ∀ w, w ∉ s.done →
        i ≤ (Function.update
          (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
          y (s.r y + 1)) w →
        (edgeGraph ends (cls ({ s with
              idx := Function.update s.idx e (s.r y + 1),
              r := Function.update
                (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
                y (s.r y + 1) } : State V E) i)).Reachable w x := by
      intro i hi w hw hiw
      by_cases hwx : w = x
      · subst hwx; rfl
      by_cases hwy : w = y
      · subst hwy
        rw [hry] at hiw
        by_cases hlt : i ≤ s.r w
        · exact reach_mono ends hmono hi (h2 i hi w x hw hxd hlt (le_trans hlt hyx))
        · have hieq : i = s.r w + 1 := by omega
          apply SimpleGraph.Adj.reachable
          apply (adj_of ends _ e i x w _ hends hxy).symm
          simp [hieq]
      · rw [hrz w hwx hwy] at hiw
        exact reach_mono ends hmono hi
          (h2 i hi w x hw hxd hiw (le_trans hiw (hmax w hw)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x' hx'
      simp only at hx'
      rw [hcur, Option.some.injEq] at hx'
      subst hx'
      refine ⟨hxd, ?_⟩
      intro z hz
      simp only at hz ⊢
      rw [hrx]
      by_cases hzx : z = x
      · subst hzx; rw [hrx]
      by_cases hzy : z = y
      · subst hzy; rw [hry]; split_ifs <;> omega
      · rw [hrz z hzx hzy]
        have := hmax z hz
        split_ifs <;> omega
    · intro i hi y' z hy' hz hiy hiz
      exact (claim i hi y' hy' hiy).trans (claim i hi z hz hiz).symm
    · intro e' he' i hi hie a b hab
      simp only at he' hie ⊢
      by_cases hee : e' = e
      · subst hee
        simp only [Function.update_self] at hie
        rw [hends] at hab
        have hxy' : (edgeGraph ends (cls s i)).Reachable x y :=
          h2 i hi x y hxd hyd (by omega) (by omega)
        rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact reach_mono ends hmono hi hxy'
        · exact reach_mono ends hmono hi hxy'.symm
      · have hid : Function.update s.idx e (s.r y + 1) e' = s.idx e' := by
          simp [hee]
        rw [hid] at he' hie
        exact reach_mono ends hmono hi (h3 e' he' i hi hie a b hab)
    · intro v hv e' hve
      simp only at hv ⊢
      by_cases hee : e' = e
      · subst hee; simp
      · simp [hee]
        exact h4 v hv e' hve
  · refine ⟨?_, ?_, h3, ?_⟩
    · intro x' hx'; simp at hx'
    · intro i hi y z hy hz hiy hiz
      simp only [Finset.mem_insert, not_or] at hy hz
      exact h2 i hi y z hy.2 hz.2 hiy hiz
    · intro v hv e' hve
      simp only [Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact hall e' hve
      · exact h4 v hv e' hve

lemma inv_run (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → Inv ends (σ k) := by
  intro k
  induction k with
  | zero => intro _; rw [hrun.1]; exact inv_init ends
  | succ n ih =>
    intro hn
    exact inv_step ends hloop _ _ (ih (by omega)) (hrun.2 n (by omega))

end NI24aHelpers

open NagamochiIbaraki.EdgeConn in
theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k < K → ∀ (e : E) (i : ℕ) (u v : V),
      (σ k).idx e = 0 → (σ (k + 1)).idx e = i → ends e = s(u, v) → 2 ≤ i →
        (edgeGraph ends (cls (σ k) (i - 1))).Reachable u v := by
  intro k hk e i u v he0 hei hends hi
  have hinv := NI24aHelpers.inv_run ends hloop σ K hrun k (le_of_lt hk)
  obtain ⟨h1, h2, _, h4⟩ := hinv
  rcases hrun.2 k hk with ⟨x, _, _, _, ht⟩ | ⟨x, y, e', hcur, he0', hends', ht⟩ |
      ⟨x, _, _, ht⟩
  · rw [ht] at hei; simp only at hei; omega
  · by_cases hee : e = e'
    · subst hee
      rw [ht] at hei
      simp only [Function.update_self] at hei
      have hxy : x ≠ y := by
        intro h; apply hloop e; rw [hends', h]; exact Sym2.mk_isDiag_iff.mpr rfl
      obtain ⟨hxd, hmax⟩ := h1 x hcur
      have hyd : y ∉ (σ k).done := by
        intro hy; exact h4 y hy e (by rw [hends']; exact Sym2.mem_mk_right x y) he0
      have hyx := hmax y hyd
      have hr : (edgeGraph ends (cls (σ k) (i - 1))).Reachable x y :=
        h2 (i - 1) (by omega) x y hxd hyd (by omega) (by omega)
      rw [hends'] at hends
      rcases Sym2.eq_iff.mp hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hr
      · exact hr.symm
    · rw [ht] at hei
      simp only [Function.update_of_ne hee] at hei
      omega
  · rw [ht] at hei; simp only at hei; omega
