-- Prove2me | solution 1 for NagamochiIbaraki.EdgeConn.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:28:05.370385+00:00
-- url     : https://prove2.me/submissions/a9f6401a-e7b1-413d-ab2f-6e7f7f381a8c

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

set_option autoImplicit false

namespace NagamochiIbaraki.EdgeConn.L23P

theorem reach_map {V : Type*} (G G' : SimpleGraph V) (φ : V → V)
    (h : ∀ a b, G'.Adj a b → φ a = φ b ∨ G.Adj (φ a) (φ b)) {a b : V}
    (hr : G'.Reachable a b) : G.Reachable (φ a) (φ b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr ⊢
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    rcases h _ _ hbc with h1 | h1
    · rw [← h1]; exact ih
    · exact ih.tail h1

theorem isolated_reach {V : Type*} (G : SimpleGraph V) (y : V) (hy : ∀ w, ¬ G.Adj y w)
    {w : V} (hr : G.Reachable y w) : w = y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => rfl
  | tail _ hbc ih =>
    rw [ih] at hbc
    exact absurd hbc (hy _)

theorem forest_insert {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) (F : Finset E)
    (hF : IsForest ends F) (e : E) (he : e ∉ F) (x y : V) (hxy : x ≠ y)
    (hend : ends e = s(x, y)) (hy : ∀ g ∈ F, y ∉ ends g) :
    IsForest ends (insert e F) := by
  classical
  have iso : ∀ w, ¬ (edgeGraph ends F).Adj y w := by
    intro w hadj
    simp only [edgeGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Finset.mem_coe] at hadj
    obtain ⟨⟨g, hg, hge⟩, -⟩ := hadj
    exact hy g hg (by rw [hge]; exact Sym2.mem_mk_left y w)
  intro f hf u v huv hr
  by_cases hfe : f = e
  · rw [hfe, Finset.erase_insert he] at hr
    rw [hfe, hend] at huv
    rcases Sym2.eq_iff.mp huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2] at hr
      exact hxy (isolated_reach _ y iso hr.symm)
    · rw [← h1, ← h2] at hr
      exact hxy (isolated_reach _ y iso hr)
  · have hfF : f ∈ F := (Finset.mem_insert.mp hf).resolve_left hfe
    rw [Finset.erase_insert_of_ne (Ne.symm hfe)] at hr
    have huy : u ≠ y := fun h => hy f hfF (by rw [huv, ← h]; exact Sym2.mem_mk_left _ _)
    have hvy : v ≠ y := fun h => hy f hfF (by rw [huv, ← h]; exact Sym2.mem_mk_right _ _)
    let φ : V → V := fun a => if a = y then x else a
    have key := reach_map (edgeGraph ends (F.erase f)) _ φ ?_ hr
    · simp only [φ, if_neg huy, if_neg hvy] at key
      exact hF f hfF u v huv key
    · intro a b hab
      simp only [edgeGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Finset.mem_coe,
        Finset.mem_insert] at hab
      obtain ⟨⟨g, hg, hge⟩, hne⟩ := hab
      rcases hg with hg | hg
      · left
        rw [hg, hend] at hge
        rcases Sym2.eq_iff.mp hge with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; simp [φ, hxy]
        · rw [← h1, ← h2]; simp [φ, hxy]
      · right
        have hgF : g ∈ F := Finset.mem_of_mem_erase hg
        have hay : a ≠ y := fun h => hy g hgF (by rw [hge, ← h]; exact Sym2.mem_mk_left _ _)
        have hby : b ≠ y := fun h => hy g hgF (by rw [hge, ← h]; exact Sym2.mem_mk_right _ _)
        simp only [φ, if_neg hay, if_neg hby, edgeGraph, SimpleGraph.fromEdgeSet_adj,
          Set.mem_image, Finset.mem_coe]
        exact ⟨⟨g, hg, hge⟩, hne⟩

def Inv {V E : Type*} [Fintype E] [DecidableEq E] (ends : E → Sym2 V) (s : State V E) :
    Prop :=
  (∀ v ∈ s.done, ∀ e, v ∈ ends e → s.idx e ≠ 0) ∧
  (∀ y, y ∉ s.done → s.cur ≠ some y → ∀ e, y ∈ ends e → s.idx e ≤ s.r y) ∧
  (∀ i, 1 ≤ i → IsForest ends (cls s i))

theorem inv_init {V E : Type*} [Fintype E] [DecidableEq E] (ends : E → Sym2 V) :
    Inv ends (init : State V E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv; simp [init] at hv
  · intro y _ _ e _; simp [init]
  · intro i hi f hf
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    change 0 = i at hf
    omega

theorem inv_step {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (s t : State V E)
    (hs : Inv ends s) (hst : Step ends s t) : Inv ends t := by
  obtain ⟨hB, hA, hC⟩ := hs
  rcases hst with ⟨x, hcur, _, _, ht⟩ | ⟨x, y, e, hcur, he0, hend, ht⟩ | ⟨x, hcur, hall, ht⟩
  · have ht_idx : t.idx = s.idx := by rw [ht]
    have ht_r : t.r = s.r := by rw [ht]
    have ht_done : t.done = s.done := by rw [ht]
    have ht_cls : ∀ i, cls t i = cls s i := by intro i; unfold cls; rw [ht_idx]
    refine ⟨?_, ?_, ?_⟩
    · intro v hv f hf; rw [ht_idx]; rw [ht_done] at hv; exact hB v hv f hf
    · intro w hw _ f hf
      rw [ht_idx, ht_r]; rw [ht_done] at hw
      exact hA w hw (by rw [hcur]; simp) f hf
    · intro i hi; rw [ht_cls]; exact hC i hi
  · have ht_idx : t.idx = Function.update s.idx e (s.r y + 1) := by rw [ht]
    have ht_r : t.r = Function.update
        (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
        y (s.r y + 1) := by rw [ht]
    have ht_done : t.done = s.done := by rw [ht]
    have ht_cur : t.cur = s.cur := by rw [ht]
    have hxy : x ≠ y := by
      intro h; apply hloop e; rw [hend, h]; exact Sym2.mk_isDiag_iff.mpr rfl
    have hyd : y ∉ s.done := fun hy => hB y hy e (by rw [hend]; exact Sym2.mem_mk_right x y) he0
    have hyc : s.cur ≠ some y := by rw [hcur]; simpa using hxy
    refine ⟨?_, ?_, ?_⟩
    · intro v hv f hf
      rw [ht_done] at hv
      rw [ht_idx, Function.update_apply]
      split_ifs
      · omega
      · exact hB v hv f hf
    · intro w hw hwc f hf
      rw [ht_done] at hw
      rw [ht_cur] at hwc
      have hwx : w ≠ x := fun h => hwc (by rw [hcur, h])
      rw [ht_idx, ht_r]
      by_cases hfe : f = e
      · have hwy : w = y := by
          rw [hfe, hend] at hf
          rcases Sym2.mem_iff.mp hf with h | h
          · exact absurd h hwx
          · exact h
        rw [hfe, hwy]; simp
      · rw [Function.update_apply, if_neg hfe]
        have := hA w hw hwc f hf
        rcases eq_or_ne w y with hwy | hwy
        · rw [hwy] at this ⊢; simp only [Function.update_apply, if_pos rfl, ↓reduceIte]; omega
        · simp only [Function.update_apply, if_neg hwy, if_neg hwx]; exact this
    · intro i hi
      have hnot : e ∉ cls s i := by
        simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and, he0]; omega
      by_cases hi' : i = s.r y + 1
      · have heq : cls t i = insert e (cls s i) := by
          ext f
          simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            ht_idx, Function.update_apply]
          by_cases hfe : f = e
          · rw [hfe, if_pos rfl]; simp [hi']
          · rw [if_neg hfe]; simp [hfe]
        rw [heq]
        refine forest_insert ends (cls s i) (hC i hi) e hnot x y hxy hend ?_
        intro g hg hyg
        simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hg
        have := hA y hyd hyc g hyg
        omega
      · have heq : cls t i = cls s i := by
          ext f
          simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and, ht_idx,
            Function.update_apply]
          by_cases hfe : f = e
          · rw [hfe, if_pos rfl, he0]; constructor <;> intro h <;> omega
          · rw [if_neg hfe]
        rw [heq]; exact hC i hi
  · have ht_idx : t.idx = s.idx := by rw [ht]
    have ht_r : t.r = s.r := by rw [ht]
    have ht_done : t.done = insert x s.done := by rw [ht]
    have ht_cur : t.cur = none := by rw [ht]
    have ht_cls : ∀ i, cls t i = cls s i := by intro i; unfold cls; rw [ht_idx]
    refine ⟨?_, ?_, ?_⟩
    · intro v hv f hf
      rw [ht_idx]
      rw [ht_done, Finset.mem_insert] at hv
      rcases hv with hv | hv
      · rw [hv] at hf; exact hall f hf
      · exact hB v hv f hf
    · intro w hw _ f hf
      rw [ht_done, Finset.mem_insert, not_or] at hw
      rw [ht_idx, ht_r]
      exact hA w hw.2 (by rw [hcur]; simpa using Ne.symm hw.1) f hf
    · intro i hi; rw [ht_cls]; exact hC i hi

theorem inv_run {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (σ : ℕ → State V E) (K : ℕ)
    (hrun : IsRun ends σ K) : ∀ k, k ≤ K → Inv ends (σ k) := by
  intro k
  induction k with
  | zero => intro _; rw [hrun.1]; exact inv_init ends
  | succ n ih =>
    intro hn
    exact inv_step ends hloop _ _ (ih (by omega)) (hrun.2 n (by omega))

end NagamochiIbaraki.EdgeConn.L23P

open NagamochiIbaraki.EdgeConn in
theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      IsForest ends (cls (σ k) i) := by
  intro k hk i hi _
  exact (NagamochiIbaraki.EdgeConn.L23P.inv_run ends hloop σ K hrun k hk).2.2 i hi
