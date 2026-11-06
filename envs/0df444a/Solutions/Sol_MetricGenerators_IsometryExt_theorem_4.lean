-- Prove2me | solution 1 for MetricGenerators.IsometryExt.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:55:47.0102+00:00
-- url     : https://prove2.me/submissions/c46d6897-329a-496b-9c7c-0f506fef91a6

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation
import Theorems.Thm_MetricGenerators_IsometryExt_strong_is_metric_generator
import Theorems.Thm_MetricGenerators_IsometryExt_represents_singleton_disjoint
import Theorems.Thm_MetricGenerators_IsometryExt_lemma_1
import Theorems.Thm_MetricGenerators_IsometryExt_represents_subset_cStar
import Theorems.Thm_MetricGenerators_IsometryExt_candidates_stabilize

open SimpleGraph

private theorem forest_choice {W X : Type*} [Fintype W] (F : SimpleGraph W) (hF : F.IsAcyclic)
    (R : X → X → Prop) (hR : ∀ x y, R x y → R y x) (C : W → Set X)
    (hC : ∀ u v, F.Adj u v → ∀ x ∈ C u, ∃ y ∈ C v, R x y) (hne : ∀ w, (C w).Nonempty) :
    ∃ φ : W → X, (∀ w, φ w ∈ C w) ∧ ∀ u v, F.Adj u v → R (φ u) (φ v) := by
  classical
  -- strengthened statement over finite edge sets
  have key : ∀ s : Finset (Sym2 W), ∀ w, ∀ x ∈ C w, ∃ φ : W → X, (∀ v, φ v ∈ C v) ∧ φ w = x ∧
      ∀ u v, F.Adj u v → s(u, v) ∈ s → R (φ u) (φ v) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro w x hx
      refine ⟨fun v => if v = w then x else (hne v).some, ?_, by simp, by simp⟩
      intro v; by_cases h : v = w
      · subst h; simpa using hx
      · simpa [h] using (hne v).some_mem
    | @insert e s he ih =>
      induction e using Sym2.ind with
      | h a b =>
      by_cases hab : F.Adj a b
      swap
      · intro w x hx
        obtain ⟨φ, h1, h2, h3⟩ := ih w x hx
        refine ⟨φ, h1, h2, ?_⟩
        intro u v huv hmem
        rcases Finset.mem_insert.1 hmem with h | h
        · exfalso; rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hab huv
          · exact hab huv.symm
        · exact h3 u v huv h
      -- the subgraph with edges from s
      set Fs : SimpleGraph W := F ⊓ fromEdgeSet (↑s : Set (Sym2 W)) with hFs
      have hFsadj : ∀ u v, Fs.Adj u v ↔ F.Adj u v ∧ s(u, v) ∈ s := by
        intro u v
        simp only [hFs, inf_adj, fromEdgeSet_adj, Finset.mem_coe]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h1.ne⟩
      have hbr : ¬ Fs.Reachable a b := by
        have := (isAcyclic_iff_forall_adj_isBridge.1 hF) hab
        rw [isBridge_iff] at this
        intro hr
        apply this
        refine hr.mono ?_
        intro u v huv
        rw [hFsadj] at huv
        rw [deleteEdges_adj]
        refine ⟨huv.1, ?_⟩
        intro hm
        rw [Set.mem_singleton_iff] at hm
        rw [hm] at huv
        exact he huv.2
      -- K = component of b
      let K : Set W := {v | Fs.Reachable b v}
      have hbK : b ∈ K := Reachable.refl b
      have haK : a ∉ K := fun h => hbr (h.symm)
      have hKclosed : ∀ u v, Fs.Adj u v → (u ∈ K ↔ v ∈ K) := by
        intro u v huv
        constructor
        · intro hu; exact hu.trans huv.reachable
        · intro hv; exact hv.trans huv.symm.reachable
      have combine : ∀ φ1 φ2 : W → X, (∀ v, φ1 v ∈ C v) → (∀ v, φ2 v ∈ C v) →
          (∀ u v, F.Adj u v → s(u, v) ∈ s → R (φ1 u) (φ1 v)) →
          (∀ u v, F.Adj u v → s(u, v) ∈ s → R (φ2 u) (φ2 v)) →
          R (φ1 a) (φ2 b) →
          ∃ φ : W → X, (∀ v, φ v ∈ C v) ∧ (∀ v, v ∈ K → φ v = φ2 v) ∧
            (∀ v, v ∉ K → φ v = φ1 v) ∧
            ∀ u v, F.Adj u v → s(u, v) ∈ insert s(a, b) s → R (φ u) (φ v) := by
        intro φ1 φ2 c1 c2 r1 r2 rab
        refine ⟨fun v => if v ∈ K then φ2 v else φ1 v, ?_, ?_, ?_, ?_⟩
        · intro v; by_cases hv : v ∈ K <;> simp [hv, c1, c2]
        · intro v hv; simp [hv]
        · intro v hv; simp [hv]
        · intro u v huv hmem
          rcases Finset.mem_insert.1 hmem with h | h
          · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simp only [haK, hbK, if_true, if_false]; exact rab
            · simp only [haK, hbK, if_true, if_false]; exact hR _ _ rab
          · have hk := hKclosed u v ((hFsadj u v).2 ⟨huv, h⟩)
            by_cases hu : u ∈ K
            · have hv : v ∈ K := hk.1 hu
              simp only [hu, hv, if_true]; exact r2 u v huv h
            · have hv : v ∉ K := fun hv => hu (hk.2 hv)
              simp only [hu, hv, if_false]; exact r1 u v huv h
      intro w x hx
      by_cases hw : w ∈ K
      · obtain ⟨φ2, c2, e2, r2⟩ := ih w x hx
        obtain ⟨x', hx', hr'⟩ := hC b a hab.symm (φ2 b) (c2 b)
        obtain ⟨φ1, c1, e1, r1⟩ := ih a x' hx'
        obtain ⟨φ, hc, hK, -, hr⟩ := combine φ1 φ2 c1 c2 r1 r2 (by rw [e1]; exact hR _ _ hr')
        exact ⟨φ, hc, by rw [hK w hw, e2], hr⟩
      · obtain ⟨φ1, c1, e1, r1⟩ := ih w x hx
        obtain ⟨y, hy, hr'⟩ := hC a b hab (φ1 a) (c1 a)
        obtain ⟨φ2, c2, e2, r2⟩ := ih b y hy
        obtain ⟨φ, hc, -, hK, hr⟩ := combine φ1 φ2 c1 c2 r1 r2 (by rw [e2]; exact hr')
        exact ⟨φ, hc, by rw [hK w hw, e1], hr⟩
  by_cases hW : Nonempty W
  · obtain ⟨w⟩ := hW
    obtain ⟨φ, h1, -, h3⟩ := key Finset.univ w _ (hne w).some_mem
    exact ⟨φ, h1, fun u v huv => h3 u v huv (Finset.mem_univ _)⟩
  · refine ⟨fun w => (hW ⟨w⟩).elim, fun w => (hW ⟨w⟩).elim, fun u => (hW ⟨u⟩).elim⟩

open MetricGenerators.IsometryExt in
private theorem cand_sub_candSet {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG)
    (T : Finset VH) (f : ↥T → VG) (i : ℕ) (u : VH) : cand H G T f i u ⊆ candSet H G T f i := by
  cases i with
  | zero =>
    intro x hx
    simp only [cand, candSet, candidates] at hx ⊢
    exact Set.mem_iUnion.2 ⟨u, hx⟩
  | succ i =>
    intro x hx
    simp only [cand, candSet, candidates] at hx ⊢
    exact hx.2

open MetricGenerators.IsometryExt in
theorem solution {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsStrongMetricGenerator H T)
    (hforest : (H.induce ((↑T : Set VH)ᶜ)).IsAcyclic)
    (f : ↥T → VG) (hf : IsIsometryOn H G T f) :
    ((∃ φ : VH → VG, IsIsometry H G φ ∧ Extends T f φ) ↔
      (∃ C : VH → Set VG, Represents H G T f C)) ∧
    ((∃ φ : VH → VG, IsIsometry H G φ ∧ Extends T f φ) →
      Represents H G T f (cStar H G T f) ∧
      ∀ C : VH → Set VG, Represents H G T f C → ∀ u : VH, C u ⊆ cStar H G T f u) := by
  classical
  -- necessity: an isometric extension gives the singleton representation
  have nec : (∃ φ : VH → VG, IsIsometry H G φ ∧ Extends T f φ) →
      (∃ C : VH → Set VG, Represents H G T f C) := by
    rintro ⟨φ, hφ, hext⟩
    refine ⟨fun u => {φ u}, fun u => Set.singleton_nonempty _, ?_, ?_⟩
    · intro t u x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [← hext t]; exact hφ t u
    · intro u v huv x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨φ v, rfl, ?_⟩
      rw [← SimpleGraph.dist_eq_one_iff_adj, hφ u v, SimpleGraph.dist_eq_one_iff_adj]
      exact huv
  refine ⟨⟨nec, ?_⟩, ?_⟩
  · -- sufficiency: choose along the forest H − T
    rintro ⟨C, hC⟩
    have hsd := represents_singleton_disjoint H G hH hG T
      (strong_is_metric_generator H hH T hT) f hf C hC
    have hL1 := lemma_1 H G hH hG T hT f hf C hC
    obtain ⟨hne, hi, hii⟩ := hC
    let W := ↥((↑T : Set VH)ᶜ)
    obtain ⟨ψ, hψC, hψadj⟩ := forest_choice (H.induce ((↑T : Set VH)ᶜ)) hforest G.Adj
      (fun x y h => h.symm) (fun w : W => C w.1)
      (fun u v huv x hx => hii u.1 v.1 (by simpa using huv) x hx) (fun w => hne w.1)
    let φ : VH → VG := fun u => if h : u ∈ T then f ⟨u, h⟩ else ψ ⟨u, h⟩
    have hφC : ∀ u, φ u ∈ C u := by
      intro u
      by_cases h : u ∈ T
      · simp only [φ, h, dif_pos]
        rw [(hsd.1 ⟨u, h⟩)]; rfl
      · simp only [φ, h, dif_neg, not_false_eq_true]
        exact hψC ⟨u, h⟩
    have hadj : ∀ u v, H.Adj u v → G.Adj (φ u) (φ v) := by
      intro u v huv
      by_cases hu : u ∈ T
      · have := hi ⟨u, hu⟩ v (φ v) (hφC v)
        have e : φ u = f ⟨u, hu⟩ := by simp [φ, hu]
        rw [e, ← SimpleGraph.dist_eq_one_iff_adj, this]
        exact SimpleGraph.dist_eq_one_iff_adj.2 huv
      by_cases hv : v ∈ T
      · have := hi ⟨v, hv⟩ u (φ u) (hφC u)
        have e : φ v = f ⟨v, hv⟩ := by simp [φ, hv]
        rw [e, ← SimpleGraph.dist_eq_one_iff_adj, SimpleGraph.dist_comm, this]
        exact SimpleGraph.dist_eq_one_iff_adj.2 huv.symm
      · have e1 : φ u = ψ ⟨u, hu⟩ := by simp [φ, hu]
        have e2 : φ v = ψ ⟨v, hv⟩ := by simp [φ, hv]
        rw [e1, e2]
        exact hψadj ⟨u, hu⟩ ⟨v, hv⟩ (by simpa using huv)
    refine ⟨φ, ?_, ?_⟩
    · intro u v
      apply le_antisymm
      · obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist u v
        let g : H →g G := ⟨φ, fun h => hadj _ _ h⟩
        have := SimpleGraph.dist_le (p.map g)
        rw [SimpleGraph.Walk.length_map, hp] at this
        exact this
      · exact (hL1 u v (φ u) (hφC u)).2 (φ v) (hφC v)
    · intro t
      simp [φ]
  · intro hex
    have hsub : ∀ C : VH → Set VG, Represents H G T f C → ∀ u : VH, C u ⊆ cStar H G T f u :=
      fun C hC => represents_subset_cStar H G hH hG T hT f hf C hC
    obtain ⟨C, hC⟩ := nec hex
    refine ⟨⟨?_, ?_, ?_⟩, hsub⟩
    · intro u
      exact (hC.1 u).mono (hsub C hC u)
    · have hstab := candidates_stabilize H G hH hG T f
      have hdec : ∀ i u, cand H G T f i u ⊆ cand H G T f 0 u := by
        intro i
        induction i with
        | zero => intro u; exact subset_rfl
        | succ i ih => intro u; exact (hstab.1 i).2 u |>.trans (ih u)
      intro t u x hx
      have hx0 := hdec _ u hx
      simp only [cand, candidates, initialCandidates] at hx0
      exact hx0 t
    · intro u v huv x hx
      have hstab := candidates_stabilize H G hH hG T f
      set n := Fintype.card VG
      have hxS : x ∈ candSet H G T f (n + 1) := by
        rw [(hstab.2 (n + 1) (Nat.le_succ n)).1]
        exact cand_sub_candSet H G T f n u hx
      simp only [candSet, candidates] at hxS
      exact hxS.2 u v hx huv
