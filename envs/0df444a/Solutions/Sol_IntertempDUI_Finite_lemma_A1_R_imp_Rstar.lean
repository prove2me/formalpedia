-- Prove2me | solution 1 for IntertempDUI.Finite.lemma_A1_R_imp_Rstar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:19:37.105675+00:00
-- url     : https://prove2.me/submissions/b63a64a0-d251-4bf4-986a-ca2516e35ffe

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

open IntertempDUI.Finite

namespace IDUISpanK1

variable {T : ℝ}

/-- A bracket is the preimage of an open interval of `ℝ`. -/
lemma bracket_eq_preimage (r s : ℝ) :
    bracket T r s = Subtype.val ⁻¹' Set.Ioo (if r = 0 then -1 else r) (if s = T then T + 1 else s) := by
  ext x
  simp only [bracket, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioo]
  have h0 := x.2.1
  have h1 := x.2.2
  constructor
  · rintro ⟨h2, h3⟩
    constructor
    · split_ifs with hr
      · linarith
      · rcases h2 with h2 | h2
        · exact h2
        · exact absurd h2.1 hr
    · split_ifs with hs
      · linarith
      · rcases h3 with h3 | h3
        · exact h3
        · exact absurd h3.1 hs
  · rintro ⟨h2, h3⟩
    constructor
    · split_ifs at h2 with hr
      · rcases lt_or_eq_of_le h0 with h | h
        · left; rw [hr]; exact h
        · right; exact ⟨hr, h.symm⟩
      · left; exact h2
    · split_ifs at h3 with hs
      · rcases lt_or_eq_of_le h1 with h | h
        · left; rw [hs]; exact h
        · right; exact ⟨hs, h⟩
      · left; exact h3

lemma isOpen_bracket (r s : ℝ) : IsOpen (bracket T r s) := by
  rw [bracket_eq_preimage]
  exact isOpen_Ioo.preimage continuous_subtype_val

lemma isPreconnected_bracket (hT : 0 ≤ T) (r s : ℝ) : IsPreconnected (bracket T r s) := by
  rw [bracket_eq_preimage]
  set J := Set.Ioo (if r = 0 then -1 else r) (if s = T then T + 1 else s) with hJ
  have : Subtype.val ⁻¹' J = Set.projIcc (0:ℝ) T hT '' (J ∩ Set.Icc 0 T) := by
    ext x
    constructor
    · intro hx
      exact ⟨x.1, ⟨hx, x.2⟩, Set.projIcc_val _ _⟩
    · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
      simp only [Set.mem_preimage, Set.projIcc_of_mem _ hy']
      exact hy
  rw [this]
  exact (Set.OrdConnected.isPreconnected (Set.OrdConnected.inter (Set.ordConnected_Ioo)
    (Set.ordConnected_Icc))).image _ continuous_projIcc.continuousOn

/-- Points of the real closed interval `[r,s]` lie in the closure of the bracket. -/
lemma mem_closure_bracket {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ T)
    (x : Time T) (hx1 : r ≤ x.1) (hx2 : x.1 ≤ s) : x ∈ closure (bracket T r s) := by
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have hsub : Set.Ioo r s ⊆ Subtype.val '' bracket T r s := by
    intro y hy
    refine ⟨⟨y, by linarith [hy.1], by linarith [hy.2]⟩, ?_, rfl⟩
    simp only [bracket, Set.mem_ofPred_eq]
    exact ⟨Or.inl hy.1, Or.inl hy.2⟩
  have := closure_mono hsub
  rw [closure_Ioo hrs.ne] at this
  exact this ⟨hx1, hx2⟩

/-- Order facts for a sorted, separated family of brackets. -/
lemma lt_of_sep {N : ℕ} {s t : Fin N → ℝ}
    (hst : ∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) (hsep : ∀ i j : Fin N, i < j → t i < s j)
    {i j : Fin N} (hij : i < j) : t i < s j ∧ s i < s j ∧ t i < t j :=
  ⟨hsep i j hij, lt_trans (hst i).2.1 (hsep i j hij), lt_trans (hsep i j hij) (hst j).2.1⟩

/-- Components of a time span are exactly its constituent brackets. -/
lemma component_eq {N : ℕ} {s t : Fin N → ℝ} (hT : 0 < T)
    (hst : ∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) (hsep : ∀ i j : Fin N, i < j → t i < s j)
    (I : Set (Time T)) (hI : IsComponent (⋃ i, bracket T (s i) (t i)) I) :
    ∃ i, I = bracket T (s i) (t i) := by
  obtain ⟨t0, ht0, rfl⟩ := hI
  set S := ⋃ i, bracket T (s i) (t i) with hS
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ht0
  refine ⟨i, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxi
    have hC := isPreconnected_connectedComponentIn (F := S) (x := t0)
    have ht0C : t0 ∈ connectedComponentIn S t0 := mem_connectedComponentIn ht0
    have hCS : connectedComponentIn S t0 ⊆ S := connectedComponentIn_subset _ _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hCS hx)
    have hji : j ≠ i := by rintro rfl; exact hxi hj
    simp only [bracket, Set.mem_ofPred_eq] at hi hj
    rcases lt_or_gt_of_ne hji with hlt | hlt
    · -- j < i : the point s i separates x and t0
      obtain ⟨h1, h2, h3⟩ := lt_of_sep hst hsep hlt
      have hsj := hst j
      have hsi := hst i
      have hxlt : x.1 < t j := by
        rcases hj.2 with h | h
        · exact h
        · linarith [h.1]
      have ht0gt : s i < t0.1 := by
        rcases hi.1 with h | h
        · exact h
        · linarith [h.1]
      let p : Time T := ⟨s i, by linarith, by linarith⟩
      have hp : p ∈ connectedComponentIn S t0 :=
        hC.Icc_subset hx ht0C ⟨show x.1 ≤ s i by linarith, show s i ≤ t0.1 by linarith⟩
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hCS hp)
      simp only [bracket, Set.mem_ofPred_eq, p] at hk
      rcases lt_trichotomy k i with hki | rfl | hki
      · obtain ⟨g1, -, -⟩ := lt_of_sep hst hsep hki
        rcases hk.2 with h | h
        · linarith
        · have := hst k; linarith [h.1]
      · rcases hk.1 with h | h
        · linarith
        · linarith [h.1]
      · obtain ⟨g1, g2, -⟩ := lt_of_sep hst hsep hki
        rcases hk.1 with h | h
        · linarith
        · linarith [h.1]
    · -- i < j : the point t i separates t0 and x
      obtain ⟨h1, h2, h3⟩ := lt_of_sep hst hsep hlt
      have hsj := hst j
      have hsi := hst i
      have hxgt : t i < x.1 := by
        rcases hj.1 with h | h
        · linarith
        · linarith [h.1]
      have ht0lt : t0.1 < t i := by
        rcases hi.2 with h | h
        · exact h
        · linarith [h.1]
      let p : Time T := ⟨t i, by linarith, by linarith⟩
      have hp : p ∈ connectedComponentIn S t0 :=
        hC.Icc_subset ht0C hx ⟨show t0.1 ≤ t i by linarith, show t i ≤ x.1 by linarith⟩
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hCS hp)
      simp only [bracket, Set.mem_ofPred_eq, p] at hk
      rcases lt_trichotomy k i with hki | rfl | hki
      · obtain ⟨g1, -, g3⟩ := lt_of_sep hst hsep hki
        rcases hk.2 with h | h
        · linarith
        · linarith [h.1]
      · rcases hk.2 with h | h
        · linarith
        · linarith [h.1]
      · obtain ⟨g1, g2, -⟩ := lt_of_sep hst hsep hki
        rcases hk.1 with h | h
        · linarith
        · have := hst k; linarith [h.2]
  · exact (isPreconnected_bracket hT.le _ _).subset_connectedComponentIn hi
      (Set.subset_iUnion (fun i => bracket T (s i) (t i)) i)

end IDUISpanK1

open IDUISpanK1 in
theorem solution {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : Richness A pref) :
    RichnessStar A pref := by
  intro Q R hQ hRs hQR a ha b hb
  obtain ⟨N, s, t, hst, hsep, rfl⟩ := hRs
  have hQo : IsOpen Q := by
    obtain ⟨M, s', t', -, -, rfl⟩ := hQ
    exact isOpen_iUnion fun i => isOpen_bracket _ _
  -- interval-ness of each bracket
  have hint : ∀ j, IsTimeInterval (bracket T (s j) (t j)) := fun j =>
    ⟨s j, t j, (hst j).1, (hst j).2.1, (hst j).2.2, rfl⟩
  have key : ∀ k, k ≤ N → ∃ g ∈ A, Set.EqOn g a Q ∧
      ∀ j : Fin N, j.1 < k → indiff pref (bracket T (s j) (t j)) g b := by
    intro k
    induction k with
    | zero => intro _; exact ⟨a, ha, fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgQ, hgj⟩ := ih (Nat.le_of_succ_le hk)
      set j0 : Fin N := ⟨k, hk⟩ with hj0
      obtain ⟨h0, h1, h2⟩ := hst j0
      obtain ⟨f, hf, hfl, hfm, hfr⟩ := hR 0 (s j0) (t j0) T (le_refl _) h0 h1 h2 (le_refl _)
        g hg b hb g hg
      -- f agrees with g outside the closed real interval [s j0, t j0]
      have hout : ∀ x : Time T, (x.1 < s j0 ∨ t j0 < x.1) → f x = g x := by
        intro x hx
        rcases hx with hx | hx
        · apply hfl
          simp only [bracket, Set.mem_ofPred_eq]
          refine ⟨?_, Or.inl hx⟩
          rcases lt_or_eq_of_le x.2.1 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨trivial, h.symm⟩
        · apply hfr
          simp only [bracket, Set.mem_ofPred_eq]
          refine ⟨Or.inl hx, ?_⟩
          rcases lt_or_eq_of_le x.2.2 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨trivial, h⟩
      refine ⟨f, hf, ?_, ?_⟩
      · intro x hx
        rw [hout x ?_, hgQ hx]
        by_contra hc
        push Not at hc
        have hdisj : Disjoint Q (bracket T (s j0) (t j0)) :=
          Disjoint.mono_right (Set.subset_iUnion (fun i => bracket T (s i) (t i)) j0) hQR
        have hcl := (hdisj.closure_right hQo)
        exact Set.disjoint_left.1 hcl hx (mem_closure_bracket h0 h1 h2 x hc.1 hc.2)
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · -- an earlier component: f = g there
          have hjj0 : j < j0 := by rw [Fin.lt_def]; exact hj
          obtain ⟨g1, -, -⟩ := lt_of_sep hst hsep hjj0
          have hfg : Set.EqOn f g (bracket T (s j) (t j)) := by
            intro x hx
            apply hout
            left
            simp only [bracket, Set.mem_ofPred_eq] at hx
            rcases hx.2 with h | h
            · linarith
            · linarith [h.1, h.2, (hst j0).2.2, (hst j0).2.1]
          obtain ⟨-, -, -, hres⟩ := hstd _ (hint j)
          have e1 := hres f hf b hb g hg b hb hfg (fun _ _ => rfl)
          have e2 := hres b hb f hf b hb g hg (fun _ _ => rfl) hfg
          obtain ⟨i1, i2⟩ := hgj j hj
          exact ⟨e1.2 i1, e2.2 i2⟩
        · have : j = j0 := Fin.ext hj
          rw [this]; exact hfm
  obtain ⟨g, hg, hgQ, hgj⟩ := key N (le_refl _)
  refine ⟨g, hg, hgQ, ?_⟩
  intro I hI
  obtain ⟨j, rfl⟩ := component_eq hT hst hsep I hI
  exact hgj j j.2
