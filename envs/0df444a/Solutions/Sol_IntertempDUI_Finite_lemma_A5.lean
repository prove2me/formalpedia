-- Prove2me | solution 1 for IntertempDUI.Finite.lemma_A5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:22:38.152187+00:00
-- url     : https://prove2.me/submissions/fbb862b6-1dac-4c09-906f-4a7bf1ce9100

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

open IntertempDUI.Finite

namespace IDUILib


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

end IDUILib


open IntertempDUI.Finite

namespace IDUILib

variable {T : ℝ}

lemma mem_bracket_left {r : ℝ} (x : Time T) (h : x.1 < r) : x ∈ bracket T 0 r := by
  refine ⟨?_, Or.inl h⟩
  rcases lt_or_eq_of_le x.2.1 with h' | h'
  · exact Or.inl h'
  · exact Or.inr ⟨rfl, h'.symm⟩

lemma mem_bracket_right {s : ℝ} (x : Time T) (h : s < x.1) : x ∈ bracket T s T := by
  refine ⟨Or.inl h, ?_⟩
  rcases lt_or_eq_of_le x.2.2 with h' | h'
  · exact Or.inl h'
  · exact Or.inr ⟨rfl, h'⟩

lemma mem_bracket_left_iff {r : ℝ} (hr : r < T) (x : Time T) :
    x ∈ bracket T 0 r ↔ x.1 < r := by
  refine ⟨fun h => ?_, mem_bracket_left x⟩
  rcases h.2 with h | h
  · exact h
  · exact absurd h.1 hr.ne

lemma mem_bracket_right_iff {s : ℝ} (hs : 0 < s) (x : Time T) :
    x ∈ bracket T s T ↔ s < x.1 := by
  refine ⟨fun h => ?_, mem_bracket_right x⟩
  rcases h.1 with h | h
  · exact h
  · exact absurd h.1 hs.ne'

/-- Points of a bracket lie in the real closed interval. -/
lemma bracket_bounds {r s : ℝ} (hr : 0 ≤ r) (hs : s ≤ T) {x : Time T}
    (hx : x ∈ bracket T r s) : r ≤ x.1 ∧ x.1 ≤ s := by
  rcases hx with ⟨h1 | h1, h2 | h2⟩
  · exact ⟨h1.le, h2.le⟩
  · exact ⟨h1.le, by rw [h2.2, h2.1]⟩
  · exact ⟨by rw [h1.1, h1.2], h2.le⟩
  · exact ⟨by rw [h1.1, h1.2], by rw [h2.2, h2.1]⟩

/-- The complement-interior of a time interval. -/
lemma neg_bracket {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ T) :
    neg (bracket T r s) = bracket T 0 r ∪ bracket T s T := by
  ext x
  simp only [neg, interior_compl, Set.mem_compl_iff, Set.mem_union]
  constructor
  · intro hx
    by_cases h1 : x.1 < r
    · exact Or.inl (mem_bracket_left x h1)
    by_cases h2 : s < x.1
    · exact Or.inr (mem_bracket_right x h2)
    push Not at h1 h2
    exact absurd (mem_closure_bracket hr hrs hs x h1 h2) hx
  · intro hx hcl
    have hopen : IsOpen (bracket T 0 r ∪ bracket T s T) :=
      (isOpen_bracket _ _).union (isOpen_bracket _ _)
    have hdisj : Disjoint (bracket T 0 r ∪ bracket T s T) (bracket T r s) := by
      rw [Set.disjoint_left]
      intro y hy hy'
      have hb := bracket_bounds hr hs hy'
      rcases hy with hy | hy
      · rw [mem_bracket_left_iff (by linarith)] at hy
        rcases hy' with ⟨h | h, -⟩
        · linarith
        · rw [h.1] at hy; linarith [y.2.1]
      · rw [mem_bracket_right_iff (by linarith)] at hy
        rcases hy' with ⟨-, h | h⟩
        · linarith
        · rw [h.1] at hy; linarith [y.2.2]
    exact Set.disjoint_left.1 (hdisj.closure_right hopen) hx hcl

/-- Connected components of `⌊0,r⌉ ∪ ⌊s,T⌉` (with `r < s`). -/
lemma component_negbracket (hT : 0 < T) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ T)
    (t0 : Time T) (ht0 : t0 ∈ bracket T 0 r ∪ bracket T s T) :
    connectedComponentIn (bracket T 0 r ∪ bracket T s T) t0 =
      if t0.1 < r then bracket T 0 r else bracket T s T := by
  set U := bracket T 0 r ∪ bracket T s T
  have hrT : r < T := lt_of_lt_of_le hrs hs
  -- the point r separates the two pieces
  have hrU : (⟨r, hr, hrT.le⟩ : Time T) ∉ U := by
    rintro (h | h)
    · rw [mem_bracket_left_iff hrT] at h; exact lt_irrefl _ h
    · rcases h.1 with h | h
      · exact absurd h (by simp only; linarith)
      · linarith [h.1]
  have key : ∀ B : Set (Time T), B ⊆ U → IsPreconnected B → t0 ∈ B →
      ∀ C : Set (Time T), IsPreconnected C → C ⊆ U → t0 ∈ C → (∀ x ∈ C, x ∈ B) → True :=
    fun _ _ _ _ _ _ _ _ _ => trivial
  clear key
  have hC := isPreconnected_connectedComponentIn (F := U) (x := t0)
  have ht0C : t0 ∈ connectedComponentIn U t0 := mem_connectedComponentIn ht0
  have hCU : connectedComponentIn U t0 ⊆ U := connectedComponentIn_subset _ _
  split_ifs with h
  · apply Set.Subset.antisymm
    · intro x hx
      rcases hCU hx with hx' | hx'
      · exact hx'
      · exfalso
        have hsx : s < x.1 := by
          rcases hx'.1 with h' | h'
          · exact h'
          · linarith [h'.1]
        exact hrU (hCU (hC.Icc_subset ht0C hx ⟨show t0.1 ≤ r by linarith,
          show r ≤ x.1 by linarith⟩))
    · exact (isPreconnected_bracket hT.le _ _).subset_connectedComponentIn
        (mem_bracket_left t0 h) Set.subset_union_left
  · push Not at h
    have ht0s : t0 ∈ bracket T s T := by
      rcases ht0 with h' | h'
      · rw [mem_bracket_left_iff hrT] at h'; linarith
      · exact h'
    have hst0 : s < t0.1 ∨ (s = 0 ∧ t0.1 = 0) := ht0s.1
    have hst0' : s < t0.1 := by rcases hst0 with h' | h'; exact h'; linarith [h'.1]
    apply Set.Subset.antisymm
    · intro x hx
      rcases hCU hx with hx' | hx'
      · exfalso
        rw [mem_bracket_left_iff hrT] at hx'
        exact hrU (hCU (hC.Icc_subset hx ht0C ⟨show x.1 ≤ r by linarith,
          show r ≤ t0.1 by linarith⟩))
      · exact hx'
    · exact (isPreconnected_bracket hT.le _ _).subset_connectedComponentIn ht0s
        Set.subset_union_right

lemma span_empty' : IsTimeSpan (∅ : Set (Time T)) :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩

lemma span_single {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ T) :
    IsTimeSpan (bracket T r s) :=
  ⟨1, fun _ => r, fun _ => s, fun _ => ⟨hr, hrs, hs⟩, fun i j hij => absurd hij (by omega),
    by ext x; simp only [Set.mem_iUnion]; exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩⟩

lemma bracket_empty_of_le (hT : 0 < T) {r s : ℝ} (h : s ≤ r) : bracket T r s = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1 | h1, h2 | h2⟩
  · linarith
  · rw [h2.1] at h; linarith [x.2.2, h2.2]
  · rw [h1.1] at h; linarith [x.2.1, h1.2]
  · rw [h1.1, h2.1] at h; linarith

lemma span_negbracket (hT : 0 < T) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ T) :
    IsTimeSpan (bracket T 0 r ∪ bracket T s T) := by
  rcases lt_or_eq_of_le hr with hr0 | hr0
  · rcases lt_or_eq_of_le hs with hsT | hsT
    · refine ⟨2, ![0, s], ![r, T], ?_, ?_, ?_⟩
      · intro i; fin_cases i
        · exact ⟨le_refl _, hr0, by simp; linarith⟩
        · exact ⟨by simp; linarith, by simp; exact hsT, by simp⟩
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      · ext x; simp only [Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro (h | h)
          · exact ⟨0, by simpa using h⟩
          · exact ⟨1, by simpa using h⟩
        · rintro ⟨i, hi⟩
          fin_cases i
          · left; simpa using hi
          · right; simpa using hi
    · rw [hsT, bracket_empty_of_le hT (le_refl T), Set.union_empty]
      exact span_single (le_refl _) hr0 (by linarith)
  · rw [← hr0, bracket_empty_of_le hT (le_refl 0), Set.empty_union]
    rcases lt_or_eq_of_le hs with hsT | hsT
    · exact span_single (by linarith) hsT (le_refl _)
    · rw [hsT, bracket_empty_of_le hT (le_refl T)]; exact span_empty'

lemma bracket_univ (hT : 0 < T) : bracket T 0 T = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  refine ⟨?_, ?_⟩
  · rcases lt_or_eq_of_le x.2.1 with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨rfl, h'.symm⟩
  · rcases lt_or_eq_of_le x.2.2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨rfl, h'⟩

end IDUILib


open IntertempDUI.Finite

open IDUILib in
theorem solution {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : RichnessStar A pref) (hI : ISep A pref) (hL : LSepStar A pref) :
    ∀ J, IsTimeInterval J → ∀ a ∈ A, ∀ b ∈ A,
      pref J a b ↔ induced A pref J a b := by
  rintro J ⟨r, s, hr, hrs, hs, rfl⟩ a ha b hb
  have hN : neg (bracket T r s) = bracket T 0 r ∪ bracket T s T := neg_bracket hr hrs hs
  have hrT : r < T := lt_of_lt_of_le hrs hs
  have hs0 : 0 < s := lt_of_le_of_lt hr hrs
  have hJint : IsTimeInterval (bracket T r s) := ⟨r, s, hr, hrs, hs, rfl⟩
  have chain : ∀ a' ∈ A, ∀ b' ∈ A,
      (∀ I, IsComponent (neg (bracket T r s)) I → indiff pref I a' b') →
      (pref Set.univ a' b' ↔ pref (bracket T r s) a' b') := by
    intro a' ha' b' hb' hcomp
    have hH : pref (bracket T 0 s) a' b' ↔ pref (bracket T r s) a' b' := by
      rcases lt_or_eq_of_le hr with hr0 | hr0
      · have hadj : AreAdjacent (bracket T 0 r) (bracket T r s) (bracket T 0 s) :=
          ⟨0, r, s, le_refl _, hr0, hrs, hs, Or.inl ⟨rfl, rfl⟩, rfl⟩
        refine hI _ _ _ hadj a' ha' b' hb' (hcomp _ ?_)
        refine ⟨⟨0, le_refl _, hT.le⟩, ?_, ?_⟩
        · rw [hN]; exact Or.inl (mem_bracket_left _ hr0)
        · rw [hN, component_negbracket hT hr hrs hs _ (Or.inl (mem_bracket_left _ hr0)),
            if_pos hr0]
      · rw [← hr0]
    have hU : pref Set.univ a' b' ↔ pref (bracket T 0 s) a' b' := by
      rcases lt_or_eq_of_le hs with hsT | hsT
      · have hadj : AreAdjacent (bracket T s T) (bracket T 0 s) (bracket T 0 T) :=
          ⟨0, s, T, le_refl _, hs0, hsT, le_refl _, Or.inr ⟨rfl, rfl⟩, rfl⟩
        rw [← bracket_univ hT]
        refine hI _ _ _ hadj a' ha' b' hb' (hcomp _ ?_)
        refine ⟨⟨T, hT.le, le_refl _⟩, ?_, ?_⟩
        · rw [hN]; exact Or.inr (mem_bracket_right _ hsT)
        · rw [hN, component_negbracket hT hr hrs hs _ (Or.inr (mem_bracket_right _ hsT)),
            if_neg (by simp only; linarith)]
      · rw [hsT, bracket_univ hT]
    exact hU.trans hH
  obtain ⟨-, -, -, hres⟩ := hstd _ hJint
  constructor
  · intro hab
    have hspanN : IsTimeSpan (neg (bracket T r s)) := by
      rw [hN]; exact span_negbracket hT hr hrs hs
    have hdisj : Disjoint (bracket T r s) (neg (bracket T r s)) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact interior_subset hx' hx
    obtain ⟨f, hf, hfJ, hfc⟩ := hR _ _ (span_single hr hrs hs) hspanN hdisj b hb a ha
    refine ⟨a, ha, f, hf, fun _ _ => rfl, hfJ, fun I hI' => ?_, ?_⟩
    · exact ⟨(hfc I hI').2, (hfc I hI').1⟩
    · have hc : ∀ I, IsComponent (neg (bracket T r s)) I → indiff pref I a f :=
        fun I hI' => ⟨(hfc I hI').2, (hfc I hI').1⟩
      rw [chain a ha f hf hc]
      exact (hres a ha b hb a ha f hf (fun _ _ => rfl) (fun x hx => (hfJ hx).symm)).1 hab
  · rintro ⟨a', ha', b', hb', hea, heb, hc, hpu⟩
    have := (chain a' ha' b' hb' hc).1 hpu
    exact (hres a' ha' b' hb' a ha b hb hea heb).1 this
