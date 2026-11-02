-- Prove2me | solution 1 for IntertempDUI.Finite.lemma_A3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:41:14.503218+00:00
-- url     : https://prove2.me/submissions/25b86b60-2f64-4da7-adf0-d36dcea196df

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

namespace IDUILib

variable {T : ℝ}

/-- Regular open sets with finite frontier: the topological description of time spans. -/
def NiceSet (S : Set (Time T)) : Prop :=
  IsOpen S ∧ interior (closure S) = S ∧ (frontier S).Finite

lemma closure_bracket_subset {r s : ℝ} (hr : 0 ≤ r) (hs : s ≤ T) :
    closure (bracket T r s) ⊆ {x : Time T | r ≤ x.1 ∧ x.1 ≤ s} := by
  apply closure_minimal
  · intro x hx; exact bracket_bounds hr hs hx
  · exact (isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)

lemma isClosed_Cset (r s : ℝ) : IsClosed {x : Time T | r ≤ x.1 ∧ x.1 ≤ s} :=
  (isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)

lemma mem_bracket_of_lt {r s : ℝ} {x : Time T} (h1 : r < x.1) (h2 : x.1 < s) :
    x ∈ bracket T r s := ⟨Or.inl h1, Or.inl h2⟩

section forward

variable {N : ℕ} {s t : Fin N → ℝ}

lemma span_isOpen (S : Set (Time T)) (hS : IsTimeSpan S) : IsOpen S := by
  obtain ⟨N, s, t, -, -, rfl⟩ := hS
  exact isOpen_iUnion fun i => isOpen_bracket _ _

lemma closure_span_subset (hst : ∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) :
    closure (⋃ i, bracket T (s i) (t i)) ⊆ ⋃ i, {x : Time T | s i ≤ x.1 ∧ x.1 ≤ t i} := by
  rw [closure_iUnion_of_finite]
  exact Set.iUnion_mono fun i => closure_bracket_subset (hst i).1 (hst i).2.2

lemma span_frontier_finite (hst : ∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) :
    (frontier (⋃ i, bracket T (s i) (t i))).Finite := by
  have hfin : (Set.range s ∪ Set.range t).Finite :=
    (Set.finite_range s).union (Set.finite_range t)
  apply (hfin.preimage Subtype.val_injective.injOn).subset
  intro x hx
  have hopen : IsOpen (⋃ i, bracket T (s i) (t i)) := isOpen_iUnion fun i => isOpen_bracket _ _
  rw [hopen.frontier_eq] at hx
  obtain ⟨hcl, hnot⟩ := hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (closure_span_subset hst hcl)
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_range]
  by_cases h1 : s i < x.1
  · by_cases h2 : x.1 < t i
    · exact absurd (Set.mem_iUnion.2 ⟨i, mem_bracket_of_lt h1 h2⟩) hnot
    · right; exact ⟨i, le_antisymm (not_lt.1 h2) hi.2⟩
  · left; exact ⟨i, le_antisymm hi.1 (not_lt.1 h1)⟩

lemma span_regular (hT : 0 < T) (hst : ∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T)
    (hsep : ∀ i j : Fin N, i < j → t i < s j) :
    interior (closure (⋃ i, bracket T (s i) (t i))) = ⋃ i, bracket T (s i) (t i) := by
  set S := ⋃ i, bracket T (s i) (t i) with hSdef
  have hopen : IsOpen S := isOpen_iUnion fun i => isOpen_bracket _ _
  apply Set.Subset.antisymm _ (interior_maximal subset_closure hopen)
  intro x hx
  by_contra hxS
  have hcl : x ∈ closure S := interior_subset hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (closure_span_subset hst hcl)
  obtain ⟨hs0, hst', htT⟩ := hst i
  have hnot : ¬ (s i < x.1 ∧ x.1 < t i) := fun h =>
    hxS (Set.mem_iUnion.2 ⟨i, mem_bracket_of_lt h.1 h.2⟩)
  by_cases hxs : x.1 = s i
  · -- x is a left endpoint
    have hx0 : 0 < x.1 := by
      rcases lt_or_eq_of_le hs0 with h | h
      · rw [hxs]; exact h
      · exfalso; apply hxS
        refine Set.mem_iUnion.2 ⟨i, Or.inr ⟨h.symm, by rw [hxs, ← h]⟩, Or.inl (by linarith)⟩
    set Z := ⋃ j ∈ {j : Fin N | t j < x.1}, {y : Time T | s j ≤ y.1 ∧ y.1 ≤ t j} with hZ
    have hZc : IsClosed Z := by
      apply Set.Finite.isClosed_biUnion (Set.toFinite _)
      intro j _; exact isClosed_Cset _ _
    have hxZ : x ∉ Z := by
      simp only [hZ, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_and]
      intro j hj hj1 hj2; linarith
    have hW : IsOpen (interior (closure S) ∩ Zᶜ) := isOpen_interior.inter hZc.isOpen_compl
    have hxW : x ∈ interior (closure S) ∩ Zᶜ := ⟨hx, hxZ⟩
    have hxcl : x ∈ closure (bracket T 0 x.1) :=
      mem_closure_bracket (le_refl _) hx0 (by linarith) x (by linarith) (le_refl _)
    obtain ⟨y, ⟨hyU, hyZ⟩, hyB⟩ := (mem_closure_iff.1 hxcl) _ hW hxW
    have hyx : y.1 < x.1 := by
      rw [mem_bracket_left_iff (by linarith)] at hyB; exact hyB
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (closure_span_subset hst (interior_subset hyU))
    apply hyZ
    simp only [hZ, Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨j, ?_, hj⟩
    by_contra htj
    push Not at htj
    rcases lt_trichotomy j i with hji | rfl | hji
    · have := hsep j i hji; linarith
    · linarith [hj.1]
    · have := hsep i j hji; linarith [hj.1, (hst j).2.1]
  · -- x is a right endpoint
    have hxt : x.1 = t i := by
      rcases lt_or_eq_of_le hi.1 with h | h
      · by_contra h'; exact hnot ⟨h, lt_of_le_of_ne hi.2 h'⟩
      · exact absurd h.symm hxs
    have hxT : x.1 < T := by
      rcases lt_or_eq_of_le htT with h | h
      · rw [hxt]; exact h
      · exfalso; apply hxS
        exact Set.mem_iUnion.2 ⟨i, Or.inl (by linarith), Or.inr ⟨h, by rw [hxt, h]⟩⟩
    set Z := ⋃ j ∈ {j : Fin N | x.1 < s j}, {y : Time T | s j ≤ y.1 ∧ y.1 ≤ t j} with hZ
    have hZc : IsClosed Z := by
      apply Set.Finite.isClosed_biUnion (Set.toFinite _)
      intro j _; exact isClosed_Cset _ _
    have hxZ : x ∉ Z := by
      simp only [hZ, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_and]
      intro j hj hj1 hj2; linarith
    have hW : IsOpen (interior (closure S) ∩ Zᶜ) := isOpen_interior.inter hZc.isOpen_compl
    have hxW : x ∈ interior (closure S) ∩ Zᶜ := ⟨hx, hxZ⟩
    have hxcl : x ∈ closure (bracket T x.1 T) :=
      mem_closure_bracket x.2.1 hxT (le_refl _) x (le_refl _) (by linarith)
    obtain ⟨y, ⟨hyU, hyZ⟩, hyB⟩ := (mem_closure_iff.1 hxcl) _ hW hxW
    have hyx : x.1 < y.1 := by
      rw [mem_bracket_right_iff (by linarith [hst' , hs0])] at hyB; exact hyB
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (closure_span_subset hst (interior_subset hyU))
    apply hyZ
    simp only [hZ, Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨j, ?_, hj⟩
    by_contra hsj
    push Not at hsj
    rcases lt_trichotomy j i with hji | rfl | hji
    · have := hsep j i hji; linarith [hj.2, (hst j).2.1]
    · linarith [hj.2]
    · have := hsep i j hji; linarith

lemma span_nice (hT : 0 < T) (S : Set (Time T)) (hS : IsTimeSpan S) : NiceSet S := by
  obtain ⟨N, s, t, hst, hsep, rfl⟩ := hS
  exact ⟨isOpen_iUnion fun i => isOpen_bracket _ _, span_regular hT hst hsep,
    span_frontier_finite hst⟩

end forward

/-- Sorting lemma: a finite family of pairwise separated brackets forms a time span. -/
lemma span_of_family {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hab : ∀ k, 0 ≤ a k ∧ a k < b k ∧ b k ≤ T)
    (hsep : ∀ k l, k ≠ l → b k < a l ∨ b l < a k) :
    IsTimeSpan (⋃ k, bracket T (a k) (b k)) := by
  classical
  have hinj : Function.Injective a := by
    intro k l hkl
    by_contra hne
    rcases hsep k l hne with h | h
    · have := (hab k).2.1; linarith
    · have := (hab l).2.1; linarith
  set A' : Finset ℝ := Finset.univ.image a with hA'
  set N := A'.card
  set e := A'.orderEmbOfFin rfl
  have hmem : ∀ i : Fin N, ∃ k, a k = e i := by
    intro i
    have : e i ∈ A' := Finset.orderEmbOfFin_mem A' rfl i
    simpa [hA'] using this
  choose kk hkk using hmem
  refine ⟨N, fun i => a (kk i), fun i => b (kk i), fun i => hab (kk i), ?_, ?_⟩
  · intro i j hij
    have hlt : e i < e j := e.strictMono hij
    have hne : kk i ≠ kk j := by
      intro h; rw [← hkk i, ← hkk j, h] at hlt; exact lt_irrefl _ hlt
    rcases hsep (kk i) (kk j) hne with h | h
    · exact h
    · exfalso
      have := (hab (kk j)).2.1
      rw [hkk i, hkk j] at *
      linarith
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      have : a k ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]; simp [hA']
      obtain ⟨i, hi⟩ := this
      have : kk i = k := hinj (by rw [hkk i, hi])
      exact ⟨i, by rw [this]; exact hk⟩
    · rintro ⟨i, hi⟩; exact ⟨kk i, hi⟩

end IDUILib

namespace IDUILib

variable {T : ℝ}

/-- The next element of a finite set of reals after `p` (or `p` itself if none). -/
noncomputable def nxt (D : Finset ℝ) (p : ℝ) : ℝ := by
  classical
  exact if h : (D.filter (fun q => p < q)).Nonempty then (D.filter (fun q => p < q)).min' h else p

lemma nxt_spec (D : Finset ℝ) (p : ℝ) (h : ∃ q ∈ D, p < q) :
    nxt D p ∈ D ∧ p < nxt D p ∧ ∀ q ∈ D, p < q → nxt D p ≤ q := by
  classical
  have hne : (D.filter (fun q => p < q)).Nonempty := by
    obtain ⟨q, hq, hpq⟩ := h; exact ⟨q, Finset.mem_filter.2 ⟨hq, hpq⟩⟩
  have e : nxt D p = (D.filter (fun q => p < q)).min' hne := by
    unfold nxt; rw [dif_pos hne]
  have hm := Finset.min'_mem _ hne
  rw [Finset.mem_filter] at hm
  refine ⟨e ▸ hm.1, e ▸ hm.2, fun q hq hpq => ?_⟩
  rw [e]; exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hq, hpq⟩)

lemma isPreconnected_cell (hT : 0 ≤ T) {p q : ℝ} (hp : 0 ≤ p) (hq : q ≤ T) :
    IsPreconnected {x : Time T | p < x.1 ∧ x.1 < q} := by
  have : {x : Time T | p < x.1 ∧ x.1 < q} = Set.projIcc (0:ℝ) T hT '' Set.Ioo p q := by
    ext x
    constructor
    · intro hx; exact ⟨x.1, hx, Set.projIcc_val _ _⟩
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ Set.Icc (0:ℝ) T := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      simp only [Set.mem_ofPred_eq, Set.projIcc_of_mem _ hy']
      exact hy
  rw [this]
  exact isPreconnected_Ioo.image _ continuous_projIcc.continuousOn

lemma isOpen_cell (p q : ℝ) : IsOpen {x : Time T | p < x.1 ∧ x.1 < q} :=
  (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

lemma mem_closure_cell {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ T)
    (x : Time T) (hx1 : p ≤ x.1) (hx2 : x.1 ≤ q) : x ∈ closure {y : Time T | p < y.1 ∧ y.1 < q} := by
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have hsub : Set.Ioo p q ⊆ Subtype.val '' {y : Time T | p < y.1 ∧ y.1 < q} := by
    intro y hy
    exact ⟨⟨y, by linarith [hy.1], by linarith [hy.2]⟩, hy, rfl⟩
  have := closure_mono hsub
  rw [closure_Ioo hpq.ne] at this
  exact this ⟨hx1, hx2⟩

/-- A preconnected set avoiding the frontier of an open set lies inside it or outside its
closure. -/
lemma mono_of_frontier {S C : Set (Time T)} (hS : IsOpen S) (hC : IsPreconnected C)
    (hCf : ∀ x ∈ C, x ∉ frontier S) : C ⊆ S ∨ C ⊆ (closure S)ᶜ := by
  have hcov : C ⊆ S ∪ (closure S)ᶜ := by
    intro x hx
    by_cases h : x ∈ S
    · exact Or.inl h
    · right; intro hcl; exact hCf x hx ⟨hcl, by rw [hS.interior_eq]; exact h⟩
  exact hC.subset_or_subset hS isClosed_closure.isOpen_compl
    (Set.disjoint_left.2 fun x hx hx' => hx' (subset_closure hx)) hcov

/-- Conversely, a regular open subset with finite frontier is a time span. -/
lemma span_of_nice (hT : 0 < T) (S : Set (Time T)) (hS : NiceSet S) : IsTimeSpan S := by
  classical
  obtain ⟨hSo, hSr, hSf⟩ := hS
  set F' : Finset ℝ := hSf.toFinset.image Subtype.val with hF'
  set D : Finset ℝ := insert 0 (insert T F') with hD
  have hD01 : ∀ p ∈ D, 0 ≤ p ∧ p ≤ T := by
    intro p hp
    simp only [hD, hF', Finset.mem_insert, Finset.mem_image, Set.Finite.mem_toFinset] at hp
    rcases hp with rfl | rfl | ⟨y, -, rfl⟩
    · exact ⟨le_refl _, hT.le⟩
    · exact ⟨hT.le, le_refl _⟩
    · exact ⟨y.2.1, y.2.2⟩
  have h0D : (0:ℝ) ∈ D := Finset.mem_insert_self _ _
  have hTD : T ∈ D := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfrD : ∀ y ∈ frontier S, y.1 ∈ D := by
    intro y hy
    apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem
    simp only [hF', Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨y, hy, rfl⟩
  have hDfr : ∀ y : Time T, y.1 ∈ D → y.1 ≠ 0 → y.1 ≠ T → y ∈ frontier S := by
    intro y hy h0 hT'
    simp only [hD, hF', Finset.mem_insert, Finset.mem_image, Set.Finite.mem_toFinset] at hy
    rcases hy with h | h | ⟨z, hz, hzy⟩
    · exact absurd h h0
    · exact absurd h hT'
    · have : z = y := Subtype.ext hzy
      rw [← this]; exact hz
  have hnotS : ∀ y ∈ frontier S, y ∉ S := by
    intro y hy hyS
    rw [hSo.frontier_eq] at hy; exact hy.2 hyS
  -- next points
  have hnx : ∀ p ∈ D, p < T → nxt D p ∈ D ∧ p < nxt D p ∧ ∀ q ∈ D, p < q → nxt D p ≤ q :=
    fun p _ hpT => nxt_spec D p ⟨T, hTD, hpT⟩
  set Cell : ℝ → Set (Time T) := fun p => {x : Time T | p < x.1 ∧ x.1 < nxt D p} with hCell
  have hCellF : ∀ p ∈ D, p < T → ∀ x ∈ Cell p, x ∉ frontier S := by
    intro p hp hpT x hx hxf
    obtain ⟨-, -, hmin⟩ := hnx p hp hpT
    have := hmin x.1 (hfrD x hxf) hx.1
    exact absurd hx.2 (not_lt.2 this)
  have hmono : ∀ p ∈ D, p < T → Cell p ⊆ S ∨ Cell p ⊆ (closure S)ᶜ := by
    intro p hp hpT
    exact mono_of_frontier hSo (isPreconnected_cell hT.le (hD01 p hp).1
      (hD01 _ (hnx p hp hpT).1).2) (hCellF p hp hpT)
  -- a point of S in the closure of a cell forces the cell into S
  have hcellS : ∀ p ∈ D, p < T → ∀ x ∈ S, x ∈ closure (Cell p) → Cell p ⊆ S := by
    intro p hp hpT x hxS hxc
    rcases hmono p hp hpT with h | h
    · exact h
    · exfalso
      obtain ⟨y, hyS, hyC⟩ := (mem_closure_iff.1 hxc) S hSo hxS
      exact h hyC (subset_closure hyS)
  set K : Finset ℝ := D.filter (fun p => p < T ∧ Cell p ⊆ S) with hK
  have hKD : ∀ k ∈ K, k ∈ D ∧ k < T ∧ Cell k ⊆ S := by
    intro k hk; rw [hK, Finset.mem_filter] at hk; exact ⟨hk.1, hk.2.1, hk.2.2⟩
  -- the span representation
  have hrep : S = ⋃ k : K, bracket T k.1 (nxt D k.1) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hxS
      have hxnf : x ∉ frontier S := fun h => hnotS x h hxS
      by_cases hxD : x.1 ∈ D
      · by_cases hx0 : x.1 = 0
        · obtain ⟨hnD, hlt, -⟩ := hnx 0 h0D hT
          have hxc : x ∈ closure (Cell 0) :=
            mem_closure_cell (le_refl _) hlt (hD01 _ hnD).2 x (by rw [hx0]) (by rw [hx0]; exact hlt.le)
          have hC := hcellS 0 h0D hT x hxS hxc
          refine ⟨⟨0, Finset.mem_filter.2 ⟨h0D, hT, hC⟩⟩, ?_⟩
          exact ⟨Or.inr ⟨rfl, hx0⟩, Or.inl (by rw [hx0]; exact hlt)⟩
        by_cases hxT : x.1 = T
        · -- the last cell
          have hne : (D.filter (fun q => q < T)).Nonempty := ⟨0, Finset.mem_filter.2 ⟨h0D, hT⟩⟩
          set k := (D.filter (fun q => q < T)).max' hne with hk
          have hkm := Finset.max'_mem _ hne
          rw [← hk, Finset.mem_filter] at hkm
          obtain ⟨hnD, hlt, hmin⟩ := hnx k hkm.1 hkm.2
          have hnT : nxt D k = T := by
            by_contra hne'
            have h1 : nxt D k < T := lt_of_le_of_ne (hD01 _ hnD).2 hne'
            have : nxt D k ≤ k := Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hnD, h1⟩)
            linarith
          have hxc : x ∈ closure (Cell k) :=
            mem_closure_cell (hD01 k hkm.1).1 hlt (hD01 _ hnD).2 x
              (by rw [hxT]; exact hkm.2.le) (by rw [hxT, hnT])
          have hC := hcellS k hkm.1 hkm.2 x hxS hxc
          refine ⟨⟨k, Finset.mem_filter.2 ⟨hkm.1, hkm.2, hC⟩⟩, ?_⟩
          exact ⟨Or.inl (by rw [hxT]; exact hkm.2), Or.inr ⟨hnT, hxT⟩⟩
        · exact absurd (hDfr x hxD hx0 hxT) hxnf
      · -- x lies strictly inside a cell
        have hx0 : 0 < x.1 := lt_of_le_of_ne x.2.1 (fun h => hxD (h ▸ h0D))
        have hne : (D.filter (fun q => q < x.1)).Nonempty := ⟨0, Finset.mem_filter.2 ⟨h0D, hx0⟩⟩
        set k := (D.filter (fun q => q < x.1)).max' hne with hk
        have hkm := Finset.max'_mem _ hne
        rw [← hk, Finset.mem_filter] at hkm
        have hkT : k < T := lt_of_lt_of_le hkm.2 x.2.2
        obtain ⟨hnD, hlt, hmin⟩ := hnx k hkm.1 hkT
        have hxn : x.1 < nxt D k := by
          by_contra hle
          push Not at hle
          rcases lt_or_eq_of_le hle with h | h
          · have : nxt D k ≤ k := Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hnD, h⟩)
            linarith
          · exact hxD (h ▸ hnD)
        have hxC : x ∈ Cell k := ⟨hkm.2, hxn⟩
        have hC := hcellS k hkm.1 hkT x hxS (subset_closure hxC)
        exact ⟨⟨k, Finset.mem_filter.2 ⟨hkm.1, hkT, hC⟩⟩, mem_bracket_of_lt hkm.2 hxn⟩
    · rintro ⟨⟨k, hkK⟩, hx⟩
      obtain ⟨hkD, hkT, hkS⟩ := hKD k hkK
      obtain ⟨hnD, hlt, hmin⟩ := hnx k hkD hkT
      simp only at hx
      by_cases hin : k < x.1 ∧ x.1 < nxt D k
      · exact hkS hin
      · -- an endpoint 0 or T: use regularity
        rw [← hSr]
        have hb := bracket_bounds (hD01 k hkD).1 (hD01 _ hnD).2 hx
        have hcl : Set.Icc k (nxt D k) ⊆ Subtype.val '' closure S := by
          intro y hy
          have hy' : y ∈ Set.Icc (0:ℝ) T := ⟨le_trans (hD01 k hkD).1 hy.1,
            le_trans hy.2 (hD01 _ hnD).2⟩
          refine ⟨⟨y, hy'⟩, closure_mono hkS ?_, rfl⟩
          exact mem_closure_cell (hD01 k hkD).1 hlt (hD01 _ hnD).2 _ hy.1 hy.2
        rcases hx with ⟨h1 | h1, h2 | h2⟩
        · exact absurd ⟨h1, h2⟩ hin
        · -- x = T = nxt
          have W : IsOpen {y : Time T | k < y.1} := isOpen_lt continuous_const continuous_subtype_val
          refine interior_maximal ?_ W h1
          intro y hy
          obtain ⟨z, hz, hzy⟩ := hcl ⟨hy.le, by rw [h2.1]; exact y.2.2⟩
          rw [← Subtype.ext hzy]; exact hz
        · have W : IsOpen {y : Time T | y.1 < nxt D k} :=
            isOpen_lt continuous_subtype_val continuous_const
          refine interior_maximal ?_ W h2
          intro y hy
          obtain ⟨z, hz, hzy⟩ := hcl ⟨by rw [h1.1]; exact y.2.1, hy.le⟩
          rw [← Subtype.ext hzy]; exact hz
        · exfalso; linarith [h1.2, h2.2]
  rw [hrep]
  refine span_of_family (fun k : K => k.1) (fun k : K => nxt D k.1) ?_ ?_
  · intro k
    obtain ⟨hkD, hkT, -⟩ := hKD k.1 k.2
    obtain ⟨hnD, hlt, -⟩ := hnx k.1 hkD hkT
    exact ⟨(hD01 _ hkD).1, hlt, (hD01 _ hnD).2⟩
  · intro k l hkl
    have hne : k.1 ≠ l.1 := fun h => hkl (Subtype.ext h)
    -- separation of two distinct chosen cells
    have sep : ∀ k l : K, k.1 < l.1 → nxt D k.1 < l.1 := by
      intro k l hlt'
      obtain ⟨hkD, hkT, hkS⟩ := hKD k.1 k.2
      obtain ⟨hlD, hlT, hlS⟩ := hKD l.1 l.2
      obtain ⟨hnD, hlt, hmin⟩ := hnx k.1 hkD hkT
      obtain ⟨hnD', hlt'', -⟩ := hnx l.1 hlD hlT
      rcases lt_or_eq_of_le (hmin l.1 hlD hlt') with h | h
      · exact h
      · exfalso
        have hl0 : l.1 ≠ 0 := by linarith [(hD01 _ hkD).1]
        let y : Time T := ⟨l.1, (hD01 _ hlD).1, (hD01 _ hlD).2⟩
        have hyf : y ∈ frontier S := hDfr y hlD hl0 (ne_of_lt hlT)
        apply hnotS y hyf
        rw [← hSr]
        have W : IsOpen {z : Time T | k.1 < z.1 ∧ z.1 < nxt D l.1} := isOpen_cell _ _
        refine interior_maximal ?_ W ⟨hlt', hlt''⟩
        intro z hz
        rcases lt_trichotomy z.1 l.1 with h1 | h1 | h1
        · exact subset_closure (hkS ⟨hz.1, by rw [h]; exact h1⟩)
        · have : z = y := Subtype.ext h1
          rw [this]; exact hyf.1
        · exact subset_closure (hlS ⟨h1, hz.2⟩)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (sep k l h)
    · exact Or.inr (sep l k h)

lemma span_iff_nice (hT : 0 < T) (S : Set (Time T)) : IsTimeSpan S ↔ NiceSet S :=
  ⟨span_nice hT S, span_of_nice hT S⟩

end IDUILib


open IntertempDUI.Finite

namespace IDUILib

variable {T : ℝ}

lemma nice_neg {S : Set (Time T)} (hS : NiceSet S) : NiceSet (neg S) := by
  obtain ⟨hSo, -, hSf⟩ := hS
  refine ⟨isOpen_interior, ?_, ?_⟩
  · unfold neg
    have : closure Sᶜ = Sᶜ := hSo.isClosed_compl.closure_eq
    conv_lhs => rw [← this]
    rw [interior_closure_idem, this]
  · apply hSf.subset
    unfold neg
    exact (frontier_interior_subset).trans (by rw [frontier_compl])

lemma nice_join {Q R : Set (Time T)} (hQ : NiceSet Q) (hR : NiceSet R) : NiceSet (join Q R) := by
  refine ⟨isOpen_interior, ?_, ?_⟩
  · unfold join
    exact interior_closure_idem
  · apply (hQ.2.2.union hR.2.2).subset
    unfold join
    refine frontier_interior_subset.trans (frontier_closure_subset.trans ?_)
    intro x hx
    rcases frontier_union_subset Q R hx with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2

lemma nice_inter {Q R : Set (Time T)} (hQ : NiceSet Q) (hR : NiceSet R) : NiceSet (Q ∩ R) := by
  obtain ⟨hQo, hQr, hQf⟩ := hQ
  obtain ⟨hRo, hRr, hRf⟩ := hR
  refine ⟨hQo.inter hRo, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      refine ⟨?_, ?_⟩
      · rw [← hQr]; exact interior_mono (closure_mono Set.inter_subset_left) hx
      · rw [← hRr]; exact interior_mono (closure_mono Set.inter_subset_right) hx
    · exact interior_maximal subset_closure (hQo.inter hRo)
  · apply (hQf.union hRf).subset
    intro x hx
    rcases frontier_inter_subset Q R hx with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2

lemma span_neg (hT : 0 < T) {S : Set (Time T)} (hS : IsTimeSpan S) : IsTimeSpan (neg S) :=
  span_of_nice hT _ (nice_neg (span_nice hT S hS))

lemma span_join (hT : 0 < T) {Q R : Set (Time T)} (hQ : IsTimeSpan Q) (hR : IsTimeSpan R) :
    IsTimeSpan (join Q R) :=
  span_of_nice hT _ (nice_join (span_nice hT Q hQ) (span_nice hT R hR))

lemma span_inter (hT : 0 < T) {Q R : Set (Time T)} (hQ : IsTimeSpan Q) (hR : IsTimeSpan R) :
    IsTimeSpan (Q ∩ R) :=
  span_of_nice hT _ (nice_inter (span_nice hT Q hQ) (span_nice hT R hR))

lemma disjoint_neg (S : Set (Time T)) : Disjoint S (neg S) :=
  Set.disjoint_left.2 fun _ hx hx' => interior_subset hx' hx

/-- Components of a time span are time intervals. -/
lemma component_interval (hT : 0 < T) {S I : Set (Time T)} (hS : IsTimeSpan S)
    (hI : IsComponent S I) : IsTimeInterval I := by
  obtain ⟨N, s, t, hst, hsep, rfl⟩ := hS
  obtain ⟨i, rfl⟩ := component_eq hT hst hsep I hI
  exact ⟨s i, t i, (hst i).1, (hst i).2.1, (hst i).2.2, rfl⟩

lemma component_subset {S I : Set (Time T)} (hI : IsComponent S I) : I ⊆ S := by
  obtain ⟨t, -, rfl⟩ := hI
  exact connectedComponentIn_subset _ _

end IDUILib


open IntertempDUI.Finite

namespace IDUILib

variable {T : ℝ}

lemma join_neg_univ {Q : Set (Time T)} : join Q (neg Q) = Set.univ := by
  unfold join neg
  have : closure (Q ∪ interior Qᶜ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx'
    have hx : x ∈ interior (Q ∪ interior Qᶜ)ᶜ := by rw [interior_compl]; exact hx'
    have s1 : (Q ∪ interior Qᶜ)ᶜ ⊆ Qᶜ := fun y hy hyQ => hy (Or.inl hyQ)
    have s2 : (Q ∪ interior Qᶜ)ᶜ ⊆ (interior Qᶜ)ᶜ := fun y hy hyQ => hy (Or.inr hyQ)
    have h1 : x ∈ interior Qᶜ := interior_mono s1 hx
    have h2 : x ∈ (interior Qᶜ)ᶜ := interior_subset (interior_mono s2 hx)
    exact h2 h1
  rw [this, interior_univ]

lemma comp_of_inter {U V K L : Set (Time T)} (hK : IsComponent U K) (hVU : V ⊆ U)
    (hL : IsComponent (K ∩ V) L) : IsComponent V L := by
  obtain ⟨t0, ht0, rfl⟩ := hK
  obtain ⟨x, hx, rfl⟩ := hL
  refine ⟨x, hx.2, Set.Subset.antisymm ?_ ?_⟩
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) ((connectedComponentIn_subset _ _).trans Set.inter_subset_right)
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx.2)
    refine Set.subset_inter ?_ (connectedComponentIn_subset _ _)
    rw [connectedComponentIn_eq hx.1]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx.2) ((connectedComponentIn_subset _ _).trans hVU)

lemma subset_join_left {Q R : Set (Time T)} (hQ : IsOpen Q) : Q ⊆ join Q R :=
  interior_maximal (subset_closure.trans (closure_mono Set.subset_union_left)) hQ

lemma subset_join_right {Q R : Set (Time T)} (hR : IsOpen R) : R ⊆ join Q R :=
  interior_maximal (subset_closure.trans (closure_mono Set.subset_union_right)) hR

lemma neg_eq_join {Q R : Set (Time T)} (hQo : IsOpen Q) (hRo : IsOpen R)
    (hQR : Disjoint Q R) : neg Q = join (neg (join Q R)) R := by
  set S := join Q R
  have hQS : Q ⊆ S := subset_join_left hQo
  apply Set.Subset.antisymm
  · apply interior_maximal _ isOpen_interior
    intro x hx
    rw [mem_closure_iff]
    intro U hU hxU
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    set W := U ∩ neg Q
    have hWo : IsOpen W := hU.inter isOpen_interior
    have hWS : W ⊆ closure S := by
      intro y hy
      by_contra hy'
      have : y ∈ neg S := by
        unfold neg; rw [interior_compl]; exact hy'
      have : y ∈ U ∩ (neg S ∪ R) := ⟨hy.1, Or.inl this⟩
      rw [hne] at this; exact this
    have hclS : closure S ⊆ closure Q ∪ closure R := by
      rw [← closure_union]
      exact (closure_mono interior_subset).trans (by rw [closure_closure])
    have hWQ : Disjoint W (closure Q) := by
      refine Disjoint.closure_right ?_ hWo
      rw [Set.disjoint_left]
      intro y hy hyQ
      exact (interior_subset hy.2) hyQ
    have hxR : x ∈ closure R := by
      rcases hclS (hWS ⟨hxU, hx⟩) with h | h
      · exact absurd h (Set.disjoint_left.1 hWQ ⟨hxU, hx⟩)
      · exact h
    obtain ⟨y, hyW, hyR⟩ := (mem_closure_iff.1 hxR) W hWo ⟨hxU, hx⟩
    have : y ∈ U ∩ (neg S ∪ R) := ⟨hyW.1, Or.inr hyR⟩
    rw [hne] at this; exact this
  · unfold join neg
    apply interior_mono
    have hc : IsClosed Qᶜ := hQo.isClosed_compl
    refine closure_minimal ?_ hc
    rintro y (hy | hy)
    · exact fun hyQ => (interior_subset hy) (hQS hyQ)
    · exact fun hyQ => Set.disjoint_left.1 hQR hyQ hy

lemma join_inter_eq {K A B : Set (Time T)} (hKo : IsOpen K) (hKr : interior (closure K) = K)
    (hsub : K ⊆ join A B) : join (K ∩ A) (K ∩ B) = K := by
  unfold join at *
  apply Set.Subset.antisymm
  · rw [← Set.inter_union_distrib_left]
    conv_rhs => rw [← hKr]
    exact interior_mono (closure_mono Set.inter_subset_left)
  · apply interior_maximal _ hKo
    rw [← Set.inter_union_distrib_left]
    intro x hx
    exact hKo.inter_closure ⟨hx, interior_subset (hsub hx)⟩

/-- Lemma A.7 (formal version, using (ISep*)): componentwise indifference implies indifference
of the induced intermittent order. -/
lemma lemmaA7 {X : Type*} [TopologicalSpace X] (hT : 0 < T) (A : Set (Traj T X))
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : RichnessStar A pref) (hI : ISepStar A pref)
    (Q : Set (Time T)) (hQ : IsTimeSpan Q) (a : Traj T X) (ha : a ∈ A) (b : Traj T X) (hb : b ∈ A)
    (hc : ∀ I, IsComponent Q I → indiff pref I a b) : inducedIndiff A pref Q a b := by
  have hN := span_neg hT hQ
  have huniv : IsTimeInterval (Set.univ : Set (Time T)) :=
    ⟨0, T, le_refl _, hT, le_refl _, (bracket_univ hT).symm⟩
  obtain ⟨f, hf, hfQ, hfc⟩ := hR Q (neg Q) hQ hN (disjoint_neg Q) b hb a ha
  have hcomp : ∀ I, (IsComponent Q I ∨ IsComponent (neg Q) I) → indiff pref I a f := by
    rintro I (hI' | hI')
    · obtain ⟨-, -, -, hres⟩ := hstd I (component_interval hT hQ hI')
      have he : Set.EqOn f b I := fun x hx => hfQ (component_subset hI' hx)
      exact ⟨(hres a ha b hb a ha f hf (fun _ _ => rfl) (fun x hx => (he hx).symm)).1 (hc I hI').1,
        (hres b hb a ha f hf a ha (fun x hx => (he hx).symm) (fun _ _ => rfl)).1 (hc I hI').2⟩
    · exact ⟨(hfc I hI').2, (hfc I hI').1⟩
  have p1 := (hI Set.univ Q (neg Q) huniv hQ hN (disjoint_neg Q) join_neg_univ.symm a ha f hf
    (fun I hI' => (hcomp I hI').1)).1
  have p2 := (hI Set.univ Q (neg Q) huniv hQ hN (disjoint_neg Q) join_neg_univ.symm f hf a ha
    (fun I hI' => (hcomp I hI').2)).1
  exact ⟨⟨a, ha, f, hf, fun _ _ => rfl, hfQ, fun I hI' => hcomp I (Or.inr hI'), p1⟩,
    ⟨f, hf, a, ha, hfQ, fun _ _ => rfl, fun I hI' => ⟨(hcomp I (Or.inr hI')).2,
      (hcomp I (Or.inr hI')).1⟩, p2⟩⟩

end IDUILib


open IntertempDUI.Finite

namespace IDUILib

variable {T : ℝ}

lemma interior_Cset (hT : 0 < T) {r t : ℝ} (hr : 0 ≤ r) (hrt : r < t) (ht : t ≤ T) :
    interior {x : Time T | r ≤ x.1 ∧ x.1 ≤ t} = bracket T r t := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxC := interior_subset hx
    simp only [Set.mem_ofPred_eq] at hxC
    by_cases h1 : r < x.1
    · by_cases h2 : x.1 < t
      · exact mem_bracket_of_lt h1 h2
      · have hxt : x.1 = t := le_antisymm hxC.2 (not_lt.1 h2)
        suffices htT0 : t = T by exact ⟨Or.inl h1, Or.inr ⟨htT0, by rw [hxt, htT0]⟩⟩
        by_contra htT
        have htT' : t < T := lt_of_le_of_ne ht htT
        have hcl : x ∈ closure (bracket T t T) :=
          mem_closure_bracket (by linarith) htT' (le_refl _) x (by rw [hxt]) (by rw [hxt]; exact ht)
        obtain ⟨y, hy, hyB⟩ := (mem_closure_iff.1 hcl) _ isOpen_interior hx
        rw [mem_bracket_right_iff (by linarith)] at hyB
        have := (interior_subset hy : y ∈ {x : Time T | r ≤ x.1 ∧ x.1 ≤ t}).2
        linarith
    · have hxr : x.1 = r := le_antisymm (not_lt.1 h1) hxC.1
      suffices hr00 : r = 0 by exact ⟨Or.inr ⟨hr00, by rw [hxr, hr00]⟩, Or.inl (by linarith)⟩
      by_contra hr0
      have hr0' : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hcl : x ∈ closure (bracket T 0 r) :=
        mem_closure_bracket (le_refl _) hr0' (by linarith) x (by rw [hxr]; exact hr) (by rw [hxr])
      obtain ⟨y, hy, hyB⟩ := (mem_closure_iff.1 hcl) _ isOpen_interior hx
      rw [mem_bracket_left_iff (by linarith)] at hyB
      have := (interior_subset hy : y ∈ {x : Time T | r ≤ x.1 ∧ x.1 ≤ t}).1
      linarith
  · exact interior_maximal (fun x hx => bracket_bounds hr ht hx) (isOpen_bracket _ _)

lemma join_adjacent (hT : 0 < T) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t)
    (ht : t ≤ T) : join (bracket T r s) (bracket T s t) = bracket T r t := by
  unfold join
  have : closure (bracket T r s ∪ bracket T s t) = {x : Time T | r ≤ x.1 ∧ x.1 ≤ t} := by
    apply Set.Subset.antisymm
    · rw [closure_union]
      rintro x (hx | hx)
      · have := closure_bracket_subset hr (by linarith) hx
        exact ⟨this.1, by linarith [this.2]⟩
      · have := closure_bracket_subset (by linarith) ht hx
        exact ⟨by linarith [this.1], this.2⟩
    · rintro x ⟨h1, h2⟩
      by_cases hxs : x.1 ≤ s
      · exact closure_mono Set.subset_union_left
          (mem_closure_bracket hr hrs (by linarith) x h1 hxs)
      · exact closure_mono Set.subset_union_right
          (mem_closure_bracket (by linarith) hst ht x (by linarith) h2)
  rw [this, interior_Cset hT hr (by linarith) ht]

lemma comp_single (hT : 0 < T) {r s : ℝ} {K : Set (Time T)}
    (hK : IsComponent (bracket T r s) K) : K = bracket T r s := by
  obtain ⟨x, hx, rfl⟩ := hK
  exact (isPreconnected_bracket hT.le r s).connectedComponentIn hx

lemma adj_symm {I J H : Set (Time T)} (h : AreAdjacent I J H) : AreAdjacent J I H := by
  obtain ⟨r, s, t, h1, h2, h3, h4, h5 | h5, h6⟩ := h
  · exact ⟨r, s, t, h1, h2, h3, h4, Or.inr h5, h6⟩
  · exact ⟨r, s, t, h1, h2, h3, h4, Or.inl h5, h6⟩

section prefs

variable {X : Type*} [TopologicalSpace X] (A : Set (Traj T X)) (pref : Pref T X)

/-- Lemma A.2(b). -/
lemma lemmaA2b (hT : 0 < T) (hstd : Standing A pref) (hR : Richness A pref) (hI : ISep A pref)
    {I J H : Set (Time T)} (hadj : AreAdjacent I J H) {a b : Traj T X} (ha : a ∈ A) (hb : b ∈ A)
    (hIs : strict pref I a b) (hJ : pref J a b) : strict pref H a b := by
  obtain ⟨r, s, t, h0r, hrs, hst, htT, hor, hH⟩ := hadj
  have hIint : IsTimeInterval I := by
    rcases hor with h | h
    · exact ⟨r, s, h0r, hrs, by linarith, h.1⟩
    · exact ⟨s, t, by linarith, hst, htT, h.2⟩
  have hJint : IsTimeInterval J := by
    rcases hor with h | h
    · exact ⟨s, t, by linarith, hst, htT, h.2⟩
    · exact ⟨r, s, h0r, hrs, by linarith, h.1⟩
  have hHint : IsTimeInterval H := ⟨r, t, h0r, by linarith, htT, hH⟩
  -- γ = b on J and γ ≈ a on I
  obtain ⟨g, hg, hgJ, hgI⟩ : ∃ g ∈ A, Set.EqOn g b J ∧ indiff pref I g a := by
    rcases hor with ⟨hI', hJ'⟩ | ⟨hJ', hI'⟩
    · obtain ⟨f, hf, -, hfm, hfr⟩ := hR r r s t h0r (le_refl _) hrs hst.le htT a ha a ha b hb
      exact ⟨f, hf, hJ' ▸ hfr, hI' ▸ hfm⟩
    · obtain ⟨f, hf, hfl, hfm, -⟩ := hR r s t t h0r hrs.le hst (le_refl _) htT b hb a ha a ha
      exact ⟨f, hf, hJ' ▸ hfl, hI' ▸ hfm⟩
  obtain ⟨hIc, hIt, -, hIr⟩ := hstd I hIint
  obtain ⟨hJc, -, -, hJr⟩ := hstd J hJint
  obtain ⟨-, hHt, -, -⟩ := hstd H hHint
  have hbb : pref J b b := (hJc b hb b hb).elim id id
  have hJgb : indiff pref J g b :=
    ⟨(hJr b hb b hb g hg b hb (fun x hx => (hgJ hx).symm) (fun _ _ => rfl)).1 hbb,
     (hJr b hb b hb b hb g hg (fun _ _ => rfl) (fun x hx => (hgJ hx).symm)).1 hbb⟩
  have hIgb : strict pref I g b :=
    ⟨hIt g hg a ha b hb hgI.1 hIs.1, fun h => hIs.2 (hIt b hb g hg a ha h hgI.1)⟩
  have hHgb : strict pref H g b :=
    ⟨((hI J I H (adj_symm ⟨r, s, t, h0r, hrs, hst, htT, hor, hH⟩) g hg b hb hJgb).2 hIgb.1),
     fun h => hIgb.2 ((hI J I H (adj_symm ⟨r, s, t, h0r, hrs, hst, htT, hor, hH⟩) b hb g hg
       ⟨hJgb.2, hJgb.1⟩).1 h)⟩
  have hJag : pref J a g :=
    (hJr a ha b hb a ha g hg (fun _ _ => rfl) (fun x hx => (hgJ hx).symm)).1 hJ
  have hHag : pref H a g :=
    (hI I J H ⟨r, s, t, h0r, hrs, hst, htT, hor, hH⟩ a ha g hg ⟨hgI.2, hgI.1⟩).2 hJag
  exact ⟨hHt a ha g hg b hb hHag hHgb.1, fun h => hHgb.2 (hHt b hb a ha g hg h hHag)⟩

/-- Lemma A.2(a). -/
lemma lemmaA2a (hT : 0 < T) (hstd : Standing A pref) (hR : Richness A pref) (hI : ISep A pref)
    {I J H : Set (Time T)} (hadj : AreAdjacent I J H) {a b : Traj T X} (ha : a ∈ A) (hb : b ∈ A)
    (hIp : pref I a b) (hJ : pref J a b) : pref H a b := by
  by_cases h : pref I b a
  · exact (hI I J H hadj a ha b hb ⟨hIp, h⟩).2 hJ
  · exact (lemmaA2b A pref hT hstd hR hI hadj ha hb ⟨hIp, h⟩ hJ).1

end prefs

end IDUILib


open IntertempDUI.Finite

namespace IDUILib

variable {T : ℝ}

section prefs

variable {X : Type*} [TopologicalSpace X] (A : Set (Traj T X)) (pref : Pref T X)

/-- Lemma A.3, "(ISep) ⟹ (ISep*)" on a finite horizon, under (R). -/
lemma isepstar_of_isep (hT : 0 < T) (hstd : Standing A pref) (hR : Richness A pref)
    (hI : ISep A pref) : ISepStar A pref := by
  classical
  intro H Q R hH hQ hRs hQR hHj a ha b hb hcomp
  obtain ⟨h0, h1, hh0, hh01, hh1, rfl⟩ := hH
  have hQn := span_nice hT Q hQ
  have hRn := span_nice hT R hRs
  have Ffin : (frontier Q ∪ frontier R).Finite := hQn.2.2.union hRn.2.2
  set D : Finset ℝ := (insert h0 (insert h1 (Ffin.toFinset.image Subtype.val))).filter
    (fun x => h0 ≤ x ∧ x ≤ h1) with hDdef
  have hD : ∀ p ∈ D, h0 ≤ p ∧ p ≤ h1 := fun p hp => (Finset.mem_filter.1 hp).2
  have h0D : h0 ∈ D := Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, le_refl _, hh01.le⟩
  have h1D : h1 ∈ D := Finset.mem_filter.2
    ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hh01.le, le_refl _⟩
  have hFD : ∀ z ∈ frontier Q ∪ frontier R, h0 ≤ z.1 → z.1 ≤ h1 → z.1 ∈ D := by
    intro z hz h1' h2'
    refine Finset.mem_filter.2 ⟨?_, h1', h2'⟩
    apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem
    exact Finset.mem_image.2 ⟨z, Ffin.mem_toFinset.2 hz, rfl⟩
  have hHQ : Q ⊆ bracket T h0 h1 := hHj ▸ subset_join_left hQn.1
  have hHR : R ⊆ bracket T h0 h1 := hHj ▸ subset_join_right hRn.1
  have hHcl : bracket T h0 h1 ⊆ closure (Q ∪ R) := by
    rw [hHj]; exact interior_subset
  -- points of D lying in Q ∪ R are 0 or T
  have hDQR : ∀ y : Time T, y.1 ∈ D → y ∈ Q ∪ R → y.1 = 0 ∨ y.1 = T := by
    intro y hyD hyQR
    have hyH : y ∈ bracket T h0 h1 := hyQR.elim (fun h => hHQ h) (fun h => hHR h)
    obtain ⟨hmem, -⟩ := Finset.mem_filter.1 hyD
    rcases Finset.mem_insert.1 hmem with h | h
    · rcases hyH.1 with h' | h'
      · linarith
      · exact Or.inl h'.2
    rcases Finset.mem_insert.1 h with h | h
    · rcases hyH.2 with h' | h'
      · linarith
      · exact Or.inr h'.2
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.1 h
    have hzy' : z = y := Subtype.ext hzy
    rw [Ffin.mem_toFinset, hzy'] at hz
    exfalso
    rcases hz with hz | hz
    · rcases hyQR with h' | h'
      · rw [hQn.1.frontier_eq] at hz; exact hz.2 h'
      · obtain ⟨w, hwR, hwQ⟩ := (mem_closure_iff.1 hz.1) R hRn.1 h'
        exact Set.disjoint_left.1 hQR hwQ hwR
    · rcases hyQR with h' | h'
      · obtain ⟨w, hwQ, hwR⟩ := (mem_closure_iff.1 hz.1) Q hQn.1 h'
        exact Set.disjoint_left.1 hQR hwQ hwR
      · rw [hRn.1.frontier_eq] at hz; exact hz.2 h'
  have hnx : ∀ p ∈ D, p < h1 → nxt D p ∈ D ∧ p < nxt D p ∧ ∀ q ∈ D, p < q → nxt D p ≤ q :=
    fun p _ hp1 => nxt_spec D p ⟨h1, h1D, hp1⟩
  -- each cell is a component of Q or of R
  have hcell : ∀ p ∈ D, p < h1 →
      IsComponent Q (bracket T p (nxt D p)) ∨ IsComponent R (bracket T p (nxt D p)) := by
    intro p hp hp1
    obtain ⟨hqD, hpq, hmin⟩ := hnx p hp hp1
    set q := nxt D p with hq
    have hp0 : 0 ≤ p := le_trans hh0 (hD p hp).1
    have hqT : q ≤ T := le_trans (hD q hqD).2 hh1
    set C : Set (Time T) := {x : Time T | p < x.1 ∧ x.1 < q} with hC
    have hCH : ∀ x ∈ C, h0 < x.1 ∧ x.1 < h1 := fun x hx =>
      ⟨lt_of_le_of_lt (hD p hp).1 hx.1, lt_of_lt_of_le hx.2 (hD q hqD).2⟩
    have hCf : ∀ x ∈ C, x ∉ frontier Q ∪ frontier R := by
      intro x hx hxf
      have := hmin x.1 (hFD x hxf (hCH x hx).1.le (hCH x hx).2.le) hx.1
      linarith [hx.2]
    have hCpc : IsPreconnected C := isPreconnected_cell hT.le hp0 hqT
    have mQ := mono_of_frontier hQn.1 hCpc (fun x hx h => hCf x hx (Or.inl h))
    have mR := mono_of_frontier hRn.1 hCpc (fun x hx h => hCf x hx (Or.inr h))
    let m : Time T := ⟨(p + q) / 2, by linarith, by linarith⟩
    have hmC : m ∈ C := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
    have gen : ∀ V : Set (Time T), NiceSet V → V ⊆ Q ∪ R → C ⊆ V →
        IsComponent V (bracket T p q) := by
      intro V hV hVQR hCV
      have hBV : bracket T p q ⊆ V := by
        rw [← hV.2.1]
        refine interior_maximal ?_ (isOpen_bracket _ _)
        intro x hx
        have hb := bracket_bounds hp0 hqT hx
        exact closure_mono hCV (mem_closure_cell hp0 hpq hqT x hb.1 hb.2)
      have hmB : m ∈ bracket T p q := mem_bracket_of_lt hmC.1 hmC.2
      refine ⟨m, hBV hmB, Set.Subset.antisymm ?_ ?_⟩
      · exact (isPreconnected_bracket hT.le _ _).subset_connectedComponentIn hmB hBV
      · intro y hy
        have hCC := isPreconnected_connectedComponentIn (F := V) (x := m)
        have hmCC : m ∈ connectedComponentIn V m := mem_connectedComponentIn (hBV hmB)
        have hsub : connectedComponentIn V m ⊆ V := connectedComponentIn_subset _ _
        have hP : ∀ z : Time T, z ∈ connectedComponentIn V m → z.1 ∈ D →
            z.1 = 0 ∨ z.1 = T := fun z hz hzD => hDQR z hzD (hVQR (hsub hz))
        have hyp : p ≤ y.1 := by
          by_contra hlt
          push Not at hlt
          let P : Time T := ⟨p, hp0, by linarith⟩
          have hPC : P ∈ connectedComponentIn V m :=
            hCC.Icc_subset hy hmCC ⟨show y.1 ≤ p by linarith, show p ≤ m.1 by
              simp only [m]; linarith⟩
          rcases hP P hPC hp with h | h
          · simp only [P] at h; linarith [y.2.1]
          · simp only [P] at h; linarith
        have hyq : y.1 ≤ q := by
          by_contra hlt
          push Not at hlt
          let P : Time T := ⟨q, by linarith, hqT⟩
          have hPC : P ∈ connectedComponentIn V m :=
            hCC.Icc_subset hmCC hy ⟨show m.1 ≤ q by simp only [m]; linarith,
              show q ≤ y.1 by linarith⟩
          rcases hP P hPC hqD with h | h
          · simp only [P] at h; linarith
          · simp only [P] at h; linarith [y.2.2]
        rcases lt_or_eq_of_le hyp with h1' | h1'
        · rcases lt_or_eq_of_le hyq with h2' | h2'
          · exact mem_bracket_of_lt h1' h2'
          · rcases hP y hy (h2' ▸ hqD) with h | h
            · linarith
            · exact ⟨Or.inl h1', Or.inr ⟨by rw [← h2', h], h⟩⟩
        · rcases hP y hy (h1' ▸ hp) with h | h
          · exact ⟨Or.inr ⟨by rw [h1', h], h⟩, Or.inl (by linarith)⟩
          · linarith
    rcases mQ with hCQ | hCQ
    · exact Or.inl (gen Q hQn (fun x hx => Or.inl hx) hCQ)
    rcases mR with hCR | hCR
    · exact Or.inr (gen R hRn (fun x hx => Or.inr hx) hCR)
    exfalso
    have hmH : m ∈ bracket T h0 h1 := mem_bracket_of_lt (hCH m hmC).1 (hCH m hmC).2
    obtain ⟨w, hwC, hwQR⟩ := (mem_closure_iff.1 (hHcl hmH)) C (isOpen_cell _ _) hmC
    rcases hwQR with h | h
    · exact hCQ hwC (subset_closure h)
    · exact hCR hwC (subset_closure h)
  have hcellpref : ∀ p ∈ D, p < h1 → pref (bracket T p (nxt D p)) a b := by
    intro p hp hp1
    rcases hcell p hp hp1 with h | h
    · exact hcomp _ (Or.inl h)
    · exact hcomp _ (Or.inr h)
  -- the sweep
  have G : ∀ n, ∀ x ∈ D, h0 < x → (D.filter (fun y => y < x)).card = n →
      pref (bracket T h0 x) a b ∧
      ((∃ p ∈ D, p < h1 ∧ nxt D p ≤ x ∧ strict pref (bracket T p (nxt D p)) a b) →
        strict pref (bracket T h0 x) a b) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro x hxD hx0 hcard
    have hne : (D.filter (fun y => y < x)).Nonempty := ⟨h0, Finset.mem_filter.2 ⟨h0D, hx0⟩⟩
    set p := (D.filter (fun y => y < x)).max' hne with hpdef
    have hpm := Finset.max'_mem _ hne
    rw [← hpdef, Finset.mem_filter] at hpm
    obtain ⟨hpD, hpx⟩ := hpm
    have hp1 : p < h1 := lt_of_lt_of_le hpx (hD x hxD).2
    obtain ⟨hqD, hpq, hmin⟩ := hnx p hpD hp1
    have hqx : nxt D p = x := by
      apply le_antisymm (hmin x hxD hpx)
      by_contra hlt
      push Not at hlt
      have : nxt D p ≤ p := Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hqD, hlt⟩)
      linarith
    have hcp := hcellpref p hpD hp1
    rw [hqx] at hcp
    have hxT : x ≤ T := le_trans (hD x hxD).2 hh1
    rcases lt_or_eq_of_le (hD p hpD).1 with hp0 | hp0
    · -- p > h0: use the induction hypothesis at p
      have hlt : (D.filter (fun y => y < p)).card < n := by
        rw [← hcard]
        apply Finset.card_lt_card
        refine ⟨fun y hy => ?_, fun hsub => ?_⟩
        · rw [Finset.mem_filter] at hy ⊢; exact ⟨hy.1, lt_trans hy.2 hpx⟩
        · have := hsub (Finset.mem_filter.2 ⟨hpD, hpx⟩)
          rw [Finset.mem_filter] at this; exact lt_irrefl _ this.2
      obtain ⟨ihp, ihs⟩ := ih _ hlt p hpD hp0 rfl
      have hadj : AreAdjacent (bracket T h0 p) (bracket T p x) (bracket T h0 x) :=
        ⟨h0, p, x, hh0, hp0, hpx, hxT, Or.inl ⟨rfl, rfl⟩, rfl⟩
      refine ⟨lemmaA2a A pref hT hstd hR hI hadj ha hb ihp hcp, ?_⟩
      rintro ⟨p', hp'D, hp'1, hp'x, hstr⟩
      obtain ⟨hq'D, hpq', hmin'⟩ := hnx p' hp'D hp'1
      by_cases hle : nxt D p' ≤ p
      · exact lemmaA2b A pref hT hstd hR hI hadj ha hb (ihs ⟨p', hp'D, hp'1, hle, hstr⟩) hcp
      · push Not at hle
        have hp'p : p' ≤ p := Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hp'D, by linarith⟩)
        have hpp' : p' = p := by
          rcases lt_or_eq_of_le hp'p with h | h
          · have := hmin' p hpD h; linarith
          · exact h
        rw [hpp', hqx] at hstr
        exact lemmaA2b A pref hT hstd hR hI (adj_symm hadj) ha hb hstr ihp
    · -- p = h0: the bracket is itself a cell
      rw [hp0]
      refine ⟨hcp, ?_⟩
      rintro ⟨p', hp'D, hp'1, hp'x, hstr⟩
      obtain ⟨hq'D, hpq', hmin'⟩ := hnx p' hp'D hp'1
      have hp'p : p' ≤ p := Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hp'D, by linarith⟩)
      have : p' = p := le_antisymm hp'p (hp0 ▸ (hD p' hp'D).1)
      rw [this, hqx] at hstr
      exact hstr
  obtain ⟨Gp, Gs⟩ := G _ h1 h1D hh01 rfl
  refine ⟨Gp, ?_⟩
  rintro ⟨I, hIc, hIs⟩
  apply Gs
  -- the strict component is one of the cells
  have hIspan : ∃ V, (V = Q ∨ V = R) ∧ IsComponent V I := by
    rcases hIc with h | h
    · exact ⟨Q, Or.inl rfl, h⟩
    · exact ⟨R, Or.inr rfl, h⟩
  obtain ⟨V, hV, hVI⟩ := hIspan
  have hVspan : IsTimeSpan V := by rcases hV with rfl | rfl; exact hQ; exact hRs
  obtain ⟨s, t, hs0, hst, htT, hIeq⟩ := component_interval hT hVspan hVI
  obtain ⟨y0, hy0, hy0D⟩ : ∃ y ∈ Set.Ioo s t, y ∉ (D : Set ℝ) :=
    ((Set.Ioo_infinite hst).diff D.finite_toSet).nonempty
  let y : Time T := ⟨y0, by linarith [hy0.1], by linarith [hy0.2]⟩
  have hyI : y ∈ I := by rw [hIeq]; exact mem_bracket_of_lt hy0.1 hy0.2
  have hyV : y ∈ V := component_subset hVI hyI
  have hyH : y ∈ bracket T h0 h1 := by rcases hV with rfl | rfl; exact hHQ hyV; exact hHR hyV
  have hyb := bracket_bounds hh0 hh1 hyH
  have hy0' : h0 < y0 := lt_of_le_of_ne hyb.1 (fun h => hy0D (by rw [← h]; exact h0D))
  have hne : (D.filter (fun z => z < y0)).Nonempty := ⟨h0, Finset.mem_filter.2 ⟨h0D, hy0'⟩⟩
  set p := (D.filter (fun z => z < y0)).max' hne with hpdef
  have hpm := Finset.max'_mem _ hne
  rw [← hpdef, Finset.mem_filter] at hpm
  obtain ⟨hpD, hpy⟩ := hpm
  have hy1 : y0 < h1 := lt_of_le_of_ne hyb.2 (fun h => hy0D (by rw [h]; exact h1D))
  have hp1 : p < h1 := by linarith
  obtain ⟨hqD, hpq, hmin⟩ := hnx p hpD hp1
  have hyq : y0 < nxt D p := by
    by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hle with h | h
    · have : nxt D p ≤ p := Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hqD, h⟩)
      linarith
    · exact hy0D (h ▸ hqD)
  have hyB : y ∈ bracket T p (nxt D p) := mem_bracket_of_lt hpy hyq
  refine ⟨p, hpD, hp1, (hD _ hqD).2, ?_⟩
  -- the cell containing y is the component I
  have hIeq' : I = connectedComponentIn V y := by
    obtain ⟨t0, -, rfl⟩ := hVI
    exact connectedComponentIn_eq hyI
  have hcellI : bracket T p (nxt D p) = I := by
    rcases hcell p hpD hp1 with h | h
    · rcases hV with rfl | rfl
      · obtain ⟨t1, -, ht1⟩ := h
        rw [hIeq', ht1, connectedComponentIn_eq (ht1 ▸ hyB)]
      · exfalso
        exact Set.disjoint_left.1 hQR (component_subset h hyB) hyV
    · rcases hV with rfl | rfl
      · exfalso
        exact Set.disjoint_left.1 hQR hyV (component_subset h hyB)
      · obtain ⟨t1, -, ht1⟩ := h
        rw [hIeq', ht1, connectedComponentIn_eq (ht1 ▸ hyB)]
  rw [hcellI]; exact hIs

end prefs

end IDUILib


open IntertempDUI.Finite

namespace IDUIA3

open IDUILib

variable {T : ℝ}

lemma disjoint_adj {r s t : ℝ} (h0r : 0 ≤ r) (hrs : r < s) (hst : s < t) (htT : t ≤ T) :
    Disjoint (bracket T r s) (bracket T s t) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, h1 | h1⟩ ⟨h2 | h2, -⟩
  · linarith
  · linarith [h2.1]
  · linarith [h1.1]
  · linarith [h2.1]

lemma adj_facts (hT : 0 < T) {I J H : Set (Time T)} (hadj : AreAdjacent I J H) :
    IsTimeInterval H ∧ IsTimeSpan I ∧ IsTimeSpan J ∧ Disjoint I J ∧ H = join I J ∧
      IsTimeInterval J ∧ (∀ K, IsComponent I K → K = I) ∧ (∀ K, IsComponent J K → K = J) := by
  obtain ⟨r, s, t, h0r, hrs, hst, htT, hor, rfl⟩ := hadj
  refine ⟨⟨r, t, h0r, by linarith, htT, rfl⟩, ?_⟩
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨span_single h0r hrs (by linarith), span_single (by linarith) hst htT,
      disjoint_adj h0r hrs hst htT, (join_adjacent hT h0r hrs hst htT).symm,
      ⟨s, t, by linarith, hst, htT, rfl⟩, fun K hK => comp_single hT hK,
      fun K hK => comp_single hT hK⟩
  · refine ⟨span_single (by linarith) hst htT, span_single h0r hrs (by linarith),
      (disjoint_adj h0r hrs hst htT).symm, ?_,
      ⟨r, s, h0r, hrs, by linarith, rfl⟩, fun K hK => comp_single hT hK,
      fun K hK => comp_single hT hK⟩
    rw [← join_adjacent hT h0r hrs hst htT]
    unfold join; rw [Set.union_comm]

lemma comp_self (hT : 0 < T) {J : Set (Time T)} (hJ : IsTimeInterval J) : IsComponent J J := by
  obtain ⟨r, s, hr, hrs, hs, rfl⟩ := hJ
  let m : Time T := ⟨(r + s) / 2, by linarith, by linarith⟩
  have hm : m ∈ bracket T r s := mem_bracket_of_lt (by simp only [m]; linarith)
    (by simp only [m]; linarith)
  exact ⟨m, hm, ((isPreconnected_bracket hT.le r s).connectedComponentIn hm).symm⟩

lemma isep_of_isepstar {X : Type*} [TopologicalSpace X] (hT : 0 < T) (A : Set (Traj T X))
    (pref : Pref T X) (hstd : Standing A pref) (hIs : ISepStar A pref) : ISep A pref := by
  intro I J H hadj a ha b hb hind
  obtain ⟨hH, hIsp, hJsp, hdis, hjoin, hJint, hcI, hcJ⟩ := adj_facts hT hadj
  obtain ⟨hcpl, -, -, -⟩ := hstd J hJint
  constructor
  · intro hab
    by_contra hJ
    have hba : pref J b a := (hcpl a ha b hb).resolve_left hJ
    have := (hIs H I J hH hIsp hJsp hdis hjoin b hb a ha (by
      rintro K (hK | hK)
      · rw [hcI K hK]; exact hind.2
      · rw [hcJ K hK]; exact hba)).2 ⟨J, Or.inr (comp_self hT hJint), ⟨hba, hJ⟩⟩
    exact this.2 hab
  · intro hJ
    exact (hIs H I J hH hIsp hJsp hdis hjoin a ha b hb (by
      rintro K (hK | hK)
      · rw [hcI K hK]; exact hind.1
      · rw [hcJ K hK]; exact hJ)).1

end IDUIA3

open IDUILib IDUIA3 in
theorem solution {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref) :
    (ISepStar A pref → ISep A pref) ∧
    (Richness A pref → (ISep A pref ↔ ISepStar A pref)) :=
  ⟨isep_of_isepstar hT A pref hstd, fun hR =>
    ⟨isepstar_of_isep A pref hT hstd hR, isep_of_isepstar hT A pref hstd⟩⟩
