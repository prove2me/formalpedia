-- Prove2me | solution 1 for IntertempDUI.Finite.lemma_B2_content_to_dui
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:53:30.633655+00:00
-- url     : https://prove2.me/submissions/2e0a1fda-af14-49cf-bf74-e6f21c6bb48c

import Mathlib
import Definitions.Def_IntertempDUI_Finite_DUI
import Definitions.Def_IntertempDUI_Finite_Content
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


open IntertempDUI.Finite MeasureTheory

namespace IDUILib

variable {T : ℝ}

lemma measurableSet_image_open {S : Set (Time T)} (hS : IsOpen S) :
    MeasurableSet (Subtype.val '' S) := by
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hS
  rw [Subtype.image_preimage_coe]
  exact measurableSet_Icc.inter hU.measurableSet

/-- The difference between `join Q R` and `Q ∪ R` is contained in the boundaries. -/
lemma join_diff_subset {Q R : Set (Time T)} (hQ : IsOpen Q) (hR : IsOpen R) :
    join Q R \ (Q ∪ R) ⊆ frontier Q ∪ frontier R := by
  rintro x ⟨hx, hx'⟩
  have hcl : x ∈ closure Q ∪ closure R := by
    rw [← closure_union]; exact interior_subset hx
  rcases hcl with h | h
  · left; rw [hQ.frontier_eq]; exact ⟨h, fun h' => hx' (Or.inl h')⟩
  · right; rw [hR.frontier_eq]; exact ⟨h, fun h' => hx' (Or.inr h')⟩

section measure

variable (ρ : StieltjesFunction ℝ) (hc : Continuous (ρ : ℝ → ℝ))
include hc

lemma leftLim_eq_of_cont (x : ℝ) : Function.leftLim (ρ : ℝ → ℝ) x = ρ x :=
  (ρ.mono.continuousWithinAt_Iio_iff_leftLim_eq).1 (hc.continuousAt.continuousWithinAt)

lemma nu_singleton (x : ℝ) : ρ.measure {x} = 0 := by
  rw [StieltjesFunction.measure_singleton, leftLim_eq_of_cont ρ hc, sub_self, ENNReal.ofReal_zero]

lemma nu_finite {Z : Set ℝ} (hZ : Z.Finite) : ρ.measure Z = 0 := by
  rw [← Set.biUnion_of_singleton Z]
  exact (measure_biUnion_null_iff hZ.countable).2 (fun x _ => nu_singleton ρ hc x)

lemma nu_Ioo (a b : ℝ) : ρ.measure (Set.Ioo a b) = ENNReal.ofReal (ρ b - ρ a) := by
  rw [StieltjesFunction.measure_Ioo, leftLim_eq_of_cont ρ hc]

lemma nu_Icc (a b : ℝ) : ρ.measure (Set.Icc a b) = ENNReal.ofReal (ρ b - ρ a) := by
  rw [StieltjesFunction.measure_Icc, leftLim_eq_of_cont ρ hc]

lemma nu_image_bracket {r s : ℝ} (hr : 0 ≤ r) (hs : s ≤ T) :
    ρ.measure (Subtype.val '' bracket T r s) = ENNReal.ofReal (ρ s - ρ r) := by
  apply le_antisymm
  · rw [← nu_Icc ρ hc]
    apply measure_mono
    rintro _ ⟨x, hx, rfl⟩
    exact bracket_bounds hr hs hx
  · rw [← nu_Ioo ρ hc]
    apply measure_mono
    intro y hy
    by_cases hrs : r < s
    · exact ⟨⟨y, by linarith [hy.1], by linarith [hy.2]⟩, mem_bracket_of_lt hy.1 hy.2, rfl⟩
    · exfalso; linarith [hy.1, hy.2]

lemma nu_image_le_one (h0 : ρ 0 = 0) (h1 : ρ T = 1) (S : Set (Time T)) :
    ρ.measure (Subtype.val '' S) ≤ 1 := by
  calc ρ.measure (Subtype.val '' S) ≤ ρ.measure (Set.Icc 0 T) := by
        apply measure_mono; rintro _ ⟨x, -, rfl⟩; exact x.2
    _ = 1 := by rw [nu_Icc ρ hc, h0, h1]; simp

lemma nu_image_ne_top (h0 : ρ 0 = 0) (h1 : ρ T = 1) (S : Set (Time T)) :
    ρ.measure (Subtype.val '' S) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (nu_image_le_one ρ hc h0 h1 S)

lemma nu_join (hT : 0 < T) {Q R : Set (Time T)} (hQ : IsTimeSpan Q) (hR : IsTimeSpan R)
    (hQR : Disjoint Q R) :
    ρ.measure (Subtype.val '' join Q R) =
      ρ.measure (Subtype.val '' Q) + ρ.measure (Subtype.val '' R) := by
  have hQn := span_nice hT Q hQ
  have hRn := span_nice hT R hR
  have hdisj : Disjoint (Subtype.val '' Q) (Subtype.val '' R) := by
    rw [Set.disjoint_image_iff Subtype.val_injective]; exact hQR
  have hunion : ρ.measure (Subtype.val '' Q ∪ Subtype.val '' R) =
      ρ.measure (Subtype.val '' Q) + ρ.measure (Subtype.val '' R) :=
    measure_union hdisj (measurableSet_image_open hRn.1)
  rw [← hunion]
  apply le_antisymm
  · have hZ : (Subtype.val '' (frontier Q ∪ frontier R)).Finite :=
      (hQn.2.2.union hRn.2.2).image _
    calc ρ.measure (Subtype.val '' join Q R)
        ≤ ρ.measure ((Subtype.val '' Q ∪ Subtype.val '' R) ∪
            Subtype.val '' (frontier Q ∪ frontier R)) := by
          apply measure_mono
          rintro _ ⟨x, hx, rfl⟩
          by_cases h : x ∈ Q ∪ R
          · rcases h with h | h
            · exact Or.inl (Or.inl ⟨x, h, rfl⟩)
            · exact Or.inl (Or.inr ⟨x, h, rfl⟩)
          · exact Or.inr ⟨x, join_diff_subset hQn.1 hRn.1 ⟨hx, h⟩, rfl⟩
      _ ≤ ρ.measure (Subtype.val '' Q ∪ Subtype.val '' R) +
            ρ.measure (Subtype.val '' (frontier Q ∪ frontier R)) := measure_union_le _ _
      _ = ρ.measure (Subtype.val '' Q ∪ Subtype.val '' R) := by
          rw [nu_finite ρ hc hZ, add_zero]
  · apply measure_mono
    rw [← Set.image_union]
    apply Set.image_mono
    rintro x (h | h)
    · exact subset_join_left hQn.1 h
    · exact subset_join_right hRn.1 h

end measure

end IDUILib


open IntertempDUI.Finite MeasureTheory

namespace IDUILib

variable {T : ℝ}

/-- The content induced by a Stieltjes function. -/
noncomputable def muRho (ρ : StieltjesFunction ℝ) : Set (Time T) → ℝ :=
  fun S => (ρ.measure (Subtype.val '' S)).toReal

section integ

variable (ρ : StieltjesFunction ℝ) (hc : Continuous (ρ : ℝ → ℝ))
include hc

lemma part_integral (hT : 0 < T) {S : Set (Time T)} {N : ℕ} {P : Fin N → Set (Time T)}
    (hP : IsPartition S P) {H : ℝ → ℝ} (hH : IntegrableOn H (Set.Icc 0 T) ρ.measure) :
    ∑ i, ∫ x in Subtype.val '' P i, H x ∂ρ.measure = ∫ x in Subtype.val '' S, H x ∂ρ.measure := by
  obtain ⟨hPs, hPd, hPS⟩ := hP
  have hPn : ∀ i, NiceSet (P i) := fun i => span_nice hT _ (hPs i)
  have hsubIcc : ∀ A : Set (Time T), Subtype.val '' A ⊆ Set.Icc 0 T := by
    rintro A _ ⟨x, -, rfl⟩; exact x.2
  rw [← integral_iUnion_fintype (fun i => measurableSet_image_open (hPn i).1)
    (fun i j hij => by
      simp only [Function.onFun]
      rw [Set.disjoint_image_iff Subtype.val_injective]; exact hPd i j hij)
    (fun i => hH.mono_set (hsubIcc _))]
  apply setIntegral_congr_set
  apply Filter.EventuallyLE.antisymm
  · apply HasSubset.Subset.eventuallyLE
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    obtain ⟨x, hx, rfl⟩ := hi
    refine ⟨x, ?_, rfl⟩
    rw [hPS]
    exact interior_maximal (subset_closure.trans (closure_mono (Set.subset_iUnion P i)))
      (hPn i).1 hx
  · rw [ae_le_set]
    apply measure_mono_null (t := Subtype.val '' ⋃ i, frontier (P i))
    · rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
      refine ⟨x, ?_, rfl⟩
      have hxcl : x ∈ closure (⋃ i, P i) := by rw [hPS] at hx; exact interior_subset hx
      rw [closure_iUnion_of_finite] at hxcl
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxcl
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      rw [(hPn i).1.frontier_eq]
      refine ⟨hi, fun hxP => hy ?_⟩
      exact Set.mem_iUnion.2 ⟨i, x, hxP, rfl⟩
    · exact nu_finite ρ hc ((Set.finite_iUnion fun i => (hPn i).2.2).image _)


omit hc in
lemma bracket_disjoint_of_le {a1 b1 a2 b2 : ℝ} (ha1 : 0 ≤ a1) (h1 : a1 < b1) (h12 : b1 ≤ a2)
    (h2 : a2 < b2) (hb2 : b2 ≤ T) : Disjoint (bracket T a1 b1) (bracket T a2 b2) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hx1 | hx1⟩ ⟨hx2 | hx2, -⟩
  · linarith
  · linarith [hx2.1]
  · linarith [hx1.1]
  · linarith [hx1.1]

omit hc in
lemma piece_sub {s t a b : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hbt : b ≤ t) (ht : t ≤ T) (hab : a < b) :
    bracket T a b ⊆ bracket T s t := by
  rintro x ⟨hx1 | hx1, hx2 | hx2⟩
  · exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩
  · exact ⟨Or.inl (by linarith), Or.inr ⟨by linarith [hx2.1], hx2.2⟩⟩
  · exact ⟨Or.inr ⟨by linarith [hx1.1], hx1.2⟩, Or.inl (by linarith)⟩
  · exact ⟨Or.inr ⟨by linarith [hx1.1], hx1.2⟩, Or.inr ⟨by linarith [hx2.1], hx2.2⟩⟩

/-- Lower sums never exceed the Lebesgue–Stieltjes integral. -/
lemma lowersum_le (hT : 0 < T) {S : Set (Time T)} (g : Time T → ℝ) (hg : Continuous g)
    {N : ℕ} {P : Fin N → Set (Time T)} {r : Fin N → ℝ} {f : Time T → ℝ}
    (hP : IsPartition S P) (hfr : ∀ i, ∀ t ∈ P i, f t = r i) (hfg : ∀ t ∈ S, f t ≤ g t) :
    ∑ i, r i * muRho ρ (P i) ≤ rsIntegral hT.le ρ S g := by
  set G : ℝ → ℝ := fun x => g (Set.projIcc 0 T hT.le x) with hGdef
  have hG : Continuous G := hg.comp continuous_projIcc
  have hGi : IntegrableOn G (Set.Icc 0 T) ρ.measure := hG.integrableOn_Icc
  have hsub : ∀ i, Subtype.val '' P i ⊆ Set.Icc 0 T := by
    rintro i _ ⟨x, -, rfl⟩; exact x.2
  have hPS : ∀ i, P i ⊆ S := by
    intro i x hx
    rw [hP.2.2]
    exact interior_maximal (subset_closure.trans (closure_mono (Set.subset_iUnion P i)))
      (span_nice hT _ (hP.1 i)).1 hx
  unfold rsIntegral
  rw [← part_integral ρ hc hT hP hGi]
  apply Finset.sum_le_sum
  intro i _
  have hfin : ρ.measure (Subtype.val '' P i) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ρ.measure (Set.Icc 0 T))
    · rw [nu_Icc ρ hc]; exact ENNReal.ofReal_ne_top
    · exact measure_mono (hsub i)
  have e : r i * muRho ρ (P i) = ∫ _ in Subtype.val '' P i, r i ∂ρ.measure := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
  rw [e]
  apply setIntegral_mono_on (integrableOn_const hfin) (hGi.mono_set (hsub i))
    (measurableSet_image_open (span_nice hT _ (hP.1 i)).1)
  rintro _ ⟨x, hx, rfl⟩
  rw [← hfr i x hx]
  simp only [hGdef, Set.projIcc_val]
  exact hfg x (hPS i hx)

/-- Fine partitions: lower sums come within `2ε` of the integral. -/
lemma exists_fine (hT : 0 < T) (h0 : ρ 0 = 0) (h1 : ρ T = 1) {S : Set (Time T)}
    (hS : IsTimeSpan S) (g : Time T → ℝ)
    (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (P : Fin N → Set (Time T)) (r : Fin N → ℝ) (f : Time T → ℝ),
      IsPartition S P ∧ (∀ i, ∀ t ∈ P i, f t = r i) ∧ (∀ t ∈ S, f t ≤ g t) ∧
      rsIntegral hT.le ρ S g - 2 * ε ≤ ∑ i, r i * muRho ρ (P i) := by
  classical
  obtain ⟨N, s, t, hst, hsep, rfl⟩ := hS
  set G : ℝ → ℝ := fun x => g (Set.projIcc 0 T hT.le x) with hGdef
  have hG : Continuous G := hg.comp continuous_projIcc
  have hGi : IntegrableOn G (Set.Icc 0 T) ρ.measure := hG.integrableOn_Icc
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hG.continuousOn) ε hε
  set M : ℕ := ⌈T / δ⌉₊ + 1 with hMdef
  have hM0 : (0 : ℝ) < M := by positivity
  have hM1 : 1 ≤ M := by omega
  have hTM : T / M < δ := by
    rw [div_lt_iff₀ hM0]
    have h1 : T / δ ≤ ⌈T / δ⌉₊ := Nat.le_ceil _
    have h2 : (M : ℝ) = ⌈T / δ⌉₊ + 1 := by rw [hMdef]; push_cast; ring
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  set h : Fin N → ℝ := fun i => (t i - s i) / M with hh
  have hpos : ∀ i, 0 < h i := fun i => div_pos (by linarith [(hst i).2.1]) hM0
  have hle : ∀ i, h i ≤ T / M := fun i =>
    div_le_div_of_nonneg_right (by linarith [(hst i).1, (hst i).2.2]) hM0.le
  set lo : Fin N → ℕ → ℝ := fun i k => s i + k * h i with hlo
  have hloM : ∀ i, lo i M = t i := by
    intro i; simp only [hlo, hh]; field_simp; ring
  have hlo_mono : ∀ i (k l : ℕ), k ≤ l → lo i k ≤ lo i l := by
    intro i k l hkl
    simp only [hlo]
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    nlinarith [hpos i]
  have hlo_succ : ∀ i (k : ℕ), lo i (k + 1) = lo i k + h i := by
    intro i k; simp only [hlo]; push_cast; ring
  have hlo_lb : ∀ i k, s i ≤ lo i k := fun i k => by
    have := hlo_mono i 0 k (Nat.zero_le _); simpa [hlo] using this
  have hlo_ub : ∀ i (k : ℕ), k ≤ M → lo i k ≤ t i := fun i k hk => by
    rw [← hloM i]; exact hlo_mono i k M hk
  -- pieces
  set e := (finProdFinEquiv : Fin N × Fin M ≃ Fin (N * M))
  set Pc : Fin N × Fin M → Set (Time T) := fun ik => bracket T (lo ik.1 ik.2) (lo ik.1 (ik.2 + 1))
    with hPc
  set P : Fin (N * M) → Set (Time T) := fun j => Pc (e.symm j) with hP
  have hpiece : ∀ ik : Fin N × Fin M, 0 ≤ lo ik.1 ik.2 ∧ lo ik.1 ik.2 < lo ik.1 (ik.2 + 1) ∧
      lo ik.1 (ik.2 + 1) ≤ T ∧ s ik.1 ≤ lo ik.1 ik.2 ∧ lo ik.1 (ik.2 + 1) ≤ t ik.1 := by
    rintro ⟨i, k⟩
    have h1 := hlo_lb i k
    have h2 := hlo_ub i (k + 1) (by omega)
    refine ⟨by linarith [(hst i).1], by rw [hlo_succ]; linarith [hpos i], by linarith [(hst i).2.2],
      h1, h2⟩
  have hPcsub : ∀ ik : Fin N × Fin M, Pc ik ⊆ bracket T (s ik.1) (t ik.1) := fun ik =>
    piece_sub (hst ik.1).1 (hpiece ik).2.2.2.1 (hpiece ik).2.2.2.2 (hst ik.1).2.2 (hpiece ik).2.1
  have hPcdisj : ∀ ik jl : Fin N × Fin M, ik ≠ jl → Disjoint (Pc ik) (Pc jl) := by
    have key : ∀ ik jl : Fin N × Fin M, (ik.1 < jl.1 ∨ (ik.1 = jl.1 ∧ ik.2 < jl.2)) →
        Disjoint (Pc ik) (Pc jl) := by
      rintro ⟨i, k⟩ ⟨j, l⟩ h
      rcases h with h | ⟨rfl, h⟩
      · exact Disjoint.mono (hPcsub _) (hPcsub _)
          (bracket_disjoint_of_le (hst i).1 (hst i).2.1 (hsep i j h).le (hst j).2.1 (hst j).2.2)
      · have hkl : (k : ℕ) + 1 ≤ l := h
        exact bracket_disjoint_of_le (hpiece ⟨i, k⟩).1 (hpiece ⟨i, k⟩).2.1
          (hlo_mono i _ _ hkl) (hpiece ⟨i, l⟩).2.1 (hpiece ⟨i, l⟩).2.2.1
    rintro ⟨i, k⟩ ⟨j, l⟩ hne
    rcases lt_trichotomy i j with h | rfl | h
    · exact key (i, k) (j, l) (Or.inl h)
    · rcases lt_trichotomy k l with h' | rfl | h'
      · exact key (i, k) (i, l) (Or.inr ⟨rfl, h'⟩)
      · exact absurd rfl hne
      · exact (key (i, l) (i, k) (Or.inr ⟨rfl, h'⟩)).symm
    · exact (key (j, l) (i, k) (Or.inl h)).symm
  have hPdisj : ∀ a b : Fin (N * M), a ≠ b → Disjoint (P a) (P b) := fun a b hab =>
    hPcdisj _ _ (fun h' => hab (e.symm.injective h'))
  set S := ⋃ i, bracket T (s i) (t i) with hSdef
  have hunion : (⋃ j, P j) = ⋃ ik, Pc ik := by
    ext x; simp only [Set.mem_iUnion, hP]
    exact ⟨fun ⟨j, hj⟩ => ⟨e.symm j, hj⟩, fun ⟨ik, hik⟩ => ⟨e ik, by simpa using hik⟩⟩
  have hPS' : (⋃ j, P j) ⊆ S := by
    rw [hunion]; intro x hx
    obtain ⟨ik, hik⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨ik.1, hPcsub ik hik⟩
  have hSP : S ⊆ closure (⋃ j, P j) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    have hb := bracket_bounds (hst i).1 (hst i).2.2 hi
    set q := (x.1 - s i) / h i with hq
    have hq0 : 0 ≤ q := div_nonneg (by linarith [hb.1]) (hpos i).le
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, k < M ∧ lo i k ≤ x.1 ∧ x.1 ≤ lo i (k + 1) := by
      by_cases hfl : ⌊q⌋₊ < M
      · refine ⟨⌊q⌋₊, hfl, ?_, ?_⟩
        · have := Nat.floor_le hq0
          simp only [hlo]
          have : (⌊q⌋₊ : ℝ) * h i ≤ q * h i := mul_le_mul_of_nonneg_right this (hpos i).le
          rw [hq, div_mul_cancel₀ _ (hpos i).ne'] at this
          linarith
        · have := Nat.lt_floor_add_one q
          simp only [hlo]
          push_cast
          have : q * h i < ((⌊q⌋₊ : ℝ) + 1) * h i := mul_lt_mul_of_pos_right this (hpos i)
          rw [hq, div_mul_cancel₀ _ (hpos i).ne'] at this
          linarith
      · push Not at hfl
        refine ⟨M - 1, by omega, ?_, ?_⟩
        · exact le_trans (hlo_ub i _ (by omega)) (by
            have : (M : ℝ) ≤ q := le_trans (by exact_mod_cast hfl) (Nat.floor_le hq0)
            have h3 : (M : ℝ) * h i ≤ q * h i := mul_le_mul_of_nonneg_right this (hpos i).le
            rw [hq, div_mul_cancel₀ _ (hpos i).ne'] at h3
            have h4 : (M : ℝ) * h i = t i - s i := by simp only [hh]; field_simp
            linarith)
        · rw [Nat.sub_add_cancel hM1, hloM]; exact hb.2
    have hpc := hpiece (i, ⟨k, hk1⟩)
    have hmem : x ∈ closure (Pc (i, ⟨k, hk1⟩)) :=
      mem_closure_bracket hpc.1 hpc.2.1 hpc.2.2.1 x hk2.1 hk2.2
    rw [hunion]
    exact closure_mono (Set.subset_iUnion Pc (i, ⟨k, hk1⟩)) hmem
  have hreg := span_regular hT hst hsep
  have hPart : IsPartition S P := by
    refine ⟨fun j => ?_, hPdisj, ?_⟩
    · have hpc := hpiece (e.symm j)
      exact span_single hpc.1 hpc.2.1 hpc.2.2.1
    · apply Set.Subset.antisymm
      · exact interior_maximal (hSP) (span_isOpen _ ⟨N, s, t, hst, hsep, rfl⟩)
      · rw [← hSdef] at hreg
        conv_rhs => rw [← hreg]
        exact interior_mono (closure_mono hPS')
  -- values
  set r : Fin (N * M) → ℝ := fun j => G (lo (e.symm j).1 (e.symm j).2) - ε with hr
  set f : Time T → ℝ := fun x => if hx : ∃ j, x ∈ P j then r hx.choose else g x with hf
  have hfr : ∀ j, ∀ x ∈ P j, f x = r j := by
    intro j x hx
    have hex : ∃ j, x ∈ P j := ⟨j, hx⟩
    simp only [hf, dif_pos hex]
    by_contra hne
    exact Set.disjoint_left.1 (hPdisj _ _ (fun h' => hne (by rw [h']))) hex.choose_spec hx
  -- closeness on pieces
  have hclose : ∀ j, ∀ x ∈ P j, |g x - G (lo (e.symm j).1 (e.symm j).2)| < ε := by
    intro j x hx
    have hpc := hpiece (e.symm j)
    have hb := bracket_bounds hpc.1 hpc.2.2.1 hx
    have hx' : x.1 ∈ Set.Icc 0 T := x.2
    have hl : lo (e.symm j).1 (e.symm j).2 ∈ Set.Icc 0 T :=
      ⟨hpc.1, by linarith [hpc.2.1, hpc.2.2.1]⟩
    have hd : dist x.1 (lo (e.symm j).1 (e.symm j).2) < δ := by
      rw [Real.dist_eq, abs_lt]
      have := hlo_succ (e.symm j).1 (e.symm j).2
      have := hle (e.symm j).1
      constructor <;> linarith [hb.1, hb.2]
    have := hδG x.1 hx' _ hl hd
    rw [Real.dist_eq] at this
    simpa [hGdef, Set.projIcc_val] using this
  refine ⟨N * M, P, r, f, hPart, hfr, ?_, ?_⟩
  · intro x hx
    by_cases hex : ∃ j, x ∈ P j
    · obtain ⟨j, hj⟩ := hex
      rw [hfr j x hj]
      have := hclose j x hj
      simp only [hr]
      rw [abs_lt] at this
      linarith
    · simp only [hf, dif_neg hex]; exact le_refl _
  · -- the sum dominates the integral of G - 2ε
    have hsub : ∀ A : Set (Time T), Subtype.val '' A ⊆ Set.Icc 0 T := by
      rintro A _ ⟨x, -, rfl⟩; exact x.2
    have hfin : ∀ A : Set (Time T), ρ.measure (Subtype.val '' A) ≠ ⊤ := by
      intro A
      apply ne_top_of_le_ne_top (b := ρ.measure (Set.Icc 0 T))
      · rw [nu_Icc ρ hc]; exact ENNReal.ofReal_ne_top
      · exact measure_mono (hsub A)
    have hGe : IntegrableOn (fun x => G x - 2 * ε) (Set.Icc 0 T) ρ.measure :=
      hGi.sub (integrableOn_const (by rw [nu_Icc ρ hc]; exact ENNReal.ofReal_ne_top))
    have hpart := part_integral ρ hc hT hPart hGe
    have e1 : ∫ x in Subtype.val '' S, (G x - 2 * ε) ∂ρ.measure =
        rsIntegral hT.le ρ S g - (ρ.measure.real (Subtype.val '' S)) * (2 * ε) := by
      rw [integral_sub (hGi.mono_set (hsub S)) (integrableOn_const (hfin S)), setIntegral_const,
        smul_eq_mul]
      rfl
    have hreal : ρ.measure.real (Subtype.val '' S) ≤ 1 := by
      have := nu_image_le_one ρ hc h0 h1 S
      rw [Measure.real]
      calc (ρ.measure (Subtype.val '' S)).toReal ≤ (1 : ENNReal).toReal :=
            ENNReal.toReal_mono ENNReal.one_ne_top this
        _ = 1 := by simp
    have hsum : ∫ x in Subtype.val '' S, (G x - 2 * ε) ∂ρ.measure ≤ ∑ j, r j * muRho ρ (P j) := by
      rw [← hpart]
      apply Finset.sum_le_sum
      intro j _
      have e : r j * muRho ρ (P j) = ∫ _ in Subtype.val '' P j, r j ∂ρ.measure := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
      rw [e]
      apply setIntegral_mono_on (hGe.mono_set (hsub _)) (integrableOn_const (hfin _))
        (measurableSet_image_open (span_nice hT _ (hPart.1 j)).1)
      rintro _ ⟨x, hx, rfl⟩
      have := hclose j x hx
      rw [abs_lt] at this
      simp only [hr, hGdef, Set.projIcc_val]
      linarith [this.2]
    have h2e : 0 < 2 * ε := by linarith
    nlinarith [ENNReal.toReal_nonneg (a := ρ.measure (Subtype.val '' S))]

/-- The content integral of a continuous function equals its Lebesgue–Stieltjes integral. -/
lemma integrator_eq (hT : 0 < T) (h0 : ρ 0 = 0) (h1 : ρ T = 1) {S : Set (Time T)}
    (hS : IsTimeSpan S) (g : Time T → ℝ) (hg : Continuous g) :
    integrator (muRho ρ) S g = rsIntegral hT.le ρ S g := by
  unfold integrator
  set V := {v : ℝ | ∃ (N : ℕ) (P : Fin N → Set (Time T)) (r : Fin N → ℝ)
      (f : Time T → ℝ), IsPartition S P ∧
      (∀ i, ∀ t ∈ P i, f t = r i) ∧
      (∀ t ∈ S, f t ≤ g t) ∧
      v = ∑ i, r i * muRho ρ (P i)} with hV
  have hub : ∀ v ∈ V, v ≤ rsIntegral hT.le ρ S g := by
    rintro v ⟨N, P, r, f, hP, hfr, hfg, rfl⟩
    exact lowersum_le ρ hc hT g hg hP hfr hfg
  have hne : V.Nonempty := by
    obtain ⟨N, P, r, f, hP, hfr, hfg, -⟩ := exists_fine ρ hc hT h0 h1 hS g hg one_pos
    exact ⟨_, N, P, r, f, hP, hfr, hfg, rfl⟩
  have hbdd : BddAbove V := ⟨_, hub⟩
  apply le_antisymm (csSup_le hne hub)
  apply le_of_forall_sub_le
  intro ε hε
  obtain ⟨N, P, r, f, hP, hfr, hfg, hv⟩ := exists_fine ρ hc hT h0 h1 hS g hg (half_pos hε)
  have : (∑ i, r i * muRho ρ (P i)) ∈ V := ⟨N, P, r, f, hP, hfr, hfg, rfl⟩
  have := le_csSup hbdd this
  linarith

end integ

end IDUILib


open IntertempDUI.Finite MeasureTheory

namespace IDUILib

lemma span_univ_aux {T : ℝ} (hT : 0 < T) : IsTimeSpan (Set.univ : Set (Time T)) := by
  rw [← bracket_univ hT]; exact span_single (le_refl _) hT (le_refl _)

theorem lemmaB1 {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (u : X → ℝ) (hu : Continuous u)
    (hrep : ∀ x y : X, sy pref x y ↔ u y ≤ u x)
    (hM : MinEqn A pref) :
    ∀ a ∈ A, Comeasurable (u ∘ a) := by
  intro a ha r
  -- intermediate value: if `r` is attained between two values of `u`, it is a value of `u`
  have ivt : ∀ x1 x2 : X, u x1 ≤ r → r ≤ u x2 → ∃ x, u x = r := by
    intro x1 x2 h1 h2
    have := isPreconnected_univ.intermediate_value (Set.mem_univ x1) (Set.mem_univ x2)
      hu.continuousOn ⟨h1, h2⟩
    obtain ⟨x, -, hx⟩ := this
    exact ⟨x, hx⟩
  constructor
  · by_cases hlow : ∀ x, r < u x
    · have : {t | (u ∘ a) t ≤ r} = (∅ : Set (Time T)) := by
        ext t; simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_le]; exact hlow _
      rw [this, interior_empty]; exact span_empty'
    push Not at hlow
    obtain ⟨x1, hx1⟩ := hlow
    by_cases hhigh : ∀ x, u x ≤ r
    · have : {t | (u ∘ a) t ≤ r} = (Set.univ : Set (Time T)) := by
        ext t; simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact hhigh _
      rw [this, interior_univ]; exact (span_univ_aux hT)
    push Not at hhigh
    obtain ⟨x2, hx2⟩ := hhigh
    obtain ⟨x, rfl⟩ := ivt x1 x2 hx1 hx2.le
    have : {t | (u ∘ a) t ≤ u x} = {t | sy pref x (a t)} := by
      ext t; simp only [Function.comp, Set.mem_ofPred_eq]; exact (hrep x (a t)).symm
    rw [this]; exact (hM x a ha).2
  · by_cases hlow : ∀ x, u x < r
    · have : {t | r ≤ (u ∘ a) t} = (∅ : Set (Time T)) := by
        ext t; simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_le]; exact hlow _
      rw [this, interior_empty]; exact span_empty'
    push Not at hlow
    obtain ⟨x2, hx2⟩ := hlow
    by_cases hhigh : ∀ x, r ≤ u x
    · have : {t | r ≤ (u ∘ a) t} = (Set.univ : Set (Time T)) := by
        ext t; simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact hhigh _
      rw [this, interior_univ]; exact (span_univ_aux hT)
    push Not at hhigh
    obtain ⟨x1, hx1⟩ := hhigh
    obtain ⟨x, rfl⟩ := ivt x1 x2 hx1.le hx2
    have : {t | u x ≤ (u ∘ a) t} = {t | sy pref (a t) x} := by
      ext t; simp only [Function.comp, Set.mem_ofPred_eq]; exact (hrep (a t) x).symm
    rw [this]; exact (hM x a ha).1

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


open IntertempDUI.Finite MeasureTheory

namespace IDUILib

variable {T : ℝ}

lemma disjoint_adj' {r s t : ℝ} (h0r : 0 ≤ r) (hrs : r < s) (hst : s < t) (htT : t ≤ T) :
    Disjoint (bracket T r s) (bracket T s t) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, h1 | h1⟩ ⟨h2 | h2, -⟩
  · linarith
  · linarith [h2.1]
  · linarith [h1.1]
  · linarith [h2.1]

/-- The distribution function of a content on `[0,T]`. -/
noncomputable def rhoFun (T : ℝ) (μ : Set (Time T) → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else μ (bracket T 0 (min x T))

section content

variable {μ : Set (Time T) → ℝ} (hμ : IsContent μ)
include hμ

lemma content_empty : μ ∅ = 0 := by
  have h := hμ.2.2 ∅ ∅ span_empty' span_empty' (Set.disjoint_empty _)
  have : join (∅ : Set (Time T)) ∅ = ∅ := by unfold join; simp
  rw [this] at h; linarith

lemma content_nonneg {S : Set (Time T)} (hS : IsTimeSpan S) : 0 ≤ μ S := (hμ.2.1 S hS).1

lemma content_mono (hT : 0 < T) {Q S : Set (Time T)} (hQ : IsTimeSpan Q) (hS : IsTimeSpan S)
    (hQS : Q ⊆ S) : μ Q ≤ μ S := by
  have hSn := span_nice hT S hS
  have hj : join (S ∩ Q) (S ∩ neg Q) = S :=
    join_inter_eq hSn.1 hSn.2.1 (by rw [join_neg_univ]; exact Set.subset_univ _)
  rw [Set.inter_eq_right.2 hQS] at hj
  have hspan : IsTimeSpan (S ∩ neg Q) := span_inter hT hS (span_neg hT hQ)
  have hdis : Disjoint Q (S ∩ neg Q) :=
    Disjoint.mono_right Set.inter_subset_right (disjoint_neg Q)
  have := hμ.2.2 Q (S ∩ neg Q) hQ hspan hdis
  rw [hj] at this
  linarith [content_nonneg hμ hspan]

lemma content_bracket_add (hT : 0 < T) {r s t : ℝ} (h0r : 0 ≤ r) (hrs : r < s) (hst : s < t)
    (htT : t ≤ T) : μ (bracket T r t) = μ (bracket T r s) + μ (bracket T s t) := by
  rw [← join_adjacent hT h0r hrs hst htT]
  exact hμ.2.2 _ _ (span_single h0r hrs (by linarith)) (span_single (by linarith) hst htT)
    (disjoint_adj' h0r hrs hst htT)

omit hμ in
lemma rho_eq {x : ℝ} (hx : 0 < x) (hxT : x ≤ T) : rhoFun T μ x = μ (bracket T 0 x) := by
  unfold rhoFun; rw [if_neg (not_le.2 hx), min_eq_left hxT]

omit hμ in
lemma rho_zero : rhoFun T μ 0 = 0 := by unfold rhoFun; simp

lemma rho_T (hT : 0 < T) : rhoFun T μ T = 1 := by
  rw [rho_eq hT (le_refl _), bracket_univ hT]; exact hμ.1

lemma rho_diff (hT : 0 < T) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T) :
    rhoFun T μ b - rhoFun T μ a = μ (bracket T a b) := by
  rcases lt_or_eq_of_le ha with ha0 | ha0
  · rw [rho_eq ha0 (by linarith), rho_eq (by linarith) hb,
      content_bracket_add hμ hT (le_refl _) ha0 hab hb]
    ring
  · rw [← ha0, rho_zero, rho_eq (by linarith) hb]; ring

omit hμ in
lemma rho_clamp (hT : 0 < T) (x : ℝ) : rhoFun T μ x = rhoFun T μ (max 0 (min x T)) := by
  unfold rhoFun
  by_cases hx : x ≤ 0
  · rw [if_pos hx, if_pos (by simp [hx])]
  · push Not at hx
    have h1 : max 0 (min x T) = min x T := max_eq_right (le_min hx.le hT.le)
    rw [if_neg (not_le.2 hx), h1, if_neg (not_le.2 (lt_min hx hT)), min_eq_left (min_le_right _ _)]

lemma rho_mono (hT : 0 < T) : Monotone (rhoFun T μ) := by
  intro x y hxy
  rw [rho_clamp hT x, rho_clamp hT y]
  set a := max 0 (min x T)
  set b := max 0 (min y T)
  have hab : a ≤ b := max_le_max (le_refl _) (min_le_min hxy (le_refl _))
  have ha0 : 0 ≤ a := le_max_left _ _
  have hbT : b ≤ T := max_le hT.le (min_le_right _ _)
  rcases lt_or_eq_of_le hab with h | h
  · have := rho_diff hμ hT ha0 h hbT
    linarith [content_nonneg hμ (span_single ha0 h hbT)]
  · rw [h]

/-- Continuity on `[0,T]` from nonatomicity. -/
lemma rho_cont_on (hT : 0 < T) (hna : Nonatomic μ) (c : ℝ) (hc0 : 0 ≤ c) (hcT : c ≤ T)
    (ε : ℝ) (hε : 0 < ε) : ∃ η > 0, ∀ d, 0 ≤ d → d ≤ T → |d - c| < η →
      |rhoFun T μ d - rhoFun T μ c| < ε := by
  obtain ⟨S, hS, hcS, hμS⟩ := hna ⟨c, Set.mem_Icc.2 ⟨hc0, hcT⟩⟩ ε hε
  have hSo : IsOpen S := span_isOpen S hS
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hSo _ hcS
  refine ⟨η, hη, fun d hd0 hdT hdc => ?_⟩
  have key : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ T → |a - c| < η → |b - c| < η →
      rhoFun T μ b - rhoFun T μ a < ε := by
    intro a b ha hab hb hac hbc
    rw [rho_diff hμ hT ha hab hb]
    refine lt_of_le_of_lt (content_mono hμ hT (span_single ha hab hb) hS ?_) hμS
    intro z hz
    have hzb := bracket_bounds ha hb hz
    apply hball
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    rw [abs_lt] at hac hbc ⊢
    constructor <;> linarith [hzb.1, hzb.2]
  have hcc : |c - c| < η := by simp [hη]
  rcases lt_trichotomy d c with h | rfl | h
  · have := key d c hd0 h hcT hdc hcc
    have hm := rho_mono hμ hT h.le
    rw [abs_lt]; constructor <;> linarith
  · simp [hε]
  · have := key c d hc0 h hdT hcc hdc
    have hm := rho_mono hμ hT h.le
    rw [abs_lt]; constructor <;> linarith

lemma rho_continuous (hT : 0 < T) (hna : Nonatomic μ) : Continuous (rhoFun T μ) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  set c := max 0 (min x T)
  have hc0 : 0 ≤ c := le_max_left _ _
  have hcT : c ≤ T := max_le hT.le (min_le_right _ _)
  obtain ⟨η, hη, hη'⟩ := rho_cont_on hμ hT hna c hc0 hcT ε hε
  refine ⟨η, hη, fun y hy => ?_⟩
  rw [Real.dist_eq, rho_clamp hT y, rho_clamp hT x]
  apply hη' _ (le_max_left _ _) (max_le hT.le (min_le_right _ _))
  rw [Real.dist_eq] at hy
  calc |max 0 (min y T) - c| ≤ |y - x| := by
        have h1 := abs_max_sub_max_le_max 0 (min y T) 0 (min x T)
        have h2 := abs_min_sub_min_le_max y T x T
        simp only [sub_self, abs_zero] at h1 h2
        have h3 : max 0 |min y T - min x T| = |min y T - min x T| := max_eq_right (abs_nonneg _)
        have h4 : max |y - x| 0 = |y - x| := max_eq_left (abs_nonneg _)
        rw [h3] at h1; rw [h4] at h2
        linarith
    _ < η := hy

end content

end IDUILib


open IntertempDUI.Finite MeasureTheory

namespace IDUILib

variable {T : ℝ}

lemma integrator_congr {μ1 μ2 : Set (Time T) → ℝ}
    (h : ∀ S, IsTimeSpan S → μ1 S = μ2 S) (S : Set (Time T)) (g : Time T → ℝ) :
    integrator μ1 S g = integrator μ2 S g := by
  unfold integrator
  congr 1
  ext v
  constructor
  · rintro ⟨N, P, r, f, hP, h1, h2, rfl⟩
    exact ⟨N, P, r, f, hP, h1, h2, Finset.sum_congr rfl fun i _ => by rw [h _ (hP.1 i)]⟩
  · rintro ⟨N, P, r, f, hP, h1, h2, rfl⟩
    exact ⟨N, P, r, f, hP, h1, h2, Finset.sum_congr rfl fun i _ => by rw [h _ (hP.1 i)]⟩

lemma iUnion_fin_succ {α : Type*} {N : ℕ} (f : Fin (N + 1) → Set α) :
    (⋃ i, f i) = (⋃ i : Fin N, f (Fin.castSucc i)) ∪ f (Fin.last N) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr hi
    | cast j => exact Or.inl ⟨j, hi⟩
  · rintro (⟨j, hj⟩ | h)
    · exact ⟨_, hj⟩
    · exact ⟨_, h⟩

/-- Two contents agreeing on brackets agree on all time spans. -/
lemma content_ext (hT : 0 < T) {μ1 μ2 : Set (Time T) → ℝ}
    (h0 : μ1 ∅ = μ2 ∅)
    (hadd1 : ∀ Q R, IsTimeSpan Q → IsTimeSpan R → Disjoint Q R → μ1 (join Q R) = μ1 Q + μ1 R)
    (hadd2 : ∀ Q R, IsTimeSpan Q → IsTimeSpan R → Disjoint Q R → μ2 (join Q R) = μ2 Q + μ2 R)
    (hbr : ∀ r s, 0 ≤ r → r < s → s ≤ T → μ1 (bracket T r s) = μ2 (bracket T r s)) :
    ∀ S, IsTimeSpan S → μ1 S = μ2 S := by
  have key : ∀ N (s t : Fin N → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) →
      (∀ i j : Fin N, i < j → t i < s j) →
      μ1 (⋃ i, bracket T (s i) (t i)) = μ2 (⋃ i, bracket T (s i) (t i)) := by
    intro N
    induction N with
    | zero => intro s t _ _; simp only [Set.iUnion_of_empty]; exact h0
    | succ N ih =>
      intro s t hst hsep
      have hst' : ∀ i : Fin N, 0 ≤ s (Fin.castSucc i) ∧ s (Fin.castSucc i) < t (Fin.castSucc i) ∧
          t (Fin.castSucc i) ≤ T := fun i => hst _
      have hsep' : ∀ i j : Fin N, i < j → t (Fin.castSucc i) < s (Fin.castSucc j) :=
        fun i j hij => hsep _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)
      set S' := ⋃ i : Fin N, bracket T (s (Fin.castSucc i)) (t (Fin.castSucc i))
      set B := bracket T (s (Fin.last N)) (t (Fin.last N))
      have hS' : IsTimeSpan S' := ⟨N, _, _, hst', hsep', rfl⟩
      have hB : IsTimeSpan B := span_single (hst _).1 (hst _).2.1 (hst _).2.2
      have hdis : Disjoint S' B := by
        rw [Set.disjoint_iUnion_left]
        intro i
        have := hsep (Fin.castSucc i) (Fin.last N) (Fin.castSucc_lt_last i)
        exact bracket_disjoint_of_le (hst _).1 (hst _).2.1 this.le (hst _).2.1 (hst _).2.2
      have hU : (⋃ i, bracket T (s i) (t i)) = join S' B := by
        rw [iUnion_fin_succ (fun i => bracket T (s i) (t i))]
        unfold join
        rw [← iUnion_fin_succ (fun i => bracket T (s i) (t i))]
        exact (span_regular hT hst hsep).symm
      rw [hU, hadd1 _ _ hS' hB hdis, hadd2 _ _ hS' hB hdis, ih _ _ hst' hsep',
        hbr _ _ (hst _).1 (hst _).2.1 (hst _).2.2]
  rintro S ⟨N, s, t, hst, hsep, rfl⟩
  exact key N s t hst hsep

end IDUILib


open IntertempDUI.Finite MeasureTheory

open IDUILib in
theorem solution {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (u : X → ℝ) (μ : Set (Time T) → ℝ)
    (hrep : IsContentUtilityRep A pref u μ) (hfs : FullSupport μ) (hna : Nonatomic μ) :
    ∃ ρ : StieltjesFunction ℝ, IsDUIRep (le_of_lt hT) A pref ρ u ∧
      ∀ S, IsTimeSpan S → (ρ.measure (Subtype.val '' S)).toReal = μ S := by
  obtain ⟨hu, hμ, -, -, hspan, hint⟩ := hrep
  have hcont := rho_continuous hμ hT hna
  let ρ : StieltjesFunction ℝ :=
    ⟨rhoFun T μ, rho_mono hμ hT, fun x => hcont.continuousAt.continuousWithinAt⟩
  have hρ : (ρ : ℝ → ℝ) = rhoFun T μ := rfl
  have hc : Continuous (ρ : ℝ → ℝ) := by rw [hρ]; exact hcont
  have h0 : ρ 0 = 0 := rho_zero
  have h1 : ρ T = 1 := rho_T hμ hT
  -- the measure of ρ agrees with μ on spans
  have hagree : ∀ S, IsTimeSpan S → muRho ρ S = μ S := by
    apply content_ext hT
    · show (ρ.measure (Subtype.val '' ∅)).toReal = μ ∅
      rw [Set.image_empty, measure_empty, content_empty hμ]; rfl
    · intro Q R hQ hR hQR
      show (ρ.measure (Subtype.val '' join Q R)).toReal =
        (ρ.measure (Subtype.val '' Q)).toReal + (ρ.measure (Subtype.val '' R)).toReal
      rw [nu_join ρ hc hT hQ hR hQR, ENNReal.toReal_add (nu_image_ne_top ρ hc h0 h1 Q)
        (nu_image_ne_top ρ hc h0 h1 R)]
    · exact hμ.2.2
    · intro r s hr hrs hs
      show (ρ.measure (Subtype.val '' bracket T r s)).toReal = μ (bracket T r s)
      have hnn : 0 ≤ ρ s - ρ r := by
        have := rho_mono hμ hT hrs.le; rw [hρ]; linarith
      rw [nu_image_bracket ρ hc hr hs, ENNReal.toReal_ofReal hnn, ← rho_diff hμ hT hr hrs hs]
  have hint_eq : ∀ S, IsTimeSpan S → ∀ a : Traj T X,
      integrator μ S (u ∘ a) = rsIntegral (le_of_lt hT) ρ S (u ∘ a) := by
    intro S hS a
    rw [← integrator_congr hagree S, integrator_eq ρ hc hT h0 h1 hS _ (hu.comp a.continuous)]
  refine ⟨ρ, ⟨hu, hc, ?_, h0, h1, ?_, ?_⟩, hagree⟩
  · intro a ha b hb hab
    have := rho_diff hμ hT ha.1 hab hb.2
    have hpos : 0 < μ (bracket T a b) := by
      apply hfs _ (span_single ha.1 hab hb.2)
      exact ⟨⟨(a + b) / 2, by linarith [ha.1], by linarith [hb.2]⟩,
        mem_bracket_of_lt (by simp only; linarith) (by simp only; linarith)⟩
    show rhoFun T μ a < rhoFun T μ b
    linarith
  · intro S hS a ha b hb
    rw [hspan S hS a ha b hb, hint_eq S hS a, hint_eq S hS b]
  · intro I hI a ha b hb
    obtain ⟨r, s, hr, hrs, hs, rfl⟩ := hI
    have hS := span_single (T := T) hr hrs hs
    rw [hint _ ⟨r, s, hr, hrs, hs, rfl⟩ a ha b hb, hint_eq _ hS a, hint_eq _ hS b]
