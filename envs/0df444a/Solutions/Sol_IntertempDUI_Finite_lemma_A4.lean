-- Prove2me | solution 1 for IntertempDUI.Finite.lemma_A4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:30:07.946229+00:00
-- url     : https://prove2.me/submissions/ba0ea5c1-4668-41ce-8d5d-966ca6b0fd6b

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

open IDUILib in
theorem solution {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref) (hR : RichnessStar A pref) :
    LSepStar A pref ↔ LSep A pref := by
  have huniv : IsTimeInterval (Set.univ : Set (Time T)) :=
    ⟨0, T, le_refl _, hT, le_refl _, (bracket_univ hT).symm⟩
  obtain ⟨hcompl, htrans, -, -⟩ := hstd _ huniv
  constructor
  · rintro ⟨order, hord, hrel⟩ S hS a ha a' ha' b hb b' hb' hea heb hc hc'
    rw [hrel S hS a ha b hb hc, hrel S hS a' ha' b' hb' hc']
    exact (hord S hS).2.2 a ha b hb a' ha' b' hb' hea heb
  · intro hL
    refine ⟨induced A pref, ?_, ?_⟩
    · intro S hS
      have hN := span_neg hT hS
      have hD := disjoint_neg S
      refine ⟨?_, ?_, ?_⟩
      · intro a ha b hb
        obtain ⟨f, hf, hfS, hfc⟩ := hR S (neg S) hS hN hD b hb a ha
        rcases hcompl a ha f hf with h | h
        · left
          exact ⟨a, ha, f, hf, fun _ _ => rfl, hfS, fun I hI => ⟨(hfc I hI).2, (hfc I hI).1⟩, h⟩
        · right
          exact ⟨f, hf, a, ha, hfS, fun _ _ => rfl, hfc, h⟩
      · rintro a ha b hb c hc ⟨a1, ha1, b1, hb1, ea1, eb1, hc1, hp1⟩
          ⟨b2, hb2, c2, hc2, eb2, ec2, hc2', hp2⟩
        obtain ⟨b', hb', hb'S, hb'c⟩ := hR S (neg S) hS hN hD b hb a ha
        obtain ⟨c', hc', hc'S, hc'c⟩ := hR S (neg S) hS hN hD c hc b' hb'
        have p1 : pref Set.univ a b' := by
          refine (hL S hS a1 ha1 a ha b1 hb1 b' hb' ea1 ?_ hc1 ?_).1 hp1
          · intro x hx; rw [eb1 hx, hb'S hx]
          · intro I hI; exact ⟨(hb'c I hI).2, (hb'c I hI).1⟩
        have p2 : pref Set.univ b' c' := by
          refine (hL S hS b2 hb2 b' hb' c2 hc2 c' hc' ?_ ?_ hc2' ?_).1 hp2
          · intro x hx; rw [eb2 hx, hb'S hx]
          · intro x hx; rw [ec2 hx, hc'S hx]
          · intro I hI; exact ⟨(hc'c I hI).2, (hc'c I hI).1⟩
        refine ⟨a, ha, c', hc', fun _ _ => rfl, hc'S, fun I hI => ?_, htrans a ha b' hb' c' hc' p1 p2⟩
        obtain ⟨-, htI, -, -⟩ := hstd I (component_interval hT hN hI)
        obtain ⟨u1, u2⟩ := hb'c I hI
        obtain ⟨v1, v2⟩ := hc'c I hI
        exact ⟨htI a ha b' hb' c' hc' u2 v2, htI c' hc' b' hb' a ha v1 u1⟩
      · intro a ha b hb a' ha' b' hb' hea heb
        constructor
        · rintro ⟨a1, ha1, b1, hb1, e1, e2, hc, hp⟩
          exact ⟨a1, ha1, b1, hb1, fun x hx => (e1 hx).trans (hea hx),
            fun x hx => (e2 hx).trans (heb hx), hc, hp⟩
        · rintro ⟨a1, ha1, b1, hb1, e1, e2, hc, hp⟩
          exact ⟨a1, ha1, b1, hb1, fun x hx => (e1 hx).trans (hea hx).symm,
            fun x hx => (e2 hx).trans (heb hx).symm, hc, hp⟩
    · intro S hS a ha b hb hc
      constructor
      · intro h; exact ⟨a, ha, b, hb, fun _ _ => rfl, fun _ _ => rfl, hc, h⟩
      · rintro ⟨a1, ha1, b1, hb1, e1, e2, hc1, hp⟩
        exact (hL S hS a ha a1 ha1 b hb b1 hb1 (fun x hx => (e1 hx).symm)
          (fun x hx => (e2 hx).symm) hc hc1).2 hp
