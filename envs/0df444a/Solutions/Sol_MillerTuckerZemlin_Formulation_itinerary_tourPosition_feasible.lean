-- Prove2me | solution 1 for MillerTuckerZemlin.Formulation.itinerary_tourPosition_feasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:59:37.728724+00:00
-- url     : https://prove2.me/submissions/b06995dc-82a0-4ee9-b444-024ab4cc0ec5

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model



namespace MillerTuckerZemlin.Formulation


theorem mtz_tourArcs_fst {n : ℕ} (T : List (Fin (n + 1))) :
    (tourArcs T).map Prod.fst = 0 :: T := by
  unfold tourArcs
  rw [List.map_fst_zip]
  simp

theorem mtz_tourArcs_snd {n : ℕ} (T : List (Fin (n + 1))) :
    (tourArcs T).map Prod.snd = T ++ [0] := by
  unfold tourArcs
  rw [List.map_snd_zip]
  simp

theorem mtz_arcs_fst {n : ℕ} (I : Itinerary n) :
    (arcs I).map Prod.fst = (I.map (fun T => 0 :: T)).flatten := by
  unfold arcs
  rw [List.map_flatMap]
  simp [mtz_tourArcs_fst, List.flatMap_def]

theorem mtz_arcs_snd {n : ℕ} (I : Itinerary n) :
    (arcs I).map Prod.snd = (I.map (fun T => T ++ [0])).flatten := by
  unfold arcs
  rw [List.map_flatMap]
  simp [mtz_tourArcs_snd, List.flatMap_def]

theorem mtz_sum_count_snd {α : Type*} [Fintype α] [DecidableEq α] (L : List (α × α)) (j : α) :
    ∑ i, L.count (i, j) = (L.map Prod.snd).count j := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨a1, a2⟩ := a
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.map_cons]
    congr 1
    by_cases h : a2 = j
    · subst h; simp
    · simp [h]

theorem mtz_sum_count_fst {α : Type*} [Fintype α] [DecidableEq α] (L : List (α × α)) (i : α) :
    ∑ j, L.count (i, j) = (L.map Prod.fst).count i := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨a1, a2⟩ := a
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.map_cons]
    congr 1
    by_cases h : a1 = i
    · subst h; simp
    · simp [h]

theorem mtz_count_flatten_map {n : ℕ} (I : Itinerary n) (f : List (Fin (n+1)) → List (Fin (n+1)))
    (c : Fin (n+1)) :
    ((I.map f).flatten).count c = (I.map (fun T => (f T).count c)).sum := by
  rw [List.count_flatten]
  simp [List.map_map, Function.comp_def]

theorem mtz_colsum {n : ℕ} (I : Itinerary n) (j : Fin (n+1)) :
    ∑ i, arcCount I i j = I.flatten.count j + (if j = 0 then I.length else 0) := by
  unfold arcCount
  rw [mtz_sum_count_snd, mtz_arcs_snd, mtz_count_flatten_map]
  have : (I.map (fun T => (T ++ [0]).count j)).sum =
      (I.map (fun T => T.count j + (if j = 0 then 1 else 0))).sum := by
    congr 1
    apply List.map_congr_left
    intro T _
    rw [List.count_append]
    by_cases h : j = 0
    · subst h; simp
    · simp [h, List.count_singleton, Ne.symm h]
  rw [this, List.sum_map_add]
  simp [List.count_flatten, List.map_map, Function.comp_def]

theorem mtz_rowsum {n : ℕ} (I : Itinerary n) (i : Fin (n+1)) :
    ∑ j, arcCount I i j = I.flatten.count i + (if i = 0 then I.length else 0) := by
  unfold arcCount
  rw [mtz_sum_count_fst, mtz_arcs_fst, mtz_count_flatten_map]
  have : (I.map (fun T => (0 :: T).count i)).sum =
      (I.map (fun T => T.count i + (if i = 0 then 1 else 0))).sum := by
    congr 1
    apply List.map_congr_left
    intro T _
    rw [List.count_cons]
    by_cases h : i = 0
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [this, List.sum_map_add]
  simp [List.count_flatten, List.map_map, Function.comp_def]



theorem mtz_mem_tourArcs {n : ℕ} (T : List (Fin (n + 1))) (i j : Fin (n+1)) :
    (i, j) ∈ tourArcs T ↔ ∃ m, m ≤ T.length ∧ (0 :: (T ++ [0]))[m]? = some i ∧
      (0 :: (T ++ [0]))[m+1]? = some j := by
  have hA : ∀ m, m ≤ T.length → (0 :: (T ++ [0]))[m]? = (0 :: T)[m]? := by
    intro m hm
    cases m with
    | zero => simp
    | succ k =>
      simp only [List.getElem?_cons_succ]
      rw [List.getElem?_append_left (by simp at *; omega)]
  have hB : ∀ m, m ≤ T.length → (0 :: (T ++ [0]))[m+1]? = (T ++ [0])[m]? := by
    intro m _; simp
  unfold tourArcs
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨m, hm, h⟩
    simp only [List.length_zip, List.length_cons, List.length_append, List.length_singleton] at hm
    simp only [List.getElem_zip, Prod.mk.injEq] at h
    refine ⟨m, by omega, ?_, ?_⟩
    · rw [hA m (by omega), List.getElem?_eq_getElem (by simp; omega)]; simp [← h.1]
    · rw [hB m (by omega), List.getElem?_eq_getElem (by simp; omega)]; simp [← h.2]
  · rintro ⟨m, hm, h1, h2⟩
    have hl : m < ((0 :: T).zip (T ++ [0])).length := by simp; omega
    refine ⟨m, hl, ?_⟩
    simp only [List.getElem_zip, Prod.mk.injEq]
    rw [hA m hm, List.getElem?_eq_getElem (by simp; omega)] at h1
    rw [hB m hm, List.getElem?_eq_getElem (by simp; omega)] at h2
    simp at h1 h2
    exact ⟨h1, h2⟩

theorem mtz_pairwise_unique {α : Type*} (I : List (List α)) (hP : I.Pairwise List.Disjoint)
    (T T' : List α) (hT : T ∈ I) (hT' : T' ∈ I) (c : α) (h1 : c ∈ T) (h2 : c ∈ T') : T = T' := by
  induction I with
  | nil => simp at hT
  | cons S I ih =>
    rw [List.pairwise_cons] at hP
    rw [List.mem_cons] at hT hT'
    rcases hT with rfl | hT <;> rcases hT' with rfl | hT'
    · rfl
    · exact absurd h2 (fun h => hP.1 T' hT' h1 h)
    · exact absurd h1 (fun h => hP.1 T hT h2 h)
    · exact ih hP.2 hT hT'

theorem mtz_itin_tour_nodup {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I) {T : List (Fin (n+1))}
    (hT : T ∈ I) : T.Nodup := by
  have := (List.nodup_flatten.mp hI.2.1).1
  exact this T hT

theorem mtz_itin_unique {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I)
    {T T' : List (Fin (n+1))} (hT : T ∈ I) (hT' : T' ∈ I) {c : Fin (n+1)} (h1 : c ∈ T) (h2 : c ∈ T') :
    T = T' :=
  mtz_pairwise_unique I (List.nodup_flatten.mp hI.2.1).2 T T' hT hT' c h1 h2

theorem mtz_tourPosition_eq {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I)
    {T : List (Fin (n+1))} (hT : T ∈ I) {c : Fin (n+1)} (hc0 : c ≠ 0) (hcT : c ∈ T) :
    tourPosition I c = T.idxOf c + 1 := by
  unfold tourPosition
  rw [if_neg hc0]
  have hs : (I.find? (fun T => decide (c ∈ T))).isSome := by
    rw [List.find?_isSome]
    exact ⟨T, hT, by simpa using hcT⟩
  obtain ⟨T', hT'⟩ := Option.isSome_iff_exists.mp hs
  rw [hT']
  have h1 := List.mem_of_find?_eq_some hT'
  have h2 := List.find?_some hT'
  simp at h2
  have := mtz_itin_unique hI h1 hT h2 hcT
  simp [this]

theorem mtz_tourPosition_bounds {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I)
    {c : Fin (n+1)} (hc0 : c ≠ 0) : 1 ≤ tourPosition I c ∧ tourPosition I c ≤ p := by
  have hc := hI.2.2 c hc0
  rw [List.mem_flatten] at hc
  obtain ⟨T, hT, hcT⟩ := hc
  rw [mtz_tourPosition_eq hI hT hc0 hcT]
  have := (hI.1 T hT).2.2
  have := List.idxOf_lt_length_of_mem hcT
  omega



theorem mtz_L_get {n : ℕ} (T : List (Fin (n + 1))) (k : ℕ) (hk : k < T.length) :
    (0 :: (T ++ [0]))[k+1]? = some T[k] := by
  simp [List.getElem?_append_left hk]

theorem mtz_L_last {n : ℕ} (T : List (Fin (n + 1))) :
    (0 :: (T ++ [0]))[T.length+1]? = some 0 := by
  simp

theorem mtz_arc_cases {n : ℕ} (T : List (Fin (n + 1))) (i j : Fin (n+1))
    (h : (i, j) ∈ tourArcs T) :
    (i = 0 ∧ ∃ hl : 0 < T.length, j = T[0]) ∨
    (∃ k, ∃ hk : k + 1 < T.length, i = T[k] ∧ j = T[k+1]) ∨
    (∃ hl : 0 < T.length, i = T[T.length - 1] ∧ j = 0) ∨
    (T = [] ∧ i = 0 ∧ j = 0) := by
  rw [mtz_mem_tourArcs] at h
  obtain ⟨m, hm, h1, h2⟩ := h
  rcases m with _ | k
  · simp at h1 h2
    by_cases hl : 0 < T.length
    · left
      refine ⟨h1.symm, hl, ?_⟩
      rw [List.getElem_append_left hl] at h2
      exact h2.symm
    · right; right; right
      have : T = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp at h2
      exact ⟨rfl, h1.symm, h2.symm⟩
  · have hk : k < T.length := by omega
    rw [mtz_L_get T k hk] at h1
    simp at h1
    by_cases hk2 : k + 1 < T.length
    · right; left
      rw [mtz_L_get T (k+1) hk2] at h2
      simp at h2
      exact ⟨k, hk2, h1.symm, h2.symm⟩
    · right; right; left
      have e : k + 1 = T.length := by omega
      rw [e, mtz_L_last] at h2
      simp at h2
      refine ⟨by omega, ?_, h2.symm⟩
      have : T.length - 1 = k := by omega
      simp [this, h1.symm]

theorem mtz_arc_mem_first {n : ℕ} (T : List (Fin (n + 1))) (hl : 0 < T.length) :
    ((0 : Fin (n+1)), T[0]) ∈ tourArcs T := by
  rw [mtz_mem_tourArcs]
  refine ⟨0, by omega, by simp, ?_⟩
  rw [mtz_L_get T 0 hl]

theorem mtz_arc_mem_mid {n : ℕ} (T : List (Fin (n + 1))) (k : ℕ) (hk : k + 1 < T.length) :
    (T[k], T[k+1]) ∈ tourArcs T := by
  rw [mtz_mem_tourArcs]
  refine ⟨k+1, by omega, mtz_L_get T k (by omega), mtz_L_get T (k+1) hk⟩

theorem mtz_arc_mem_last {n : ℕ} (T : List (Fin (n + 1))) (hl : 0 < T.length) :
    (T[T.length - 1], (0 : Fin (n+1))) ∈ tourArcs T := by
  rw [mtz_mem_tourArcs]
  have e : T.length - 1 + 1 = T.length := by omega
  refine ⟨T.length, le_rfl, ?_, ?_⟩
  · have := mtz_L_get T (T.length - 1) (by omega)
    rwa [e] at this
  · exact mtz_L_last T

theorem mtz_tourArcs_ne {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I) {T : List (Fin (n+1))}
    (hT : T ∈ I) {i j : Fin (n+1)} (h : (i, j) ∈ tourArcs T) : i ≠ j := by
  have hnd := mtz_itin_tour_nodup hI hT
  obtain ⟨hne, h0, -⟩ := hI.1 T hT
  rcases mtz_arc_cases T i j h with ⟨rfl, hl, rfl⟩ | ⟨k, hk, rfl, rfl⟩ | ⟨hl, rfl, rfl⟩ | ⟨rfl, _⟩
  · intro e; exact h0 (by rw [e]; exact List.getElem_mem _)
  · intro e
    have := (hnd.getElem_inj_iff).mp e
    omega
  · intro e; exact h0 (by rw [← e]; exact List.getElem_mem _)
  · exact absurd rfl hne

theorem mtz_arcs_ne {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I) (i : Fin (n+1)) :
    arcCount I i i = 0 := by
  unfold arcCount
  rw [List.count_eq_zero]
  intro h
  unfold arcs at h
  rw [List.mem_flatMap] at h
  obtain ⟨T, hT, hh⟩ := h
  exact mtz_tourArcs_ne hI hT hh rfl

theorem mtz_arc_pos {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I) {i j : Fin (n+1)}
    (hi : i ≠ 0) (hj : j ≠ 0) (h : (i, j) ∈ arcs I) : tourPosition I j = tourPosition I i + 1 := by
  unfold arcs at h
  rw [List.mem_flatMap] at h
  obtain ⟨T, hT, hh⟩ := h
  have hnd := mtz_itin_tour_nodup hI hT
  rcases mtz_arc_cases T i j hh with ⟨rfl, _⟩ | ⟨k, hk, rfl, rfl⟩ | ⟨hl, rfl, rfl⟩ | ⟨rfl, hi0, _⟩
  · exact absurd rfl hi
  · rw [mtz_tourPosition_eq hI hT hi (List.getElem_mem _),
      mtz_tourPosition_eq hI hT hj (List.getElem_mem _), hnd.idxOf_getElem, hnd.idxOf_getElem]
  · exact absurd rfl hj
  · exact absurd hi0 hi



theorem mtz_sum_erase {n : ℕ} (f : Fin (n+1) → ℕ) (j : Fin (n+1)) (h : f j = 0) :
    ∑ i ∈ Finset.univ.filter (· ≠ j), f i = ∑ i, f i := by
  rw [Finset.filter_ne' , ← Finset.add_sum_erase Finset.univ f (Finset.mem_univ j), h, zero_add]

theorem mtz_col_one {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I) {j : Fin (n+1)}
    (hj : j ≠ 0) : ∑ i ∈ Finset.univ.filter (· ≠ j), arcCount I i j = 1 := by
  rw [mtz_sum_erase (fun i => arcCount I i j) j (mtz_arcs_ne hI j), mtz_colsum, if_neg hj,
    add_zero]
  exact List.count_eq_one_of_mem hI.2.1 (hI.2.2 j hj)

theorem mtz_row_one {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I) {i : Fin (n+1)}
    (hi : i ≠ 0) : ∑ j ∈ Finset.univ.filter (· ≠ i), arcCount I i j = 1 := by
  rw [mtz_sum_erase (fun j => arcCount I i j) i (mtz_arcs_ne hI i), mtz_rowsum, if_neg hi,
    add_zero]
  exact List.count_eq_one_of_mem hI.2.1 (hI.2.2 i hi)

theorem mtz_itin_feasible (n p : ℕ) (I : Itinerary n) (hI : IsItinerary n p I) :
    Feasible n p (arcCount I) (fun i => (tourPosition I i : ℝ)) ∧
      ∀ i : Fin (n + 1), i ≠ 0 → 1 ≤ tourPosition I i ∧ tourPosition I i ≤ p := by
  refine ⟨⟨mtz_arcs_ne hI, fun j hj => mtz_col_one hI hj, fun i hi => mtz_row_one hI hi, ?_⟩,
    fun i hi => mtz_tourPosition_bounds hI hi⟩
  intro i j hi hj hij
  have hc1 : arcCount I i j ≤ 1 := by
    have h1 := mtz_col_one hI hj
    have h2 := Finset.single_le_sum (f := fun i => arcCount I i j) (fun _ _ => Nat.zero_le _)
      (s := Finset.univ.filter (· ≠ j)) (a := i) (by simp [hij])
    omega
  have bi := mtz_tourPosition_bounds hI hi
  have bj := mtz_tourPosition_bounds hI hj
  rcases Nat.lt_or_ge (arcCount I i j) 1 with h0 | h1
  · have : arcCount I i j = 0 := by omega
    rw [this]
    have : (tourPosition I i : ℝ) ≤ p := by exact_mod_cast bi.2
    have : (1 : ℝ) ≤ tourPosition I j := by exact_mod_cast bj.1
    push_cast; linarith
  · have h1' : arcCount I i j = 1 := by omega
    have hm : (i, j) ∈ arcs I := by
      have : 0 < arcCount I i j := by omega
      exact List.count_pos_iff.mp this
    have := mtz_arc_pos hI hi hj hm
    rw [h1']
    have : (tourPosition I j : ℝ) = tourPosition I i + 1 := by exact_mod_cast this
    push_cast; linarith

theorem mtz_sum_count_weight {n : ℕ} (d : Fin (n + 1) → Fin (n + 1) → ℝ) (L : List (Fin (n+1) × Fin (n+1))) :
    ∑ i, ∑ j, d i j * (L.count (i, j) : ℝ) = (L.map (fun a => d a.1 a.2)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨a1, a2⟩ := a
    simp only [List.count_cons, List.map_cons, List.sum_cons, ← ih]
    simp [mul_add, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq]
    rw [add_comm]

theorem mtz_objective_eq (n p : ℕ) (d : Fin (n + 1) → Fin (n + 1) → ℝ)
    (I : Itinerary n) (hI : IsItinerary n p I) :
    objective d (arcCount I) = itineraryLength d I := by
  unfold objective itineraryLength
  rw [← mtz_sum_count_weight]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_filter_of_ne
  intro j _ hne
  intro hji
  apply hne
  subst hji
  simp [mtz_arcs_ne hI j]

theorem mtz_tours_mul_p (n p : ℕ) (I : Itinerary n) (hI : IsItinerary n p I) :
    n ≤ I.length * p := by
  have h0 : (0 : Fin (n+1)) ∉ I.flatten := by
    intro h
    rw [List.mem_flatten] at h
    obtain ⟨T, hT, hh⟩ := h
    exact (hI.1 T hT).2.1 hh
  have hts : I.flatten.toFinset = Finset.univ.erase 0 := by
    ext c
    simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h; rintro rfl; exact h0 h
    · intro h; exact hI.2.2 c h
  have hlen : I.flatten.length = n := by
    rw [← List.toFinset_card_of_nodup hI.2.1, hts]
    simp
  have key : I.flatten.length ≤ I.length * p := by
    rw [List.length_flatten]
    have := List.sum_le_card_nsmul (I.map List.length) p (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨T, hT, rfl⟩ := hx
      exact (hI.1 T hT).2.2)
    simpa using this
  omega


end MillerTuckerZemlin.Formulation

open MillerTuckerZemlin.Formulation


theorem solution (n p : ℕ) (I : Itinerary n) (hI : IsItinerary n p I) :
    Feasible n p (arcCount I) (fun i => (tourPosition I i : ℝ)) ∧
      ∀ i : Fin (n + 1), i ≠ 0 → 1 ≤ tourPosition I i ∧ tourPosition I i ≤ p := by
  exact mtz_itin_feasible n p I hI
