-- Prove2me | solution 1 for MillerTuckerZemlin.Formulation.mtz_formulation_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:05:10.22655+00:00
-- url     : https://prove2.me/submissions/170480f4-d977-410a-8e57-3fea496339e1

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model



namespace MillerTuckerZemlin.Formulation


theorem mtz_x_le_one (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) : ∀ i j : Fin (n + 1), x i j ≤ 1 := by
  obtain ⟨hd, hc, hr, -⟩ := hx
  intro i j
  by_cases hij : i = j
  · subst hij; simp [hd]
  by_cases hj : j = 0
  · subst hj
    have hi : i ≠ 0 := hij
    have h1 := hr i hi
    have h2 := Finset.single_le_sum (f := fun j => x i j) (fun _ _ => Nat.zero_le _)
      (s := Finset.univ.filter (· ≠ i)) (a := 0) (by simp [Finset.mem_filter, Ne.symm hij])
    omega
  · have h1 := hc j hj
    have h2 := Finset.single_le_sum (f := fun i => x i j) (fun _ _ => Nat.zero_le _)
      (s := Finset.univ.filter (· ≠ j)) (a := i) (by simp [Finset.mem_filter, hij])
    omega

theorem mtz_step (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (i j : Fin (n + 1)) (hi : i ≠ 0) (hj : j ≠ 0) (h : x i j = 1) :
    u i - u j ≤ -1 := by
  have hij : i ≠ j := by
    rintro rfl
    have := hx.1 i; omega
  have := hx.2.2.2 i j hi hj hij
  rw [h] at this
  push_cast at this
  linarith

theorem mtz_path (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (m : ℕ) (r : Fin (m + 1) → Fin (n + 1))
    (hr : ∀ k, r k ≠ 0) (hpath : ∀ k : Fin m, x (r k.castSucc) (r k.succ) = 1) :
    u (r 0) - u (r (Fin.last m)) ≤ -(m : ℝ) := by
  have key : ∀ k : ℕ, (hk : k ≤ m) → u (r 0) - u (r ⟨k, by omega⟩) ≤ -(k : ℝ) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := mtz_step n p x u hx (r ⟨k, by omega⟩) (r ⟨k+1, by omega⟩) (hr _) (hr _)
        (hpath ⟨k, by omega⟩)
      push_cast
      linarith
  have := key m le_rfl
  have e : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
  rw [e] at this
  exact this

theorem mtz_no_cycle (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ)
    (u : Fin (n + 1) → ℝ) (hx : Feasible n p x u) (k : ℕ) (r : Fin (k + 1) → Fin (n + 1))
    (hr : ∀ i, r i ≠ 0) : ¬ ∀ i : Fin (k + 1), x (r i) (r (i + 1)) = 1 := by
  intro h
  have h1 := mtz_path n p x u hx k r hr (fun i => by
    have := h i.castSucc
    rwa [Fin.coeSucc_eq_succ] at this)
  have h2 := mtz_step n p x u hx (r (Fin.last k)) (r 0) (hr _) (hr _) (by
    have := h (Fin.last k)
    rwa [Fin.last_add_one] at this)
  have : (0:ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem mtz_col_unique (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (j i i' : Fin (n + 1)) (hj : j ≠ 0) (h : x i j = 1) (h' : x i' j = 1) :
    i = i' := by
  by_contra hne
  have hc := hx.2.1 j hj
  have hi : i ≠ j := by rintro rfl; have := hx.1 i; omega
  have hi' : i' ≠ j := by rintro rfl; have := hx.1 i'; omega
  have : x i j + x i' j ≤ ∑ a ∈ Finset.univ.filter (· ≠ j), x a j := by
    rw [← Finset.sum_pair (f := fun a => x a j) hne]
    apply Finset.sum_le_sum_of_subset
    intro a ha
    simp at ha
    simp
    rcases ha with rfl | rfl <;> assumption
  omega

theorem mtz_row_unique (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (i j j' : Fin (n + 1)) (hi : i ≠ 0) (h : x i j = 1) (h' : x i j' = 1) :
    j = j' := by
  by_contra hne
  have hc := hx.2.2.1 i hi
  have hj : j ≠ i := by rintro rfl; have := hx.1 j; omega
  have hj' : j' ≠ i := by rintro rfl; have := hx.1 j'; omega
  have : x i j + x i j' ≤ ∑ a ∈ Finset.univ.filter (· ≠ i), x i a := by
    rw [← Finset.sum_pair (f := fun a => x i a) hne]
    apply Finset.sum_le_sum_of_subset
    intro a ha
    simp at ha
    simp
    rcases ha with rfl | rfl <;> assumption
  omega

theorem mtz_no_long (n p : ℕ) (hp : 1 ≤ p) (x : Fin (n + 1) → Fin (n + 1) → ℕ)
    (u : Fin (n + 1) → ℝ) (hx : Feasible n p x u) (r : Fin (p + 1) → Fin (n + 1))
    (hr : ∀ k, r k ≠ 0) (h0 : x 0 (r 0) = 1) :
    ¬ ∀ k : Fin p, x (r k.castSucc) (r k.succ) = 1 := by
  intro h
  have h1 := mtz_path n p x u hx p r hr h
  have hne : r (Fin.last p) ≠ r 0 := by
    intro e
    rw [e] at h1
    have : (1:ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hz : x (r (Fin.last p)) (r 0) = 0 := by
    by_contra hh
    have h1' := mtz_x_le_one n p x u hx (r (Fin.last p)) (r 0)
    have : x (r (Fin.last p)) (r 0) = 1 := by omega
    have := mtz_col_unique n p x u hx (r 0) _ _ (hr 0) this h0
    exact hr _ (by simpa using this)
  have h2 := hx.2.2.2 (r (Fin.last p)) (r 0) (hr _) (hr _) hne
  rw [hz] at h2
  have : (1:ℝ) ≤ p := by exact_mod_cast hp
  simp at h2
  linarith



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



theorem mtz_walk_u {n p : ℕ} {x : Fin (n + 1) → Fin (n + 1) → ℕ} {u : Fin (n + 1) → ℝ}
    (hx : Feasible n p x u) (s : Fin (n+1) → Fin (n+1)) (hs : ∀ i, i ≠ 0 → x i (s i) = 1)
    (j : Fin (n+1)) (a m : ℕ) (h : ∀ k ≤ m, s^[a+k] j ≠ 0) :
    u (s^[a] j) - u (s^[a+m] j) ≤ -(m : ℝ) := by
  have := mtz_path n p x u hx m (fun k => s^[a + (k : ℕ)] j) (fun k => h k (by omega))
    (fun k => by
      have e : s^[a + ((k.succ : Fin (m+1)) : ℕ)] j = s (s^[a + ((k.castSucc : Fin (m+1)) : ℕ)] j) := by
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [← Function.iterate_succ_apply' s (a + k) j]
        rfl
      beta_reduce
      rw [e]
      exact hs _ (h k (by omega)))
  simpa using this

theorem mtz_exists_L {n p : ℕ} (hp : 1 ≤ p) {x : Fin (n + 1) → Fin (n + 1) → ℕ} {u : Fin (n + 1) → ℝ}
    (hx : Feasible n p x u) (s : Fin (n+1) → Fin (n+1)) (hs : ∀ i, i ≠ 0 → x i (s i) = 1)
    (j : Fin (n+1)) (hj : x 0 j = 1) : ∃ k, s^[k] j = 0 ∧ k ≤ p := by
  by_contra hcon
  push_neg at hcon
  have hne : ∀ k ≤ p, s^[k] j ≠ 0 := fun k hk h => by have := hcon k h; omega
  have hj0 : j ≠ 0 := by rintro rfl; have := hx.1 0; omega
  apply mtz_no_long n p hp x u hx (fun k => s^[(k : ℕ)] j)
    (fun k => hne _ (by have := k.2; omega)) (by simpa using hj)
  intro k
  have e : s^[((k.succ : Fin (p+1)) : ℕ)] j = s (s^[((k.castSucc : Fin (p+1)) : ℕ)] j) := by
    simp only [Fin.val_succ, Fin.val_castSucc]
    rw [Function.iterate_succ_apply']
  beta_reduce
  rw [e]
  exact hs _ (hne _ (by simp))

noncomputable def mtzL {n : ℕ} (s : Fin (n+1) → Fin (n+1)) (j : Fin (n+1)) : ℕ := by
  classical
  exact if h : ∃ k, s^[k] j = 0 then Nat.find h else 0

theorem mtz_Lspec {n p : ℕ} (s : Fin (n+1) → Fin (n+1)) (j : Fin (n+1)) (hj0 : j ≠ 0)
    (hex : ∃ k, s^[k] j = 0 ∧ k ≤ p) :
    s^[mtzL s j] j = 0 ∧ (∀ k < mtzL s j, s^[k] j ≠ 0) ∧ mtzL s j ≤ p ∧ 0 < mtzL s j := by
  classical
  have h : ∃ k, s^[k] j = 0 := by obtain ⟨k, hk, _⟩ := hex; exact ⟨k, hk⟩
  have e : mtzL s j = Nat.find h := by unfold mtzL; rw [dif_pos h]
  rw [e]
  refine ⟨Nat.find_spec h, fun k hk => Nat.find_min h hk, ?_, ?_⟩
  · obtain ⟨k, hk, hkp⟩ := hex
    exact le_trans (Nat.find_min' h hk) hkp
  · rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
    · exfalso; have := Nat.find_spec h; rw [h0] at this; simp at this; exact hj0 this
    · exact h0

noncomputable def mtzT {n : ℕ} (s : Fin (n+1) → Fin (n+1)) (j : Fin (n+1)) : List (Fin (n+1)) :=
  (List.range (mtzL s j)).map (fun k => s^[k] j)

theorem mtz_T_nodup {n p : ℕ} {x : Fin (n + 1) → Fin (n + 1) → ℕ} {u : Fin (n + 1) → ℝ}
    (hx : Feasible n p x u) (s : Fin (n+1) → Fin (n+1)) (hs : ∀ i, i ≠ 0 → x i (s i) = 1)
    (j : Fin (n+1)) (hj0 : j ≠ 0) (hL : ∀ k < mtzL s j, s^[k] j ≠ 0) : (mtzT s j).Nodup := by
  unfold mtzT
  apply List.Nodup.map_on _ (List.nodup_range)
  intro a ha b hb hab
  rw [List.mem_range] at ha hb
  by_contra hne
  wlog hlt : a < b generalizing a b
  · exact this b hb a ha hab.symm (Ne.symm hne) (by omega)
  have := mtz_walk_u hx s hs j a (b - a) (fun k hk => hL _ (by omega))
  have e : a + (b - a) = b := by omega
  rw [e, hab] at this
  have : ((b - a : ℕ) : ℝ) ≥ 1 := by exact_mod_cast (by omega : b - a ≥ 1)
  linarith



theorem mtz_disj {n p : ℕ} {x : Fin (n + 1) → Fin (n + 1) → ℕ} {u : Fin (n + 1) → ℝ}
    (hx : Feasible n p x u) (s : Fin (n+1) → Fin (n+1)) (hs : ∀ i, i ≠ 0 → x i (s i) = 1)
    (hLs : ∀ j, x 0 j = 1 → s^[mtzL s j] j = 0 ∧ (∀ k < mtzL s j, s^[k] j ≠ 0) ∧ mtzL s j ≤ p ∧
      0 < mtzL s j)
    (j j' : Fin (n+1)) (hj : x 0 j = 1) (hj' : x 0 j' = 1) :
    ∀ a b, a < mtzL s j → b < mtzL s j' → s^[a] j = s^[b] j' → j = j' := by
  have hj0 : j ≠ 0 := by rintro rfl; have := hx.1 0; omega
  have hj0' : j' ≠ 0 := by rintro rfl; have := hx.1 0; omega
  intro a
  induction a with
  | zero =>
    intro b _ hb h
    simp only [Function.iterate_zero, id] at h
    cases b with
    | zero => simpa using h
    | succ b' =>
      exfalso
      rw [Function.iterate_succ_apply'] at h
      have hne : s^[b'] j' ≠ 0 := (hLs j' hj').2.1 b' (by omega)
      have h1 := hs _ hne
      rw [← h] at h1
      have := mtz_col_unique n p x u hx j _ _ hj0 h1 hj
      exact hne this
  | succ a' ih =>
    intro b ha hb h
    have hne : s^[a'] j ≠ 0 := (hLs j hj).2.1 a' (by omega)
    have hne2 : s^[a'+1] j ≠ 0 := (hLs j hj).2.1 (a'+1) ha
    have h1 := hs _ hne
    rw [← Function.iterate_succ_apply' s a' j] at h1
    cases b with
    | zero =>
      exfalso
      simp only [Function.iterate_zero, id] at h
      rw [h] at h1
      have := mtz_col_unique n p x u hx j' _ _ hj0' h1 hj'
      exact hne this
    | succ b' =>
      have hne' : s^[b'] j' ≠ 0 := (hLs j' hj').2.1 b' (by omega)
      have h1' := hs _ hne'
      rw [← Function.iterate_succ_apply' s b' j'] at h1'
      rw [← h] at h1'
      have := mtz_col_unique n p x u hx _ _ _ hne2 h1 h1'
      exact ih b' (by omega) (by omega) this

theorem mtz_cover {n p : ℕ} {x : Fin (n + 1) → Fin (n + 1) → ℕ} {u : Fin (n + 1) → ℝ}
    (hx : Feasible n p x u) (s : Fin (n+1) → Fin (n+1)) (hs : ∀ i, i ≠ 0 → x i (s i) = 1)
    (hLs : ∀ j, x 0 j = 1 → s^[mtzL s j] j = 0 ∧ (∀ k < mtzL s j, s^[k] j ≠ 0) ∧ mtzL s j ≤ p ∧
      0 < mtzL s j) :
    ∀ c, c ≠ 0 → ∃ j, x 0 j = 1 ∧ ∃ k, k < mtzL s j ∧ s^[k] j = c := by
  classical
  have key : ∀ N, ∀ c, c ≠ 0 → (Finset.univ.filter (fun c' => u c' < u c)).card = N →
      ∃ j, x 0 j = 1 ∧ ∃ k, k < mtzL s j ∧ s^[k] j = c := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro c hc hN
      -- predecessor
      have hcol := hx.2.1 c hc
      have hex : ∃ i, x i c = 1 := by
        by_contra hno
        push_neg at hno
        have : ∑ i ∈ Finset.univ.filter (· ≠ c), x i c = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          have := mtz_x_le_one n p x u hx i c
          have := hno i
          omega
        omega
      obtain ⟨i, hi⟩ := hex
      by_cases hi0 : i = 0
      · subst hi0
        have hLc := hLs c hi
        exact ⟨c, hi, 0, hLc.2.2.2, by simp⟩
      · have hstep := mtz_step n p x u hx i c hi0 hc hi
        have hlt : u i < u c := by linarith
        have hsub : Finset.univ.filter (fun c' => u c' < u i) ⊂
            Finset.univ.filter (fun c' => u c' < u c) := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨i, by simp [hlt], by simp⟩
          · intro c' hc'
            simp at hc' ⊢
            linarith
        have hcard := Finset.card_lt_card hsub
        obtain ⟨j, hj, k, hk, hki⟩ := ih _ (by omega) i hi0 rfl
        refine ⟨j, hj, k + 1, ?_, ?_⟩
        · by_contra hnot
          have : k + 1 = mtzL s j := by omega
          have h0 := (hLs j hj).1
          rw [← this] at h0
          have e : s^[k+1] j = c := by
            rw [Function.iterate_succ_apply', hki]
            exact (mtz_row_unique n p x u hx i _ _ hi0 (hs i hi0) hi)
          rw [e] at h0
          exact hc h0
        · rw [Function.iterate_succ_apply', hki]
          exact (mtz_row_unique n p x u hx i _ _ hi0 (hs i hi0) hi)
  intro c hc
  exact key _ c hc rfl



theorem mtz_T_len {n : ℕ} (s : Fin (n+1) → Fin (n+1)) (j : Fin (n+1)) :
    (mtzT s j).length = mtzL s j := by simp [mtzT]

theorem mtz_T_get {n : ℕ} (s : Fin (n+1) → Fin (n+1)) (j : Fin (n+1)) (k : ℕ)
    (h : k < (mtzT s j).length) : (mtzT s j)[k] = s^[k] j := by simp [mtzT]

theorem mtz_construct (n p : ℕ) (hp : 1 ≤ p) (x : Fin (n + 1) → Fin (n + 1) → ℕ)
    (u : Fin (n + 1) → ℝ) (hx : Feasible n p x u) :
    ∃ I : Itinerary n, IsItinerary n p I ∧ x = arcCount I := by
  classical
  have hex : ∀ i : Fin (n+1), i ≠ 0 → ∃ j, x i j = 1 := by
    intro i hi
    by_contra hno
    push_neg at hno
    have hrow := hx.2.2.1 i hi
    have : ∑ j ∈ Finset.univ.filter (· ≠ i), x i j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have := mtz_x_le_one n p x u hx i j
      have := hno j
      omega
    omega
  choose! s hs using hex
  have hLs : ∀ j, x 0 j = 1 → s^[mtzL s j] j = 0 ∧ (∀ k < mtzL s j, s^[k] j ≠ 0) ∧
      mtzL s j ≤ p ∧ 0 < mtzL s j := by
    intro j hj
    have hj0 : j ≠ 0 := by rintro rfl; have := hx.1 0; omega
    exact mtz_Lspec s j hj0 (mtz_exists_L hp hx s hs j hj)
  let S : Finset (Fin (n+1)) := Finset.univ.filter (fun j => x 0 j = 1)
  have hS : ∀ j, j ∈ S ↔ x 0 j = 1 := by intro j; simp [S]
  let I : Itinerary n := S.toList.map (mtzT s)
  have hmemI : ∀ T, T ∈ I ↔ ∃ j, x 0 j = 1 ∧ mtzT s j = T := by
    intro T
    simp only [I, List.mem_map, Finset.mem_toList, hS]
  have hI : IsItinerary n p I := by
    refine ⟨?_, ?_, ?_⟩
    · intro T hT
      obtain ⟨j, hj, rfl⟩ := (hmemI T).mp hT
      obtain ⟨-, h2, h3, h4⟩ := hLs j hj
      refine ⟨?_, ?_, ?_⟩
      · intro h
        have := mtz_T_len s j
        rw [h] at this
        simp at this
        omega
      · intro h
        simp only [mtzT, List.mem_map, List.mem_range] at h
        obtain ⟨k, hk, hk0⟩ := h
        exact h2 k hk hk0
      · rw [mtz_T_len]; exact h3
    · rw [List.nodup_flatten]
      refine ⟨?_, ?_⟩
      · intro T hT
        obtain ⟨j, hj, rfl⟩ := (hmemI T).mp hT
        have hj0 : j ≠ 0 := by rintro rfl; have := hx.1 0; omega
        exact mtz_T_nodup hx s hs j hj0 (hLs j hj).2.1
      · simp only [I]
        rw [List.pairwise_map]
        apply List.Pairwise.imp_of_mem _ (Finset.nodup_toList S)
        intro j j' hj hj' hne
        rw [Finset.mem_toList, hS] at hj hj'
        intro c hc hc'
        simp only [mtzT, List.mem_map, List.mem_range] at hc hc'
        obtain ⟨a, ha, rfl⟩ := hc
        obtain ⟨b, hb, hab⟩ := hc'
        exact hne (mtz_disj hx s hs hLs j j' hj hj' a b ha hb hab.symm)
    · intro c hc
      obtain ⟨j, hj, k, hk, hkc⟩ := mtz_cover hx s hs hLs c hc
      rw [List.mem_flatten]
      refine ⟨mtzT s j, (hmemI _).mpr ⟨j, hj, rfl⟩, ?_⟩
      simp only [mtzT, List.mem_map, List.mem_range]
      exact ⟨k, hk, hkc⟩
  refine ⟨I, hI, ?_⟩
  -- arcs coverage
  have harc : ∀ i j, x i j = 1 → (i, j) ∈ arcs I := by
    intro i j hij
    unfold arcs
    rw [List.mem_flatMap]
    by_cases hi0 : i = 0
    · subst hi0
      have hLj := hLs j hij
      refine ⟨mtzT s j, (hmemI _).mpr ⟨j, hij, rfl⟩, ?_⟩
      have hl : 0 < (mtzT s j).length := by rw [mtz_T_len]; exact hLj.2.2.2
      have := mtz_arc_mem_first (mtzT s j) hl
      rw [mtz_T_get] at this
      simpa using this
    · obtain ⟨j', hj', k, hk, hki⟩ := mtz_cover hx s hs hLs i hi0
      refine ⟨mtzT s j', (hmemI _).mpr ⟨j', hj', rfl⟩, ?_⟩
      have hjs : j = s i := mtz_row_unique n p x u hx i _ _ hi0 hij (hs i hi0)
      have hnext : s^[k+1] j' = j := by
        rw [Function.iterate_succ_apply', hki, hjs]
      have hlen := mtz_T_len s j'
      by_cases hk1 : k + 1 < mtzL s j'
      · have := mtz_arc_mem_mid (mtzT s j') k (by omega)
        rw [mtz_T_get, mtz_T_get] at this
        rw [hki, hnext] at this
        exact this
      · have e : k + 1 = mtzL s j' := by omega
        have hz : j = 0 := by
          rw [← hnext, e]; exact (hLs j' hj').1
        have := mtz_arc_mem_last (mtzT s j') (by omega)
        rw [mtz_T_get] at this
        have e2 : (mtzT s j').length - 1 = k := by omega
        rw [e2, hki] at this
        rw [hz]
        exact this
  have hle : ∀ i j, x i j ≤ arcCount I i j := by
    intro i j
    have h1 := mtz_x_le_one n p x u hx i j
    rcases Nat.eq_zero_or_pos (x i j) with h | h
    · omega
    · have : x i j = 1 := by omega
      have : 0 < arcCount I i j := List.count_pos_iff.mpr (harc i j this)
      omega
  funext i j
  by_cases hij : i = j
  · subst hij; rw [hx.1, mtz_arcs_ne hI]
  by_cases hi0 : i = 0
  · subst hi0
    have hj0 : j ≠ 0 := fun h => hij h.symm
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ.filter (· ≠ j))
      (f := fun a => x a j) (g := fun a => arcCount I a j) (fun a _ => hle a j)).mp
      (by rw [hx.2.1 j hj0, mtz_col_one hI hj0]) 0 (by simp [hij])
    exact this
  · have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ.filter (· ≠ i))
      (f := fun a => x i a) (g := fun a => arcCount I i a) (fun a _ => hle i a)).mp
      (by rw [hx.2.2.1 i hi0, mtz_row_one hI hi0]) j (by simp [Ne.symm hij])
    exact this



theorem mtz_col_zero {n p : ℕ} {I : Itinerary n} (hI : IsItinerary n p I) :
    ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))), arcCount I i 0 = I.length := by
  rw [mtz_sum_erase (fun i => arcCount I i 0) 0 (mtz_arcs_ne hI 0), mtz_colsum, if_pos rfl]
  have h0 : (0 : Fin (n+1)) ∉ I.flatten := by
    intro h
    rw [List.mem_flatten] at h
    obtain ⟨T, hT, hh⟩ := h
    exact (hI.1 T hT).2.1 hh
  rw [List.count_eq_zero_of_not_mem h0, zero_add]

theorem mtz_goal (n p : ℕ) (hp : 1 ≤ p) :
    (∀ (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ), Feasible n p x u →
        ∃ I : Itinerary n, IsItinerary n p I ∧ x = arcCount I ∧
          ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))), x i 0 = I.length) ∧
    (∀ I : Itinerary n, IsItinerary n p I →
        (∃ u : Fin (n + 1) → ℕ, Feasible n p (arcCount I) (fun i => (u i : ℝ))) ∧
          ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))), arcCount I i 0 = I.length) ∧
    (∀ (d : Fin (n + 1) → Fin (n + 1) → ℝ) (I : Itinerary n), IsItinerary n p I →
        objective d (arcCount I) = itineraryLength d I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x u hF
    obtain ⟨I, hI, hxe⟩ := mtz_construct n p hp x u hF
    refine ⟨I, hI, hxe, ?_⟩
    subst hxe
    exact mtz_col_zero hI
  · intro I hI
    exact ⟨⟨tourPosition I, (mtz_itin_feasible n p I hI).1⟩, mtz_col_zero hI⟩
  · intro d I hI
    exact mtz_objective_eq n p d I hI


end MillerTuckerZemlin.Formulation

open MillerTuckerZemlin.Formulation


theorem solution (n p : ℕ) (hp : 1 ≤ p) :
    (∀ (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ), Feasible n p x u →
        ∃ I : Itinerary n, IsItinerary n p I ∧ x = arcCount I ∧
          ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))), x i 0 = I.length) ∧
    (∀ I : Itinerary n, IsItinerary n p I →
        (∃ u : Fin (n + 1) → ℕ, Feasible n p (arcCount I) (fun i => (u i : ℝ))) ∧
          ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))), arcCount I i 0 = I.length) ∧
    (∀ (d : Fin (n + 1) → Fin (n + 1) → ℝ) (I : Itinerary n), IsItinerary n p I →
        objective d (arcCount I) = itineraryLength d I) := by
  exact mtz_goal n p hp
