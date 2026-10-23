-- Prove2me | solution 1 for HochbaumShmoys.Uniform.lemma_4_traced
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:58:28.54618+00:00
-- url     : https://prove2.me/submissions/ee9e69f3-ace1-4e0c-9da0-824b3ccc74b3

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph

namespace X4HS

open HochbaumShmoys.Uniform Finset

lemma dpos {N : ℕ} (hN : 2 ≤ N) : 0 < (N : ℝ)⁻¹ :=
  inv_pos.2 (by exact_mod_cast (by omega : 0 < N))

lemma dle {N : ℕ} (hN : 2 ≤ N) : (N : ℝ)⁻¹ ≤ 1 / 2 := by
  rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hN)

lemma iv_lt {N : ℕ} (hN : 2 ≤ N) (x : ℝ) (hx0 : 0 < x) :
    ((N : ℝ)⁻¹) ^ (intervalIndex N x + 1) < x := by
  have hδ0 := dpos hN
  have hδ1 : (N : ℝ)⁻¹ < 1 := by linarith [dle hN]
  have hne : {q : ℕ | ((N : ℝ)⁻¹) ^ (q + 1) < x}.Nonempty := by
    obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one hx0 hδ1
    exact ⟨q, lt_of_le_of_lt (pow_le_pow_of_le_one hδ0.le hδ1.le (Nat.le_succ q)) hq⟩
  exact Nat.sInf_mem hne

lemma iv_le {N : ℕ} (x : ℝ) (hx1 : x ≤ 1) :
    x ≤ ((N : ℝ)⁻¹) ^ (intervalIndex N x) := by
  rcases Nat.eq_zero_or_pos (intervalIndex N x) with h | h
  · rw [h, pow_zero]; exact hx1
  · by_contra hc
    push_neg at hc
    have : intervalIndex N x ≤ intervalIndex N x - 1 := Nat.sInf_le (by
      show ((N : ℝ)⁻¹) ^ (intervalIndex N x - 1 + 1) < x
      rwa [Nat.sub_add_cancel h])
    omega

lemma y_gt {N : ℕ} (hN : 2 ≤ N) (x : ℝ) (hx0 : 0 < x) :
    (N : ℝ) < x / ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : 0 < ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) := pow_pos (dpos hN) _
  rw [lt_div_iff₀ hp]
  have : (N : ℝ) * ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) =
      ((N : ℝ)⁻¹) ^ (intervalIndex N x + 1) := by
    rw [pow_succ, mul_comm, mul_assoc, inv_mul_cancel₀ hN0.ne', mul_one]
  rw [this]; exact iv_lt hN x hx0

lemma rd_bound {N : ℕ} (hN : 2 ≤ N) (x : ℝ) (hx0 : 0 < x) :
    x ≤ (1 + (N : ℝ)⁻¹) * roundDown N x := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : 0 < ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) := pow_pos (dpos hN) _
  have hy := y_gt hN x hx0
  set y := x / ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) with hydef
  have hfl : (N : ℝ) ≤ (⌊y⌋ : ℝ) := by
    have : (N : ℤ) ≤ ⌊y⌋ := Int.le_floor.mpr (by exact_mod_cast hy.le)
    exact_mod_cast this
  have h1 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  have h2 : (1 : ℝ) ≤ (N : ℝ)⁻¹ * (⌊y⌋ : ℝ) := by
    rw [inv_mul_eq_div, le_div_iff₀ hN0]; linarith
  have hb : y ≤ (1 + (N : ℝ)⁻¹) * (⌊y⌋ : ℝ) := by nlinarith
  have hx : x = y * ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) := by
    rw [hydef, div_mul_cancel₀ _ hp.ne']
  unfold roundDown
  rw [← hydef]
  calc x = y * ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) := hx
    _ ≤ (1 + (N : ℝ)⁻¹) * (⌊y⌋ : ℝ) * ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) :=
        mul_le_mul_of_nonneg_right hb hp.le
    _ = _ := by rw [mul_assoc]

lemma rd_nonneg {N : ℕ} (hN : 2 ≤ N) (x : ℝ) (hx0 : 0 < x) : 0 ≤ roundDown N x := by
  have hp : 0 < ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) := pow_pos (dpos hN) _
  have hy := y_gt hN x hx0
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  unfold roundDown
  apply mul_nonneg _ hp.le
  have : (0 : ℤ) ≤ ⌊x / ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2)⌋ := Int.floor_nonneg.2 (by linarith)
  exact_mod_cast this

lemma class_eq {N : ℕ} (hN : 2 ≤ N) (x : ℝ) (hx0 : 0 < x) :
    classSize N (intervalIndex N x) (roundClass N x) = roundDown N x := by
  have hy := y_gt hN x hx0
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  unfold classSize roundDown roundClass
  set y := x / ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2)
  have hle : N ≤ ⌊y⌋₊ := Nat.le_floor hy.le
  rw [Nat.cast_sub hle, natCast_floor_eq_intCast_floor (by linarith)]
  ring

lemma class_lt {N : ℕ} (hN : 2 ≤ N) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    roundClass N x < numClasses N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : 0 < ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) := pow_pos (dpos hN) _
  have hfl : ⌊x / ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2)⌋₊ ≤ N ^ 2 := by
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ hp]
    have h1 := iv_le (N := N) x hx1
    have : ((N ^ 2 : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) =
        ((N : ℝ)⁻¹) ^ (intervalIndex N x) := by
      push_cast
      rw [pow_add, ← mul_assoc, mul_comm ((N : ℝ) ^ 2), mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hN0.ne', one_pow, mul_one]
    rw [this]; exact h1
  unfold roundClass numClasses
  have : N ≤ N ^ 2 := by nlinarith
  omega

lemma fiber {n : ℕ} (s : Finset (Fin n)) (g : Fin n → ℕ) (M : ℕ) (hg : ∀ j ∈ s, g j < M)
    (f : ℕ → ℝ) :
    ∑ j ∈ s, f (g j) = ∑ c : Fin M, ((s.filter (fun j => g j = c.val)).card : ℝ) * f c := by
  rw [← Finset.sum_fiberwise_of_maps_to' (t := range M) (fun j hj => mem_range.2 (hg j hj)) f]
  rw [← Fin.sum_univ_eq_sum_range (fun c => ∑ j ∈ s with g j = c, f c) M]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_const, nsmul_eq_mul]

end X4HS

open HochbaumShmoys.Uniform Finset X4HS in
theorem solution (N : ℕ) (hN : 2 ≤ N) (m n : ℕ) (hm : 0 < m) (β : Fin m → ℝ)
    (π : Fin n → ℝ)
    (hβ : Antitone β) (hβ0 : β ⟨0, hm⟩ = 1) (hβpos : ∀ t, 0 < β t)
    (hπ : ∀ j, 0 < π j ∧ π j ≤ 1)
    (σ : Fin n → Fin m) (hσ : IsTracedPacking N β π σ) :
    IsRelaxedFeasible (2 * (N : ℝ)⁻¹ + ((N : ℝ)⁻¹) ^ 2) π β σ := by
  classical
  obtain ⟨pre, fin, hpath, htr⟩ := hσ
  obtain ⟨hc1, hcL, hcM, ρ, hρinj, -, hslack⟩ := htr
  intro t
  have hδ0 := dpos hN
  have hδ1 := dle hN
  set δ : ℝ := (N : ℝ)⁻¹ with hδ
  set k := binInterval N β t with hk
  have hβ1 : β t ≤ 1 := by rw [← hβ0]; exact hβ (show (⟨0, hm⟩ : Fin m) ≤ t from Nat.zero_le _)
  have hβk : δ ^ (k + 1) < β t := iv_lt hN (β t) (hβpos t)
  -- the configuration arc across bin t
  set C := configSize N k (pre t) (afterBin N β pre fin t) with hC
  have hCle : C ≤ β t := by
    have harc : IsConfigArc N k (β t) (pre t) (afterBin N β pre fin t) := by
      unfold afterBin
      by_cases h : t.val + 1 < m
      · rw [dif_pos h]
        by_cases hs : binInterval N β ⟨t.val + 1, h⟩ = binInterval N β t
        · rw [if_pos hs]
          have := hpath.1 t h hs
          exact this.2.2.2
        · rw [if_neg hs]
          have hl : IsLastOfStage N β t := by
            intro h'; exact hs
          exact (hpath.2.1 t hl).2.2.2
      · rw [dif_neg h]
        have hl : IsLastOfStage N β t := fun h' => absurd h' h
        exact (hpath.2.1 t hl).2.2.2
    exact harc.2.2.2.2.1
  -- splitting the bin
  set A := univ.filter (fun j => σ j = t ∧ intervalIndex N (π j) = k) with hA
  set B := univ.filter (fun j => σ j = t ∧ intervalIndex N (π j) = k + 1) with hB
  set S := univ.filter (fun j => σ j = t ∧ k + 2 ≤ intervalIndex N (π j)) with hS
  have hsplit : binLoad π σ t = ∑ j ∈ A, π j + ∑ j ∈ B, π j + ∑ j ∈ S, π j := by
    simp only [binLoad, hA, hB, hS, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hσj : σ j = t
    · have h1 := hc1 j
      rw [hσj] at h1
      rcases (show intervalIndex N (π j) = k ∨ intervalIndex N (π j) = k + 1 ∨
          k + 2 ≤ intervalIndex N (π j) by omega) with h | h | h
      · rw [if_pos hσj, if_pos ⟨hσj, h⟩, if_neg (by omega), if_neg (by omega)]; ring
      · rw [if_pos hσj, if_neg (by omega), if_pos ⟨hσj, h⟩, if_neg (by omega)]; ring
      · rw [if_pos hσj, if_neg (by omega), if_neg (by omega), if_pos ⟨hσj, h⟩]; ring
    · simp [hσj]
  -- large and medium pieces
  have hAB : ∑ j ∈ A, roundDown N (π j) + ∑ j ∈ B, roundDown N (π j) = C := by
    have hA' : ∑ j ∈ A, roundDown N (π j) = ∑ j ∈ A, classSize N k (roundClass N (π j)) := by
      refine sum_congr rfl fun j hj => ?_
      have := (mem_filter.1 hj).2.2
      rw [← this, class_eq hN _ (hπ j).1]
    have hB' : ∑ j ∈ B, roundDown N (π j) =
        ∑ j ∈ B, classSize N (k + 1) (roundClass N (π j)) := by
      refine sum_congr rfl fun j hj => ?_
      have := (mem_filter.1 hj).2.2
      rw [← this, class_eq hN _ (hπ j).1]
    rw [hA', hB', fiber A (fun j => roundClass N (π j)) (numClasses N)
        (fun j _ => class_lt hN _ (hπ j).1 (hπ j).2) (classSize N k),
      fiber B (fun j => roundClass N (π j)) (numClasses N)
        (fun j _ => class_lt hN _ (hπ j).1 (hπ j).2) (classSize N (k + 1)), hC]
    unfold configSize
    congr 1
    · refine sum_congr rfl fun c _ => ?_
      rw [← hcL t c, hA, filter_filter]
      congr 3
      ext j; simp [and_assoc, hk]
    · refine sum_congr rfl fun c _ => ?_
      rw [← hcM t c, hB, filter_filter]
      congr 3
      ext j; simp [and_assoc, hk]
  have hπA : ∑ j ∈ A, π j ≤ (1 + δ) * ∑ j ∈ A, roundDown N (π j) := by
    rw [mul_sum]; exact sum_le_sum fun j _ => rd_bound hN _ (hπ j).1
  have hπB : ∑ j ∈ B, π j ≤ (1 + δ) * ∑ j ∈ B, roundDown N (π j) := by
    rw [mul_sum]; exact sum_le_sum fun j _ => rd_bound hN _ (hπ j).1
  have hLM : ∑ j ∈ A, π j + ∑ j ∈ B, π j ≤ (1 + δ) * C := by
    rw [← hAB]; linarith
  rw [hsplit]
  have hgoal : (1 + δ) * β t ≤ (1 + (2 * δ + δ ^ 2)) * β t := by
    nlinarith [hβpos t]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, sum_empty, add_zero]
    have : (1 + δ) * C ≤ (1 + δ) * β t := mul_le_mul_of_nonneg_left hCle (by linarith)
    linarith
  · obtain ⟨js, hjs, hmax⟩ := exists_max_image S ρ hSne
    have hjs' := mem_filter.1 hjs
    have hsmall : IsSmallIn N β π σ js := by
      show binInterval N β (σ js) + 2 ≤ intervalIndex N (π js)
      rw [hjs'.2.1]; exact hjs'.2.2
    have hsl := hslack js hsmall
    have hsub : S.erase js ⊆ univ.filter (fun j' => IsSmallIn N β π σ j' ∧ σ j' = σ js ∧
        ρ j' < ρ js) := by
      intro j hj
      obtain ⟨hne, hjS⟩ := mem_erase.1 hj
      have hj' := mem_filter.1 hjS
      refine mem_filter.2 ⟨mem_univ _, ?_, ?_, ?_⟩
      · show binInterval N β (σ j) + 2 ≤ intervalIndex N (π j)
        rw [hj'.2.1]; exact hj'.2.2
      · rw [hj'.2.1, hjs'.2.1]
      · exact lt_of_le_of_ne (hmax j hjS) (fun h => hne (hρinj h))
    have hrest : ∑ j ∈ S.erase js, roundDown N (π j) < usableSlack N β pre fin t := by
      refine lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg hsub
        (fun j _ _ => rd_nonneg hN _ (hπ j).1)) ?_
      rw [← hjs'.2.1]; exact hsl
    have hus : usableSlack N β pre fin t < (β t - C) + δ ^ (k + 4) := by
      unfold usableSlack
      rw [← hk, ← hC, ← hδ]
      have hp : 0 < δ ^ (k + 4) := pow_pos hδ0 _
      have := Int.ceil_lt_add_one ((β t - C) / δ ^ (k + 4))
      calc (⌈(β t - C) / δ ^ (k + 4)⌉ : ℝ) * δ ^ (k + 4)
          < ((β t - C) / δ ^ (k + 4) + 1) * δ ^ (k + 4) := mul_lt_mul_of_pos_right this hp
        _ = (β t - C) + δ ^ (k + 4) := by field_simp
    have hπrest : ∑ j ∈ S.erase js, π j ≤ (1 + δ) * ∑ j ∈ S.erase js, roundDown N (π j) := by
      rw [mul_sum]; exact sum_le_sum fun j _ => rd_bound hN _ (hπ j).1
    have hjsle : π js ≤ δ ^ (k + 2) := by
      calc π js ≤ δ ^ (intervalIndex N (π js)) := iv_le (π js) (hπ js).2
        _ ≤ δ ^ (k + 2) := pow_le_pow_of_le_one hδ0.le (by linarith) hjs'.2.2
    rw [← add_sum_erase S π hjs]
    have hp1 : 0 < δ ^ (k + 1) := pow_pos hδ0 _
    have e2 : δ ^ (k + 2) = δ ^ (k + 1) * δ := by rw [pow_succ]
    have e4 : δ ^ (k + 4) = δ ^ (k + 1) * δ ^ 3 := by rw [← pow_add]
    have hS' : π js + ∑ j ∈ S.erase js, π j ≤ δ ^ (k + 2) + (1 + δ) * ((β t - C) + δ ^ (k + 4)) := by
      have : (1 + δ) * ∑ j ∈ S.erase js, roundDown N (π j) ≤ (1 + δ) * ((β t - C) + δ ^ (k + 4)) :=
        mul_le_mul_of_nonneg_left (hrest.trans hus).le (by linarith)
      linarith
    -- final arithmetic
    have hfin : (1 + δ) * C + (δ ^ (k + 2) + (1 + δ) * ((β t - C) + δ ^ (k + 4))) ≤
        (1 + (2 * δ + δ ^ 2)) * β t := by
      rw [e2, e4]
      have h3 : δ * (1 + δ) ≤ 1 := by nlinarith
      have h4 : δ ^ (k + 1) * δ ^ 2 * (δ * (1 + δ)) ≤ δ ^ (k + 1) * δ ^ 2 := by
        have : 0 ≤ δ ^ (k + 1) * δ ^ 2 := by positivity
        nlinarith
      have h5 : δ * (1 + δ) * δ ^ (k + 1) ≤ δ * (1 + δ) * β t :=
        mul_le_mul_of_nonneg_left hβk.le (by positivity)
      nlinarith
    linarith
