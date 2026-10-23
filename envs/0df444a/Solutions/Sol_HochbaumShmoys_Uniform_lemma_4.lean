-- Prove2me | solution 1 for HochbaumShmoys.Uniform.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:24:48.472092+00:00
-- url     : https://prove2.me/submissions/b19c1ae5-9929-4395-938e-f49edb093c98

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
theorem X4HS.traced_feasible (N : ℕ) (hN : 2 ≤ N) (m n : ℕ) (hm : 0 < m) (β : Fin m → ℝ)
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

namespace X4HS

open HochbaumShmoys.Uniform Finset

section Path

variable {N m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ)

/-- The four layered-path conditions at index `s`. -/
def GoodAt (pre fin : Fin m → StateVector N n) (s : Fin m) : Prop :=
  (∀ h : s.val + 1 < m, binInterval N β ⟨s.val + 1, h⟩ = binInterval N β s →
      Arc N β π (.pre s (pre s)) (.pre ⟨s.val + 1, h⟩ (pre ⟨s.val + 1, h⟩))) ∧
  (IsLastOfStage N β s → Arc N β π (.pre s (pre s)) (.fin s (fin s))) ∧
  (∀ h : s.val + 1 < m, IsLastOfStage N β s →
      Arc N β π (.fin s (fin s)) (.pre ⟨s.val + 1, h⟩ (pre ⟨s.val + 1, h⟩))) ∧
  (s.val + 1 = m → Arc N β π (.fin s (fin s)) .success)

lemma goodAt_congr {pre fin pre' fin' : Fin m → StateVector N n} (s : Fin m)
    (h0 : pre' s = pre s) (h1 : ∀ h : s.val + 1 < m, pre' ⟨s.val + 1, h⟩ = pre ⟨s.val + 1, h⟩)
    (h2 : fin' s = fin s) :
    GoodAt β π pre' fin' s ↔ GoodAt β π pre fin s := by
  unfold GoodAt
  constructor
  · rintro ⟨a, b, c, d⟩
    refine ⟨fun h e => ?_, fun e => ?_, fun h e => ?_, fun e => ?_⟩
    · have := a h e; rwa [h0, h1 h] at this
    · have := b e; rwa [h0, h2] at this
    · have := c h e; rwa [h2, h1 h] at this
    · have := d e; rwa [h2] at this
  · rintro ⟨a, b, c, d⟩
    refine ⟨fun h e => ?_, fun e => ?_, fun h e => ?_, fun e => ?_⟩
    · rw [h0, h1 h]; exact a h e
    · rw [h0, h2]; exact b e
    · rw [h2, h1 h]; exact c h e
    · rw [h2]; exact d e

/-- Tail property of a node that reaches `success`. -/
def TailOK : Node m N n → Prop
  | .pre t u => ∃ pre fin : Fin m → StateVector N n, pre t = u ∧
      ∀ s : Fin m, t ≤ s → GoodAt β π pre fin s
  | .fin t u => ∃ pre fin : Fin m → StateVector N n, fin t = u ∧
      (∀ h : t.val + 1 < m, IsLastOfStage N β t →
        Arc N β π (.fin t (fin t)) (.pre ⟨t.val + 1, h⟩ (pre ⟨t.val + 1, h⟩))) ∧
      (t.val + 1 = m → Arc N β π (.fin t (fin t)) .success) ∧
      ∀ s : Fin m, t < s → GoodAt β π pre fin s
  | .success => True

lemma tail_of_reach (X : Node m N n)
    (h : Relation.ReflTransGen (Arc N β π) X .success) : TailOK β π X := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => trivial
  | @head a c hac _ ih =>
    cases a with
    | success => trivial
    | pre t u =>
      cases c with
      | success => exact absurd hac (by simp [Arc])
      | pre t' v =>
        obtain ⟨ht', hint, hinit, hcfg⟩ := hac
        obtain ⟨pre, fin, hpv, hgood⟩ := ih
        refine ⟨Function.update pre t u, fin, by simp, fun s hs => ?_⟩
        rcases eq_or_lt_of_le hs with rfl | hlt
        · refine ⟨fun h e => ?_, fun e => ?_, fun h e => ?_, fun e => ?_⟩
          · have : (⟨t.val + 1, h⟩ : Fin m) = t' := Fin.ext ht'.symm
            have hne : (⟨t.val + 1, h⟩ : Fin m) ≠ t := by
              intro h'; have := congrArg Fin.val h'; simp at this
            rw [Function.update_self, Function.update_of_ne hne, this, hpv]
            exact ⟨ht', hint, hinit, hcfg⟩
          · exfalso
            have h1 : t.val + 1 < m := by rw [← ht']; exact t'.2
            exact e h1 (by rw [← hint]; congr 1; exact Fin.ext ht'.symm)
          · exfalso
            exact e h (by rw [← hint]; congr 1; exact Fin.ext ht'.symm)
          · exfalso; have := t'.2; omega
        · have hts : t' ≤ s := by
            show t'.val ≤ s.val; rw [ht']; exact hlt
          rw [goodAt_congr β π s (pre := pre) (fin := fin)]
          · exact hgood s hts
          · exact Function.update_of_ne (ne_of_gt hlt) _ _
          · intro h; apply Function.update_of_ne
            intro h'; have := congrArg Fin.val h'; simp at this
            have : t.val < s.val := hlt; omega
          · rfl
      | fin t' v =>
        obtain ⟨ht', hlast, hinit, hcfg⟩ := hac
        subst ht'
        obtain ⟨pre, fin, hfv, h3, h4, hgood⟩ := ih
        refine ⟨Function.update pre t' u, fin, by simp, fun s hs => ?_⟩
        rcases eq_or_lt_of_le hs with rfl | hlt
        · refine ⟨fun h e => absurd e (hlast h), fun _ => ?_, fun h e => ?_, fun e => ?_⟩
          · rw [Function.update_self, hfv]; exact ⟨rfl, hlast, hinit, hcfg⟩
          · have hne : (⟨t'.val + 1, h⟩ : Fin m) ≠ t' := by
              intro h'; have := congrArg Fin.val h'; simp at this
            rw [Function.update_of_ne hne]; exact h3 h e
          · exact h4 e
        · rw [goodAt_congr β π s (pre := pre) (fin := fin)]
          · exact hgood s hlt
          · exact Function.update_of_ne (ne_of_gt hlt) _ _
          · intro h; apply Function.update_of_ne
            intro h'; have := congrArg Fin.val h'; simp at this
            have : t'.val < s.val := hlt; omega
          · rfl
    | fin t u =>
      cases c with
      | success =>
        obtain ⟨hm, hsome⟩ := hac
        refine ⟨fun _ => u, fun _ => u, rfl, fun h => by omega, fun _ => ⟨hm, hsome⟩,
          fun s hs => ?_⟩
        exfalso; have := s.2; have : t.val < s.val := hs; omega
      | fin _ _ => exact absurd hac (by simp [Arc])
      | pre t' v =>
        obtain ⟨ht', hlast, hupd⟩ := hac
        obtain ⟨pre, fin, hpv, hgood⟩ := ih
        have ht'eq : ∀ h : t.val + 1 < m, (⟨t.val + 1, h⟩ : Fin m) = t' :=
          fun h => Fin.ext ht'.symm
        refine ⟨pre, Function.update fin t u, by simp, fun h _ => ?_, fun e => ?_,
          fun s hs => ?_⟩
        · rw [Function.update_self, ht'eq h, hpv]; exact ⟨ht', hlast, hupd⟩
        · exfalso; have := t'.2; omega
        · have hts : t' ≤ s := by
            show t'.val ≤ s.val; rw [ht']; exact hs
          rw [goodAt_congr β π s (pre := pre) (fin := fin)]
          · exact hgood s hts
          · rfl
          · intro _; rfl
          · exact Function.update_of_ne (ne_of_gt hs) _ _

lemma layered_of_reach (hm : 0 < m)
    (h : Relation.ReflTransGen (Arc N β π) (initialNode N π hm) .success) :
    ∃ pre fin : Fin m → StateVector N n, IsLayeredPath N β π pre fin ∧
      pre ⟨0, hm⟩ = initialState N π := by
  obtain ⟨pre, fin, h0, hg⟩ := tail_of_reach β π _ h
  refine ⟨pre, fin, ⟨fun t h e => (hg t (Nat.zero_le _)).1 h e,
    fun t e => (hg t (Nat.zero_le _)).2.1 e, fun t h e => (hg t (Nat.zero_le _)).2.2.1 h e,
    fun t e => (hg t (Nat.zero_le _)).2.2.2 e⟩, h0⟩

end Path

end X4HS

namespace X4HS

open HochbaumShmoys.Uniform Finset

lemma iv_anti {N : ℕ} (hN : 2 ≤ N) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    intervalIndex N y ≤ intervalIndex N x :=
  Nat.sInf_le (show ((N : ℝ)⁻¹) ^ (intervalIndex N x + 1) < y from
    lt_of_lt_of_le (iv_lt hN x hx) hxy)

lemma iv_one {N : ℕ} (hN : 2 ≤ N) : intervalIndex N 1 = 0 := by
  have : intervalIndex N 1 ≤ 0 := Nat.sInf_le (show ((N : ℝ)⁻¹) ^ (0 + 1) < 1 by
    rw [zero_add, pow_one]; linarith [dle hN])
  omega

section Ledger

variable {N m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) (pre fin : Fin m → StateVector N n)

/-- Number of class-`c` pieces of interval `k'` taken as large/medium pieces by bin `s`. -/
noncomputable def dec (k' : ℕ) (c : Fin (numClasses N)) (s : Fin m) : ℕ :=
  if binInterval N β s = k' then ((pre s).L c : ℕ) - ((afterBin N β pre fin s).L c : ℕ)
  else if binInterval N β s + 1 = k' then
    ((pre s).M c : ℕ) - ((afterBin N β pre fin s).M c : ℕ)
  else 0

noncomputable def taken (k' : ℕ) (c : Fin (numClasses N)) (t : ℕ) : ℕ :=
  ∑ s ∈ univ.filter (fun s : Fin m => s.val < t), dec β pre fin k' c s

noncomputable def lo (k' : ℕ) : ℝ :=
  ∑ c : Fin (numClasses N),
    (((pieceCount N π k' c : ℕ) - taken β pre fin k' c m : ℕ) : ℝ) * classSize N k' c

noncomputable def DD (k : ℕ) : ℝ := ∑ k' ∈ range k, lo β π pre fin k'

noncomputable def US (P : Fin m → Prop) [DecidablePred P] : ℝ :=
  ∑ s ∈ univ.filter P, usableSlack N β pre fin s

def Inv (k t : ℕ) (w : StateVector N n) : Prop :=
  (∀ c, (w.L c : ℕ) + taken β pre fin k c t = pieceCount N π k c) ∧
  (∀ c, (w.M c : ℕ) + taken β pre fin (k + 1) c t = pieceCount N π (k + 1) c) ∧
  (∀ k' c, taken β pre fin k' c t ≤ pieceCount N π k' c) ∧
  ((w.V₁ : ℕ) * ((N : ℝ)⁻¹) ^ (k + 2) + DD β π pre fin k ≤
    US β pre fin (fun s => binInterval N β s + 2 ≤ k)) ∧
  ((w.V₁ : ℕ) * ((N : ℝ)⁻¹) ^ (k + 2) + (w.V₂ : ℕ) * ((N : ℝ)⁻¹) ^ (k + 3) +
    DD β π pre fin k ≤ US β pre fin (fun s => binInterval N β s + 1 ≤ k)) ∧
  ((w.V₁ : ℕ) * ((N : ℝ)⁻¹) ^ (k + 2) + (w.V₂ : ℕ) * ((N : ℝ)⁻¹) ^ (k + 3) +
    (w.V : ℕ) * ((N : ℝ)⁻¹) ^ (k + 4) + DD β π pre fin k ≤
    US β pre fin (fun s => s.val < t)) ∧
  (∀ K < k, DD β π pre fin (K + 1) ≤ US β pre fin (fun s => binInterval N β s + 2 ≤ K))

variable {β π pre fin}

lemma taken_succ (k' : ℕ) (c : Fin (numClasses N)) (t : Fin m) :
    taken β pre fin k' c (t.val + 1) = taken β pre fin k' c t.val + dec β pre fin k' c t := by
  unfold taken
  have : univ.filter (fun s : Fin m => s.val < t.val + 1) =
      insert t (univ.filter (fun s : Fin m => s.val < t.val)) := by
    ext s; simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h; rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h) <;> omega
  rw [this, sum_insert (by simp), add_comm]

lemma taken_zero (k' : ℕ) (c : Fin (numClasses N)) (t : ℕ)
    (h : ∀ s : Fin m, s.val < t → binInterval N β s ≠ k' ∧ binInterval N β s + 1 ≠ k') :
    taken β pre fin k' c t = 0 := by
  unfold taken
  refine sum_eq_zero fun s hs => ?_
  have := h s (mem_filter.1 hs).2
  unfold dec; rw [if_neg this.1, if_neg this.2]

lemma taken_stable (k' : ℕ) (c : Fin (numClasses N)) (t : ℕ) (ht : t ≤ m)
    (h : ∀ s : Fin m, t ≤ s.val → k' < binInterval N β s) :
    taken β pre fin k' c m = taken β pre fin k' c t := by
  unfold taken
  rw [← sum_filter_add_sum_filter_not (univ.filter (fun s : Fin m => s.val < m))
    (fun s : Fin m => s.val < t)]
  rw [sum_eq_zero (s := filter (fun s : Fin m => ¬ s.val < t) _) ?_]
  · rw [add_zero, filter_filter]
    congr 1; ext s; simp only [mem_filter, mem_univ, true_and]; omega
  · intro s hs
    have := h s (by simp only [mem_filter] at hs; omega)
    unfold dec; rw [if_neg (by omega), if_neg (by omega)]

lemma US_mono {P Q : Fin m → Prop} [DecidablePred P] [DecidablePred Q]
    (hus : ∀ s, 0 ≤ usableSlack N β pre fin s) (h : ∀ s, P s → Q s) :
    US β pre fin P ≤ US β pre fin Q := by
  unfold US
  exact sum_le_sum_of_subset_of_nonneg (fun s hs => by
    simp only [mem_filter, mem_univ, true_and] at hs ⊢; exact h s hs)
    (fun s _ _ => hus s)

lemma lo_nonneg (hN : 2 ≤ N) (k' : ℕ) : 0 ≤ lo β π pre fin k' := by
  unfold lo
  refine sum_nonneg fun c _ => mul_nonneg (Nat.cast_nonneg _) ?_
  unfold classSize
  exact mul_nonneg (by positivity) (pow_nonneg (dpos hN).le _)

lemma DD_mono (hN : 2 ≤ N) {a b : ℕ} (h : a ≤ b) : DD β π pre fin a ≤ DD β π pre fin b := by
  unfold DD
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h)
    (fun k _ _ => lo_nonneg hN k)

lemma DD_succ (k : ℕ) : DD β π pre fin (k + 1) = DD β π pre fin k + lo β π pre fin k := by
  unfold DD; rw [sum_range_succ]

end Ledger

end X4HS

namespace X4HS

open HochbaumShmoys.Uniform Finset

section Steps

variable {N m n : ℕ} (hN : 2 ≤ N) {β : Fin m → ℝ} {π : Fin n → ℝ}
  {pre fin : Fin m → StateVector N n}

include hN in
lemma kb_mono (hβ : Antitone β) (hβpos : ∀ t, 0 < β t) {s t : Fin m} (h : s ≤ t) :
    binInterval N β s ≤ binInterval N β t :=
  iv_anti hN (hβpos t) (hβ h)

lemma cap_le (x : ℕ) : (capSlack N n x : ℕ) ≤ x := min_le_left _ _

omit hN in
lemma cfg_arc (hpath : IsLayeredPath N β π pre fin) (t : Fin m) :
    IsConfigArc N (binInterval N β t) (β t) (pre t) (afterBin N β pre fin t) := by
  unfold afterBin
  by_cases h : t.val + 1 < m
  · rw [dif_pos h]
    by_cases hs : binInterval N β ⟨t.val + 1, h⟩ = binInterval N β t
    · rw [if_pos hs]
      exact (hpath.1 t h hs).2.2.2
    · rw [if_neg hs]
      have hl : IsLastOfStage N β t := by
        intro h'; exact hs
      exact (hpath.2.1 t hl).2.2.2
  · rw [dif_neg h]
    have hl : IsLastOfStage N β t := fun h' => absurd h' h
    exact (hpath.2.1 t hl).2.2.2

include hN in
lemma usable_eq (hpath : IsLayeredPath N β π pre fin) (t : Fin m) :
    usableSlack N β pre fin t =
      (⌈(β t - configSize N (binInterval N β t) (pre t) (afterBin N β pre fin t)) /
        ((N : ℝ)⁻¹) ^ (binInterval N β t + 4)⌉₊ : ℝ) *
        ((N : ℝ)⁻¹) ^ (binInterval N β t + 4) := by
  have h := (cfg_arc hpath t).2.2.2.2.1
  have hp : 0 < ((N : ℝ)⁻¹) ^ (binInterval N β t + 4) := pow_pos (dpos hN) _
  unfold usableSlack
  rw [natCast_ceil_eq_intCast_ceil (div_nonneg (by linarith) hp.le)]

include hN in
lemma usable_nonneg (hpath : IsLayeredPath N β π pre fin) (t : Fin m) :
    0 ≤ usableSlack N β pre fin t := by
  rw [usable_eq hN hpath]
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (dpos hN).le _)

lemma US_lt_succ (t : Fin m) :
    US β pre fin (fun s => s.val < t.val + 1) =
      US β pre fin (fun s => s.val < t.val) + usableSlack N β pre fin t := by
  unfold US
  have : univ.filter (fun s : Fin m => s.val < t.val + 1) =
      insert t (univ.filter (fun s : Fin m => s.val < t.val)) := by
    ext s; simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h; rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h) <;> omega
  rw [this, sum_insert (by simp), add_comm]

include hN in
lemma step_cfg (hpath : IsLayeredPath N β π pre fin) (t : Fin m)
    (hI : Inv β π pre fin (binInterval N β t) t.val (pre t)) :
    Inv β π pre fin (binInterval N β t) (t.val + 1) (afterBin N β pre fin t) := by
  obtain ⟨hL, hM, hV₁, hV₂, hcfg, hV⟩ := cfg_arc hpath t
  obtain ⟨ia, ib, ic, id, ie, iff, ig⟩ := hI
  set k := binInterval N β t with hk
  refine ⟨fun c => ?_, fun c => ?_, fun k' c => ?_, ?_, ?_, ?_, ig⟩
  · rw [taken_succ]
    have : dec β pre fin k c t = ((pre t).L c : ℕ) - ((afterBin N β pre fin t).L c : ℕ) := by
      unfold dec; rw [if_pos hk.symm]
    rw [this]; have := ia c; have := hL c; omega
  · rw [taken_succ]
    have : dec β pre fin (k + 1) c t =
        ((pre t).M c : ℕ) - ((afterBin N β pre fin t).M c : ℕ) := by
      unfold dec; split_ifs <;> omega
    rw [this]; have := ib c; have := hM c; omega
  · rw [taken_succ]
    unfold dec
    split_ifs with h1 h2
    · have := ia c; have := hL c; rw [← h1, ← hk]; omega
    · have := ib c; have := hM c; rw [← h2, ← hk]; omega
    · have := ic k' c; omega
  · rw [hV₁]; exact id
  · rw [hV₁, hV₂]; exact ie
  · rw [hV₁, hV₂, US_lt_succ, usable_eq hN hpath t, ← hk]
    have hp : 0 ≤ ((N : ℝ)⁻¹) ^ (k + 4) := pow_nonneg (dpos hN).le _
    have h1 : ((afterBin N β pre fin t).V : ℕ) ≤ ((pre t).V : ℕ) +
        ⌈(β t - configSize N k (pre t) (afterBin N β pre fin t)) /
          ((N : ℝ)⁻¹) ^ (k + 4)⌉₊ := by
      rw [hV]; exact cap_le _
    have h2 : (((afterBin N β pre fin t).V : ℕ) : ℝ) ≤ ((pre t).V : ℕ) +
        (⌈(β t - configSize N k (pre t) (afterBin N β pre fin t)) /
          ((N : ℝ)⁻¹) ^ (k + 4)⌉₊ : ℝ) := by exact_mod_cast h1
    nlinarith

end Steps

end X4HS

namespace X4HS

open HochbaumShmoys.Uniform Finset

lemma fl_le {W e : ℝ} (he : 0 < e) (hW : 0 ≤ W) : (⌊W / e⌋₊ : ℝ) * e ≤ W := by
  have := Nat.floor_le (div_nonneg hW he.le)
  calc (⌊W / e⌋₊ : ℝ) * e ≤ W / e * e := mul_le_mul_of_nonneg_right this he.le
    _ = W := div_mul_cancel₀ W he.ne'

lemma capR {N n : ℕ} (x : ℕ) : ((capSlack N n x : ℕ) : ℝ) ≤ x := by
  exact_mod_cast cap_le x

section Upd

variable {N m n : ℕ} (hN : 2 ≤ N) {β : Fin m → ℝ} {π : Fin n → ℝ}
  {pre fin : Fin m → StateVector N n}

lemma pc_eq (k' : ℕ) (c : Fin (numClasses N)) :
    ((pieceCount N π k' c : ℕ)) =
      ((univ.filter (fun j => intervalIndex N (π j) = k')).filter
        (fun j => roundClass N (π j) = c.val)).card := by
  unfold pieceCount; simp only [filter_filter]

include hN in
lemma pieces_sum (hπ : ∀ j, 0 < π j ∧ π j ≤ 1) (k' : ℕ) :
    ∑ c : Fin (numClasses N), ((pieceCount N π k' c : ℕ) : ℝ) * classSize N k' c =
      ∑ j ∈ univ.filter (fun j => intervalIndex N (π j) = k'), roundDown N (π j) := by
  rw [show ∑ j ∈ univ.filter (fun j => intervalIndex N (π j) = k'), roundDown N (π j) =
      ∑ j ∈ univ.filter (fun j => intervalIndex N (π j) = k'),
        classSize N k' (roundClass N (π j)) from sum_congr rfl fun j hj => by
          rw [← (mem_filter.1 hj).2, class_eq hN _ (hπ j).1]]
  rw [fiber _ (fun j => roundClass N (π j)) (numClasses N)
    (fun j _ => class_lt hN _ (hπ j).1 (hπ j).2) (classSize N k')]
  refine sum_congr rfl fun c _ => ?_
  rw [pc_eq]

include hN in
lemma lo_free (hπ : ∀ j, 0 < π j ∧ π j ≤ 1) (k' : ℕ)
    (h : ∀ c, taken β pre fin k' c m = 0) :
    lo β π pre fin k' =
      ∑ j ∈ univ.filter (fun j => intervalIndex N (π j) = k'), roundDown N (π j) := by
  rw [← pieces_sum hN hπ]
  unfold lo
  refine sum_congr rfl fun c _ => ?_
  rw [h c, Nat.sub_zero]

lemma lo_of (k' t : ℕ) (w : StateVector N n) (ht : t ≤ m)
    (hw : ∀ c, (w.L c : ℕ) + taken β pre fin k' c t = pieceCount N π k' c)
    (hhigh : ∀ s : Fin m, t ≤ s.val → k' < binInterval N β s) :
    lo β π pre fin k' = ∑ c, ((w.L c : ℕ) : ℝ) * classSize N k' c := by
  unfold lo
  refine sum_congr rfl fun c _ => ?_
  rw [taken_stable k' c t ht hhigh]
  have := hw c
  congr 2; omega

lemma lo_ofM (k' t : ℕ) (w : StateVector N n) (ht : t ≤ m)
    (hw : ∀ c, (w.M c : ℕ) + taken β pre fin k' c t = pieceCount N π k' c)
    (hhigh : ∀ s : Fin m, t ≤ s.val → k' < binInterval N β s) :
    lo β π pre fin k' = ∑ c, ((w.M c : ℕ) : ℝ) * classSize N k' c := by
  unfold lo
  refine sum_congr rfl fun c _ => ?_
  rw [taken_stable k' c t ht hhigh]
  have := hw c
  congr 2; omega

lemma sum_Ico_pieces (a b : ℕ) (f : Fin n → ℝ) :
    ∑ k' ∈ Ico a b, ∑ j ∈ univ.filter (fun j => intervalIndex N (π j) = k'), f j =
      ∑ j ∈ univ.filter (fun j => a ≤ intervalIndex N (π j) ∧ intervalIndex N (π j) < b),
        f j := by
  rw [← sum_fiberwise_of_maps_to (s := univ.filter
      (fun j => a ≤ intervalIndex N (π j) ∧ intervalIndex N (π j) < b)) (t := Ico a b)
      (g := fun j => intervalIndex N (π j))
      (fun j hj => by simp only [mem_filter, mem_univ, true_and] at hj; exact mem_Ico.2 hj)]
  refine sum_congr rfl fun k' hk' => ?_
  congr 1; ext j; simp only [mem_filter, mem_univ, true_and, mem_Ico] at hk' ⊢
  constructor
  · intro h; exact ⟨⟨h ▸ hk'.1, h ▸ hk'.2⟩, h⟩
  · exact fun h => h.2

lemma DD_add (a b : ℕ) (h : a ≤ b) :
    DD β π pre fin b = DD β π pre fin a + ∑ k' ∈ Ico a b, lo β π pre fin k' := by
  unfold DD; rw [sum_range_add_sum_Ico _ h]

end Upd

end X4HS

namespace X4HS

open HochbaumShmoys.Uniform Finset

section Upd2

variable {N m n : ℕ} (hN : 2 ≤ N) {β : Fin m → ℝ} {π : Fin n → ℝ}
  {pre fin : Fin m → StateVector N n}

set_option maxHeartbeats 1000000 in
include hN in
lemma upd_core (hπ : ∀ j, 0 < π j ∧ π j ≤ 1) (k q t : ℕ) (hq : 1 ≤ q) (htm : t ≤ m)
    (u v : StateVector N n)
    (hlow : ∀ s : Fin m, s.val < t → binInterval N β s ≤ k)
    (hhigh : ∀ s : Fin m, t ≤ s.val → k + q ≤ binInterval N β s)
    (hus : ∀ s, 0 ≤ usableSlack N β pre fin s)
    (hI : Inv β π pre fin k t u) (h : update N π k (some q) u = some v) :
    Inv β π pre fin (k + q) t v := by
  obtain ⟨ia, ib, ic, id, ie, iff, ig⟩ := hI
  have hδ := dpos hN
  have hloL : lo β π pre fin k = ∑ c, ((u.L c : ℕ) : ℝ) * classSize N k c :=
    lo_of k t u htm ia (fun s hs => by have := hhigh s hs; omega)
  have hfree : ∀ k', k + 2 ≤ k' → k' < k + q → ∀ c, taken β pre fin k' c m = 0 := by
    intro k' h1 h2 c
    apply taken_zero
    intro s _
    by_cases hs : s.val < t
    · have := hlow s hs; omega
    · have := hhigh s (by omega); omega
  have hrest : ∑ j ∈ univ.filter (fun j => k + 2 ≤ intervalIndex N (π j) ∧
      ∀ q' : ℕ, some q = some q' → intervalIndex N (π j) < k + q'), roundDown N (π j) =
      ∑ k' ∈ Ico (k + 2) (k + q), lo β π pre fin k' := by
    rw [sum_congr rfl fun k' hk' => lo_free hN hπ k' (hfree k' (mem_Ico.1 hk').1
      (mem_Ico.1 hk').2), sum_Ico_pieces]
    congr 1; ext j; simp
  have hzero : ∀ k', k + 2 ≤ k' → ∀ c, taken β pre fin k' c t = 0 := by
    intro k' h1 c
    apply taken_zero
    intro s hs; have := hlow s hs; omega
  have hUt : ∀ K, k ≤ K → US β pre fin (fun s => s.val < t) ≤
      US β pre fin (fun s => binInterval N β s ≤ K) :=
    fun K hK => US_mono hus fun s hs => by have := hlow s hs; omega
  have hU1 : ∀ K, k + 1 ≤ K → US β pre fin (fun s => s.val < t) ≤
      US β pre fin (fun s => binInterval N β s + 1 ≤ K) :=
    fun K hK => US_mono hus fun s hs => by have := hlow s hs; omega
  have hU2 : ∀ K, k + 2 ≤ K → US β pre fin (fun s => s.val < t) ≤
      US β pre fin (fun s => binInterval N β s + 2 ≤ K) :=
    fun K hK => US_mono hus fun s hs => by have := hlow s hs; omega
  have hU12 : US β pre fin (fun s => binInterval N β s + 1 ≤ k) ≤
      US β pre fin (fun s => binInterval N β s + 2 ≤ k + 1) :=
    US_mono hus fun s hs => by omega
  have hDk1 : DD β π pre fin (k + 1) = DD β π pre fin k + lo β π pre fin k := DD_succ k
  simp only [update] at h
  split_ifs at h with h1 hq1 hq2
  · -- q = 1
    obtain rfl : q = 1 := by omega
    obtain rfl := Option.some.inj h
    push Not at h1
    obtain ⟨hW1, -, -⟩ := h1
    have e3 : k + 1 + 2 = k + 3 := rfl
    have e4 : k + 1 + 3 = k + 4 := rfl
    have hc1 := capR (N := N) (n := n) (⌊(((u.V₁ : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + 2) -
      ∑ c, ((u.L c : ℕ) : ℝ) * classSize N k c) / ((N : ℝ)⁻¹) ^ (k + 1 + 2)⌋₊ + u.V₂)
    have hc2 := capR (N := N) (n := n) (u.V : ℕ)
    have hfl := fl_le (pow_pos hδ (k + 1 + 2)) hW1
    push_cast at hc1
    have hp3 := pow_pos hδ (k + 3)
    have hp4 := pow_pos hδ (k + 4)
    refine ⟨fun c => ib c, fun c => ?_, ic, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [hzero (k + 1 + 1) (by omega) c, add_zero]
    · dsimp only
      rw [e3] at hc1 hfl ⊢
      have := US_mono hus (P := fun s => binInterval N β s + 1 ≤ k)
        (Q := fun s => binInterval N β s + 2 ≤ k + 1) (fun s hs => by omega)
      nlinarith
    · dsimp only
      rw [e3, e4] at *
      have := hU1 (k + 1) le_rfl
      nlinarith
    · dsimp only
      rw [e3, e4] at *
      have hA := mul_le_mul_of_nonneg_right hc1 hp3.le
      have hB := mul_le_mul_of_nonneg_right hc2 hp4.le
      simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
      rw [hDk1, hloL]
      nlinarith
    · intro K hK
      rcases Nat.lt_succ_iff_lt_or_eq.1 hK with hK | rfl
      · exact ig K hK
      · rw [hDk1, hloL]; linarith
  · -- q = 2
    obtain rfl := Option.some.inj h
    push Not at h1
    obtain ⟨hW1, hW2, -⟩ := h1
    obtain rfl : q = 2 := hq2
    have hloM : lo β π pre fin (k + 1) = ∑ c, ((u.M c : ℕ) : ℝ) * classSize N (k + 1) c :=
      lo_ofM (k + 1) t u htm ib (fun s hs => by have := hhigh s hs; omega)
    have hW2' := hW2 (le_refl 2)
    have hDk2 : DD β π pre fin (k + 2) =
        DD β π pre fin k + lo β π pre fin k + lo β π pre fin (k + 1) := by
      rw [show k + 2 = k + 1 + 1 from rfl, DD_succ, DD_succ]
    have hc1 := capR (N := N) (n := n) (⌊(((u.V₁ : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + 2) -
      ∑ c, ((u.L c : ℕ) : ℝ) * classSize N k c + ((u.V₂ : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + 3) -
      ∑ c, ((u.M c : ℕ) : ℝ) * classSize N (k + 1) c) / ((N : ℝ)⁻¹) ^ (k + 2 + 2)⌋₊ + u.V)
    have hc0 := capR (N := N) (n := n) 0
    have hfl := fl_le (pow_pos hδ (k + 2 + 2)) hW2'
    push_cast at hc1 hc0
    have e4 : k + 2 + 2 = k + 4 := rfl
    rw [e4] at hc1 hfl
    have hp4 := pow_pos hδ (k + 4)
    have hV2 : ((capSlack N n 0 : ℕ) : ℝ) = 0 := le_antisymm hc0 (Nat.cast_nonneg _)
    refine ⟨fun c => ?_, fun c => ?_, ic, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [hzero (k + 2) (by omega) c, add_zero]
    · dsimp only; rw [hzero (k + 2 + 1) (by omega) c, add_zero]
    · dsimp only
      rw [e4, hDk2, hloL, hloM]
      have := hU2 (k + 2) le_rfl
      nlinarith
    · dsimp only
      rw [e4, hDk2, hloL, hloM, hV2]
      have := hU1 (k + 2) (by omega)
      nlinarith
    · dsimp only
      rw [e4, hDk2, hloL, hloM, hV2]
      have hA := mul_le_mul_of_nonneg_right hc1 hp4.le
      simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
      nlinarith
    · intro K hK
      rcases (show K < k ∨ K = k ∨ K = k + 1 by omega) with hK | rfl | rfl
      · exact ig K hK
      · rw [hDk1, hloL]; linarith
      · rw [hDk2, hloL, hloM]; linarith
  · -- q ≥ 3
    obtain rfl := Option.some.inj h
    push Not at h1
    obtain ⟨hW1, hW2, hW3⟩ := h1
    have hloM : lo β π pre fin (k + 1) = ∑ c, ((u.M c : ℕ) : ℝ) * classSize N (k + 1) c :=
      lo_ofM (k + 1) t u htm ib (fun s hs => by have := hhigh s hs; omega)
    have hW3' := hW3 (by omega)
    have hW2' := hW2 (by omega)
    have hDkq : DD β π pre fin (k + q) = DD β π pre fin k + lo β π pre fin k +
        lo β π pre fin (k + 1) + ∑ k' ∈ Ico (k + 2) (k + q), lo β π pre fin k' := by
      rw [DD_add (k + 2) (k + q) (by omega), show k + 2 = k + 1 + 1 from rfl, DD_succ, DD_succ]
    have hc1 := capR (N := N) (n := n) (⌊(((u.V₁ : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + 2) -
      ∑ c, ((u.L c : ℕ) : ℝ) * classSize N k c + ((u.V₂ : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + 3) -
      ∑ c, ((u.M c : ℕ) : ℝ) * classSize N (k + 1) c + ((u.V : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + 4) -
      ∑ j ∈ univ.filter (fun j => k + 2 ≤ intervalIndex N (π j) ∧
        ∀ q' : ℕ, some q = some q' → intervalIndex N (π j) < k + q'), roundDown N (π j)) /
      ((N : ℝ)⁻¹) ^ (k + q + 2)⌋₊)
    have hc0 := capR (N := N) (n := n) 0
    have hfl := fl_le (pow_pos hδ (k + q + 2)) hW3'
    push_cast at hc0
    rw [hrest] at hc1 hfl hW3'
    have hV2 : ((capSlack N n 0 : ℕ) : ℝ) = 0 := le_antisymm hc0 (Nat.cast_nonneg _)
    have hpq := pow_pos hδ (k + q + 2)
    have hmain : ((capSlack N n (⌊(((u.V₁ : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + 2) -
      ∑ c, ((u.L c : ℕ) : ℝ) * classSize N k c + ((u.V₂ : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + 3) -
      ∑ c, ((u.M c : ℕ) : ℝ) * classSize N (k + 1) c + ((u.V : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + 4) -
      ∑ k' ∈ Ico (k + 2) (k + q), lo β π pre fin k') /
      ((N : ℝ)⁻¹) ^ (k + q + 2)⌋₊) : ℕ) : ℝ) * ((N : ℝ)⁻¹) ^ (k + q + 2) +
        DD β π pre fin (k + q) ≤ US β pre fin (fun s => s.val < t) := by
      have hA := mul_le_mul_of_nonneg_right hc1 hpq.le
      rw [hDkq, hloL, hloM]; linarith
    refine ⟨fun c => ?_, fun c => ?_, ic, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [hzero (k + q) (by omega) c, add_zero]
    · dsimp only; rw [hzero (k + q + 1) (by omega) c, add_zero]
    · dsimp only; rw [hrest]
      exact hmain.trans (hU2 (k + q) (by omega))
    · dsimp only; rw [hrest, hV2]
      have := hU1 (k + q) (by omega)
      linarith
    · dsimp only; rw [hrest, hV2]
      simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
      linarith
    · intro K hK
      rcases (show K < k ∨ K = k ∨ K = k + 1 ∨ k + 2 ≤ K by omega) with hK' | rfl | rfl | hK'
      · exact ig K hK'
      · rw [hDk1, hloL]; linarith
      · rw [show k + 1 + 1 = k + 2 from rfl,
          show DD β π pre fin (k + 2) = DD β π pre fin k + lo β π pre fin k +
            lo β π pre fin (k + 1) by rw [show k + 2 = k + 1 + 1 from rfl, DD_succ, DD_succ],
          hloL, hloM]
        linarith
      · have h1 := DD_mono hN (pre := pre) (fin := fin) (β := β) (π := π)
          (show K + 1 ≤ k + q by omega)
        have h2 := hU2 K hK'
        have hDq : DD β π pre fin (k + q) ≤ US β pre fin (fun s => s.val < t) := by
          rw [hDkq, hloL, hloM]; linarith
        exact h1.trans (hDq.trans h2)

end Upd2

end X4HS

namespace X4HS

open HochbaumShmoys.Uniform Finset

section Upd3

variable {N m n : ℕ} (hN : 2 ≤ N) {β : Fin m → ℝ} {π : Fin n → ℝ}
  {pre fin : Fin m → StateVector N n}

include hN in
lemma none_core (hπ : ∀ j, 0 < π j ∧ π j ≤ 1) (k : ℕ) (u : StateVector N n)
    (hlow : ∀ s : Fin m, binInterval N β s ≤ k)
    (hus : ∀ s, 0 ≤ usableSlack N β pre fin s)
    (hI : Inv β π pre fin k m u) (h : (update N π k none u).isSome) :
    ∀ K, DD β π pre fin (K + 1) ≤ US β pre fin (fun s => binInterval N β s + 2 ≤ K) := by
  obtain ⟨ia, ib, ic, id, ie, iff, ig⟩ := hI
  have hloL : lo β π pre fin k = ∑ c, ((u.L c : ℕ) : ℝ) * classSize N k c :=
    lo_of k m u le_rfl ia (fun s hs => absurd s.2 (by omega))
  have hloM : lo β π pre fin (k + 1) = ∑ c, ((u.M c : ℕ) : ℝ) * classSize N (k + 1) c :=
    lo_ofM (k + 1) m u le_rfl ib (fun s hs => absurd s.2 (by omega))
  have hfree : ∀ k', k + 2 ≤ k' → ∀ c, taken β pre fin k' c m = 0 := by
    intro k' h1 c
    apply taken_zero
    intro s _; have := hlow s; omega
  have hrest : ∑ j ∈ univ.filter (fun j => k + 2 ≤ intervalIndex N (π j) ∧
      ∀ q' : ℕ, (none : Option ℕ) = some q' → intervalIndex N (π j) < k + q'),
        roundDown N (π j) =
      ∑ j ∈ univ.filter (fun j => k + 2 ≤ intervalIndex N (π j)), roundDown N (π j) := by
    congr 1; ext j; simp
  have hDk1 : DD β π pre fin (k + 1) = DD β π pre fin k + lo β π pre fin k := DD_succ k
  have hDk2 : DD β π pre fin (k + 2) =
      DD β π pre fin k + lo β π pre fin k + lo β π pre fin (k + 1) := by
    rw [show k + 2 = k + 1 + 1 from rfl, DD_succ, DD_succ]
  simp only [update] at h
  split_ifs at h with h1
  · simp at h
  push Not at h1
  obtain ⟨hW1, hW2, hW3⟩ := h1
  rw [hrest] at hW3
  intro K
  rcases (show K < k ∨ K = k ∨ K = k + 1 ∨ k + 2 ≤ K by omega) with hK' | rfl | rfl | hK'
  · exact ig K hK'
  · rw [hDk1, hloL]; linarith
  · have := US_mono hus (P := fun s => binInterval N β s + 1 ≤ k)
      (Q := fun s => binInterval N β s + 2 ≤ k + 1) (fun s hs => by omega)
    rw [show k + 1 + 1 = k + 2 from rfl, hDk2, hloL, hloM]; linarith
  · have hsplit := DD_add (β := β) (π := π) (pre := pre) (fin := fin) (k + 2) (K + 1)
      (by omega)
    rw [sum_congr rfl fun k' hk' => lo_free hN hπ k' (hfree k' (mem_Ico.1 hk').1),
      sum_Ico_pieces] at hsplit
    have hsub : ∑ j ∈ univ.filter (fun j => k + 2 ≤ intervalIndex N (π j) ∧
        intervalIndex N (π j) < K + 1), roundDown N (π j) ≤
        ∑ j ∈ univ.filter (fun j => k + 2 ≤ intervalIndex N (π j)), roundDown N (π j) :=
      sum_le_sum_of_subset_of_nonneg (fun j hj => by
        simp only [mem_filter, mem_univ, true_and] at hj ⊢; exact hj.1)
        (fun j _ _ => rd_nonneg hN _ (hπ j).1)
    have hU : US β pre fin (fun s => s.val < m) ≤
        US β pre fin (fun s => binInterval N β s + 2 ≤ K) :=
      US_mono hus fun s _ => by have := hlow s; omega
    rw [hsplit, hDk2, hloL, hloM]
    linarith

end Upd3

end X4HS

namespace X4HS

open HochbaumShmoys.Uniform Finset

section Main

variable {N m n : ℕ} (hN : 2 ≤ N) {β : Fin m → ℝ} {π : Fin n → ℝ}
  {pre fin : Fin m → StateVector N n}

lemma taken_at_zero (k' : ℕ) (c : Fin (numClasses N)) : taken β pre fin k' c 0 = 0 := by
  unfold taken; simp

lemma US_nonneg (hus : ∀ s, 0 ≤ usableSlack N β pre fin s) (P : Fin m → Prop)
    [DecidablePred P] : 0 ≤ US β pre fin P :=
  sum_nonneg fun s _ => hus s

include hN in
lemma inv_all (hm : 0 < m) (hβ : Antitone β) (hβ0 : β ⟨0, hm⟩ = 1) (hβpos : ∀ t, 0 < β t)
    (hπ : ∀ j, 0 < π j ∧ π j ≤ 1)
    (hpath : IsLayeredPath N β π pre fin) (hpre0 : pre ⟨0, hm⟩ = initialState N π) :
    ∀ t (ht : t < m), Inv β π pre fin (binInterval N β ⟨t, ht⟩) t (pre ⟨t, ht⟩) := by
  have hus := usable_nonneg hN hpath
  intro t
  induction t with
  | zero =>
    intro ht
    have hk0 : binInterval N β ⟨0, ht⟩ = 0 := by
      unfold binInterval; rw [hβ0, iv_one hN]
    rw [hk0, hpre0]
    have hD0 : DD β π pre fin 0 = 0 := by unfold DD; simp
    refine ⟨fun c => ?_, fun c => ?_, fun k' c => ?_, ?_, ?_, ?_, fun K hK => absurd hK (by omega)⟩
    · rw [taken_at_zero]; rfl
    · rw [taken_at_zero]; rfl
    · rw [taken_at_zero]; exact Nat.zero_le _
    · simp only [initialState, Fin.val_zero, Nat.cast_zero, zero_mul, zero_add, hD0]
      exact US_nonneg hus _
    · simp only [initialState, Fin.val_zero, Nat.cast_zero, zero_mul, zero_add, hD0]
      exact US_nonneg hus _
    · simp only [initialState, Fin.val_zero, Nat.cast_zero, zero_mul, zero_add, hD0]
      exact US_nonneg hus _
  | succ t ih =>
    intro ht
    have ht' : t < m := by omega
    have h1 := step_cfg hN hpath ⟨t, ht'⟩ (ih ht')
    by_cases hs : binInterval N β ⟨t + 1, ht⟩ = binInterval N β ⟨t, ht'⟩
    · have : afterBin N β pre fin ⟨t, ht'⟩ = pre ⟨t + 1, ht⟩ := by
        unfold afterBin; rw [dif_pos ht, if_pos hs]
      rw [hs, ← this]; exact h1
    · have haft : afterBin N β pre fin ⟨t, ht'⟩ = fin ⟨t, ht'⟩ := by
        unfold afterBin; rw [dif_pos ht, if_neg hs]
      have hlast : IsLastOfStage N β ⟨t, ht'⟩ := fun h => hs
      have hupd := (hpath.2.2.1 ⟨t, ht'⟩ ht hlast).2.2
      have hle := kb_mono hN hβ hβpos (show (⟨t, ht'⟩ : Fin m) ≤ ⟨t + 1, ht⟩ from
        Nat.le_succ t)
      rw [haft] at h1
      have := upd_core hN hπ (binInterval N β ⟨t, ht'⟩)
        (binInterval N β ⟨t + 1, ht⟩ - binInterval N β ⟨t, ht'⟩) (t + 1) (by omega) ht.le
        _ _ (fun s hs' => kb_mono hN hβ hβpos (show s ≤ ⟨t, ht'⟩ from Nat.lt_succ_iff.1 hs'))
        (fun s hs' => by
          rw [Nat.add_sub_cancel' hle]
          exact kb_mono hN hβ hβpos (show (⟨t + 1, ht⟩ : Fin m) ≤ s from hs'))
        hus h1 hupd
      rwa [Nat.add_sub_cancel' hle] at this

include hN in
lemma final_claims (hm : 0 < m) (hβ : Antitone β) (hβ0 : β ⟨0, hm⟩ = 1)
    (hβpos : ∀ t, 0 < β t) (hπ : ∀ j, 0 < π j ∧ π j ≤ 1)
    (hpath : IsLayeredPath N β π pre fin) (hpre0 : pre ⟨0, hm⟩ = initialState N π) :
    (∀ K, DD β π pre fin (K + 1) ≤ US β pre fin (fun s => binInterval N β s + 2 ≤ K)) ∧
    (∀ k' c, taken β pre fin k' c m ≤ pieceCount N π k' c) := by
  have hus := usable_nonneg hN hpath
  have ht' : m - 1 < m := by omega
  have h1 := step_cfg hN hpath ⟨m - 1, ht'⟩ (inv_all hN hm hβ hβ0 hβpos hπ hpath hpre0 _ ht')
  have haft : afterBin N β pre fin ⟨m - 1, ht'⟩ = fin ⟨m - 1, ht'⟩ := by
    unfold afterBin; rw [dif_neg (by simp; omega)]
  rw [haft, show m - 1 + 1 = m by omega] at h1
  have hsucc := (hpath.2.2.2 ⟨m - 1, ht'⟩ (by simp; omega)).2
  refine ⟨none_core hN hπ _ _ (fun s => kb_mono hN hβ hβpos
    (show s ≤ ⟨m - 1, ht'⟩ from Nat.le_sub_one_of_lt s.2)) hus h1 hsucc, h1.2.2.1⟩

end Main

end X4HS

namespace X4HS

open HochbaumShmoys.Uniform Finset

lemma rd_pos {N : ℕ} (hN : 2 ≤ N) (x : ℝ) (hx0 : 0 < x) : 0 < roundDown N x := by
  have hp : 0 < ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2) := pow_pos (dpos hN) _
  have hy := y_gt hN x hx0
  have hN0 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold roundDown
  apply mul_pos _ hp
  have : (1 : ℤ) ≤ ⌊x / ((N : ℝ)⁻¹) ^ (intervalIndex N x + 2)⌋ :=
    Int.le_floor.2 (by push_cast; linarith)
  exact_mod_cast (show (0 : ℤ) < _ by omega)

/-- Distribute pieces of a finite set into labelled groups of prescribed sizes. -/
lemma assign {α ι : Type*} [Fintype ι] [DecidableEq α] [DecidableEq ι] (G : Finset α)
    (d : ι → ℕ) (h : ∑ i, d i ≤ G.card) :
    ∃ f : α → Option ι, ∀ i, (G.filter (fun j => f j = some i)).card = d i := by
  classical
  have hc : Fintype.card (Σ i, Fin (d i)) ≤ Fintype.card G := by
    simpa [Fintype.card_sigma, Fintype.card_fin] using h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let f : α → Option ι := fun j =>
    if h : ∃ x, ((e x : G) : α) = j then some (Classical.choose h).1 else none
  refine ⟨f, fun i => ?_⟩
  have key : G.filter (fun j => f j = some i) =
      (univ : Finset (Fin (d i))).map
        ⟨fun a => ((e ⟨i, a⟩ : G) : α), fun a b hab => by
          have := e.injective (Subtype.ext hab)
          simpa using this⟩ := by
    ext j
    simp only [mem_filter, mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨hj, hf⟩
      simp only [f] at hf
      split_ifs at hf with hx
      · have hx' := Classical.choose_spec hx
        set x := Classical.choose hx
        obtain ⟨i', a⟩ := x
        simp only [Option.some.injEq] at hf
        subst hf
        exact ⟨a, hx'⟩
    · rintro ⟨a, ha⟩
      change ((e ⟨i, a⟩ : G) : α) = j at ha
      subst ha
      refine ⟨(e ⟨i, a⟩).2, ?_⟩
      simp only [f]
      have hx : ∃ x, ((e x : G) : α) = ((e ⟨i, a⟩ : G) : α) := ⟨_, rfl⟩
      rw [dif_pos hx]
      have := e.injective (Subtype.ext (Classical.choose_spec hx))
      rw [this]
  rw [key, card_map, card_univ, Fintype.card_fin]

section Small

variable {N m n : ℕ} {β : Fin m → ℝ} {pre fin : Fin m → StateVector N n}

/-- Prefix-sum placement of the small pieces. -/
lemma small_assign (hm : 0 < m) (hmono : ∀ s t : Fin m, s ≤ t →
      binInterval N β s ≤ binInterval N β t)
    (hus : ∀ s, 0 ≤ usableSlack N β pre fin s)
    (S : Finset (Fin n)) (iv : Fin n → ℕ) (r : Fin n → ℝ) (ρ : Fin n → ℕ)
    (hr : ∀ j ∈ S, 0 < r j)
    (hcap : ∀ j ∈ S, ∑ j' ∈ S.filter (fun j' => ρ j' < ρ j), r j' + r j ≤
      US β pre fin (fun s => binInterval N β s + 2 ≤ iv j)) :
    ∃ τ : Fin n → Fin m, ∀ j ∈ S, binInterval N β (τ j) + 2 ≤ iv j ∧
      ∑ j' ∈ S.filter (fun j' => τ j' = τ j ∧ ρ j' < ρ j), r j' < usableSlack N β pre fin (τ j) := by
  classical
  let P : Fin n → ℝ := fun j => ∑ j' ∈ S.filter (fun j' => ρ j' < ρ j), r j'
  let C : ℕ → ℝ := fun t => US β pre fin (fun s => s.val < t)
  let E : Fin n → Finset (Fin m) := fun j =>
    univ.filter (fun s : Fin m => binInterval N β s + 2 ≤ iv j ∧ C s.val ≤ P j)
  have hP0 : ∀ j ∈ S, 0 ≤ P j := fun j hj =>
    sum_nonneg fun j' hj' => (hr j' (mem_filter.1 hj').1).le
  have hC0 : C 0 = 0 := by simp [C, US]
  have hCs : ∀ t : Fin m, C (t.val + 1) = C t.val + usableSlack N β pre fin t :=
    fun t => US_lt_succ t
  have hE : ∀ j ∈ S, (E j).Nonempty := by
    intro j hj
    have h1 := hcap j hj
    have h2 := hr j hj
    have h3 := hP0 j hj
    have : (univ.filter (fun s : Fin m => binInterval N β s + 2 ≤ iv j)).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have : US β pre fin (fun s => binInterval N β s + 2 ≤ iv j) = 0 := by
        unfold US; rw [hne, sum_empty]
      linarith
    obtain ⟨s, hs⟩ := this
    have hs' := (mem_filter.1 hs).2
    refine ⟨⟨0, hm⟩, mem_filter.2 ⟨mem_univ _, ?_, ?_⟩⟩
    · have := hmono ⟨0, hm⟩ s (Nat.zero_le _); omega
    · show C 0 ≤ P j; rw [hC0]; exact h3
  let τ : Fin n → Fin m := fun j => if h : (E j).Nonempty then (E j).max' h else ⟨0, hm⟩
  have hτE : ∀ j ∈ S, τ j ∈ E j := by
    intro j hj
    simp only [τ, dif_pos (hE j hj)]
    exact max'_mem _ _
  have hτlt : ∀ j ∈ S, P j < C ((τ j).val + 1) := by
    intro j hj
    have hmem := mem_filter.1 (hτE j hj)
    by_cases hnext : ∃ h : (τ j).val + 1 < m,
        binInterval N β ⟨(τ j).val + 1, h⟩ + 2 ≤ iv j
    · obtain ⟨h, hk⟩ := hnext
      by_contra hle
      push Not at hle
      have hmemN : (⟨(τ j).val + 1, h⟩ : Fin m) ∈ E j := mem_filter.2 ⟨mem_univ _, hk, hle⟩
      have hτM : τ j = (E j).max' (hE j hj) := dif_pos (hE j hj)
      have h2 := le_max' (E j) _ hmemN
      rw [← hτM] at h2
      exact absurd (Fin.le_iff_val_le_val.1 h2) (by simp)
    · push Not at hnext
      have hsub : US β pre fin (fun s => binInterval N β s + 2 ≤ iv j) ≤ C ((τ j).val + 1) := by
        apply US_mono hus
        intro s hs
        by_contra hlt
        push Not at hlt
        have h1 : (τ j).val + 1 < m := by have := s.2; omega
        have h2 := hmono ⟨(τ j).val + 1, h1⟩ s (show (τ j).val + 1 ≤ s.val by omega)
        have := hnext h1
        omega
      have := hcap j hj
      have := hr j hj
      linarith
  refine ⟨τ, fun j hj => ⟨(mem_filter.1 (hτE j hj)).2.1, ?_⟩⟩
  set T := S.filter (fun j' => τ j' = τ j ∧ ρ j' < ρ j) with hT
  have hCτ : C (τ j).val ≤ P j := (mem_filter.1 (hτE j hj)).2.2
  have hlt := hτlt j hj
  rw [hCs] at hlt
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he, sum_empty]; linarith
  obtain ⟨j₁, hj₁, hmin⟩ := exists_min_image T ρ hne
  have hj₁' := mem_filter.1 hj₁
  have hj₁S := hj₁'.1
  have hCj₁ : C (τ j).val ≤ P j₁ := by
    rw [← hj₁'.2.1]; exact (mem_filter.1 (hτE j₁ hj₁S)).2.2
  have hsplit : P j = P j₁ + ∑ j' ∈ S.filter (fun j' => ρ j₁ ≤ ρ j' ∧ ρ j' < ρ j), r j' := by
    simp only [P]
    rw [← sum_filter_add_sum_filter_not (S.filter (fun j' => ρ j' < ρ j))
      (fun j' => ρ j' < ρ j₁)]
    congr 1
    · congr 1; ext x; simp only [mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by have := hj₁'.2.2; omega⟩, h3⟩
    · congr 1; ext x; simp only [mem_filter, not_lt]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3, h2⟩
      · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
  have hTle : ∑ j' ∈ T, r j' ≤ ∑ j' ∈ S.filter (fun j' => ρ j₁ ≤ ρ j' ∧ ρ j' < ρ j), r j' := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      have hx' := mem_filter.1 hx
      exact mem_filter.2 ⟨hx'.1, hmin x hx, hx'.2.2⟩
    · intro x hx _; exact (hr x (mem_filter.1 hx).1).le
  linarith

end Small

end X4HS

namespace X4HS

open HochbaumShmoys.Uniform Finset

section Assemble

variable {N m n : ℕ} (hN : 2 ≤ N) {β : Fin m → ℝ} {π : Fin n → ℝ}
  {pre fin : Fin m → StateVector N n}

include hN in
theorem traced_exists (hm : 0 < m) (hβ : Antitone β) (hβ0 : β ⟨0, hm⟩ = 1)
    (hβpos : ∀ t, 0 < β t) (hπ : ∀ j, 0 < π j ∧ π j ≤ 1)
    (hpath : IsLayeredPath N β π pre fin) (hpre0 : pre ⟨0, hm⟩ = initialState N π) :
    ∃ σ, IsTracedFrom N β π pre fin σ := by
  classical
  obtain ⟨hD, htk⟩ := final_claims hN hm hβ hβ0 hβpos hπ hpath hpre0
  have hus := usable_nonneg hN hpath
  have hmono : ∀ s t : Fin m, s ≤ t → binInterval N β s ≤ binInterval N β t :=
    fun s t h => kb_mono hN hβ hβpos h
  set iv : Fin n → ℕ := fun j => intervalIndex N (π j) with hiv
  set cl : Fin n → Fin (numClasses N) :=
    fun j => ⟨roundClass N (π j), class_lt hN _ (hπ j).1 (hπ j).2⟩ with hcl
  have hclv : ∀ j (c : Fin (numClasses N)), (cl j = c ↔ roundClass N (π j) = c.val) :=
    fun j c => Fin.ext_iff
  have hG : ∀ k' (c : Fin (numClasses N)),
      (univ.filter (fun j => iv j = k' ∧ cl j = c)).card = pieceCount N π k' c := by
    intro k' c
    rw [pc_eq]; simp only [filter_filter, hclv]; rfl
  have hsumdec : ∀ k' c, ∑ s, dec β pre fin k' c s = taken β pre fin k' c m := by
    intro k' c; unfold taken
    congr 1; ext s; simp
  have hF : ∀ k' (c : Fin (numClasses N)), ∃ f : Fin n → Option (Fin m), ∀ s,
      ((univ.filter (fun j => iv j = k' ∧ cl j = c)).filter (fun j => f j = some s)).card =
        dec β pre fin k' c s := fun k' c =>
    assign _ _ (by rw [hsumdec, hG]; exact htk k' c)
  choose F hF using hF
  set big : Fin n → Option (Fin m) := fun j => F (iv j) (cl j) j with hbig
  have hcount : ∀ k' c s, (univ.filter (fun j => iv j = k' ∧ cl j = c ∧ big j = some s)).card =
      dec β pre fin k' c s := by
    intro k' c s
    rw [← hF k' c s, filter_filter]
    congr 1; ext j; simp only [mem_filter, mem_univ, true_and, hbig]
    constructor
    · rintro ⟨h1, h2, h3⟩; subst h1; subst h2; exact ⟨⟨rfl, rfl⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; subst h1; subst h2; exact ⟨rfl, rfl, h3⟩
  have hbigkb : ∀ j s, big j = some s →
      binInterval N β s = iv j ∨ binInterval N β s + 1 = iv j := by
    intro j s hjs
    by_contra hne
    push Not at hne
    have h0 : dec β pre fin (iv j) (cl j) s = 0 := by
      unfold dec; rw [if_neg hne.1, if_neg hne.2]
    have := hcount (iv j) (cl j) s
    rw [h0, card_eq_zero] at this
    have hj : j ∈ univ.filter (fun j' => iv j' = iv j ∧ cl j' = cl j ∧ big j' = some s) :=
      mem_filter.2 ⟨mem_univ _, rfl, rfl, hjs⟩
    rw [this] at hj; simp at hj
  have hnone : ∀ k' c, (univ.filter (fun j => iv j = k' ∧ cl j = c ∧ big j = none)).card =
      pieceCount N π k' c - taken β pre fin k' c m := by
    intro k' c
    have h1 := card_eq_sum_card_fiberwise (s := univ.filter (fun j => iv j = k' ∧ cl j = c))
      (t := (univ : Finset (Option (Fin m)))) (f := big) (fun _ _ => mem_univ _)
    rw [hG, Fintype.sum_option] at h1
    have h2 : ∀ o : Option (Fin m), (univ.filter (fun j => iv j = k' ∧ cl j = c)).filter
        (fun j => big j = o) = univ.filter (fun j => iv j = k' ∧ cl j = c ∧ big j = o) := by
      intro o; rw [filter_filter]; congr 1; ext j; simp [and_assoc]
    simp only [h2, hcount, hsumdec] at h1
    omega
  set S := univ.filter (fun j => big j = none) with hS
  set r : Fin n → ℝ := fun j => roundDown N (π j) with hr
  set ρ : Fin n → ℕ := fun j => iv j * n + j.val with hρ
  have hr_pos : ∀ j ∈ S, 0 < r j := fun j _ => rd_pos hN _ (hπ j).1
  have hrcl : ∀ j, r j = classSize N (iv j) (cl j) := fun j => (class_eq hN _ (hπ j).1).symm
  -- leftover demand up to interval K
  have hlo : ∀ k', ∑ j ∈ S.filter (fun j => iv j = k'), r j = lo β π pre fin k' := by
    intro k'
    rw [show ∑ j ∈ S.filter (fun j => iv j = k'), r j =
        ∑ j ∈ S.filter (fun j => iv j = k'), classSize N k' (roundClass N (π j)) from
      sum_congr rfl fun j hj => by
        rw [hrcl j, (mem_filter.1 hj).2]]
    rw [fiber _ (fun j => roundClass N (π j)) (numClasses N)
      (fun j _ => class_lt hN _ (hπ j).1 (hπ j).2) (classSize N k')]
    unfold lo
    refine sum_congr rfl fun c _ => ?_
    congr 2
    rw [← hnone k' c, hS, filter_filter, filter_filter]
    congr 1; ext j; simp only [mem_filter, mem_univ, true_and, hclv]; tauto
  have hDS : ∀ K, ∑ j ∈ S.filter (fun j => iv j ≤ K), r j = DD β π pre fin (K + 1) := by
    intro K
    unfold DD
    rw [← sum_fiberwise_of_maps_to (s := S.filter (fun j => iv j ≤ K)) (t := range (K + 1))
      (g := iv) (fun j hj => mem_range.2 (by have := (mem_filter.1 hj).2; omega))]
    refine sum_congr rfl fun k' hk' => ?_
    rw [← hlo k', filter_filter]
    have hk'' := mem_range.1 hk'
    congr 1
    apply filter_congr
    intro j _
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by omega, h⟩
  have hρiv : ∀ j j', ρ j' < ρ j → iv j' ≤ iv j := by
    intro j j' h
    by_contra hc; push Not at hc
    have h1 : (iv j + 1) * n ≤ iv j' * n := Nat.mul_le_mul_right _ hc
    have h2 := j.2
    simp only [hρ] at h
    nlinarith
  have hcap : ∀ j ∈ S, ∑ j' ∈ S.filter (fun j' => ρ j' < ρ j), r j' + r j ≤
      US β pre fin (fun s => binInterval N β s + 2 ≤ iv j) := by
    intro j hj
    have hsub : ∑ j' ∈ S.filter (fun j' => ρ j' < ρ j), r j' + r j ≤
        ∑ j' ∈ S.filter (fun j' => iv j' ≤ iv j), r j' := by
      rw [add_comm, ← sum_insert (show j ∉ S.filter (fun j' => ρ j' < ρ j) by simp)]
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_filter.2 ⟨hj, le_rfl⟩
        · exact mem_filter.2 ⟨(mem_filter.1 hx).1, hρiv _ _ (mem_filter.1 hx).2⟩
      · intro x hx _; exact (hr_pos x (mem_filter.1 hx).1).le
    exact hsub.trans ((hDS (iv j)).trans_le (hD (iv j)))
  obtain ⟨τ, hτ⟩ := small_assign (pre := pre) (fin := fin) hm hmono hus S iv r ρ hr_pos hcap
  set σ : Fin n → Fin m := fun j => (big j).getD (τ j) with hσ
  have hσbig : ∀ j s, big j = some s → σ j = s := fun j s h => by simp [hσ, h]
  have hσsmall : ∀ j, big j = none → σ j = τ j := fun j h => by simp [hσ, h]
  have hsmall : ∀ j, IsSmallIn N β π σ j ↔ big j = none := by
    intro j
    constructor
    · intro h
      rcases hb : big j with _ | s
      · rfl
      · exfalso
        have := hbigkb j s hb
        unfold IsSmallIn at h; rw [hσbig j s hb] at h
        simp only [hiv] at this; omega
    · intro h
      unfold IsSmallIn; rw [hσsmall j h]
      exact (hτ j (mem_filter.2 ⟨mem_univ _, h⟩)).1
  refine ⟨σ, fun j => ?_, fun t c => ?_, fun t c => ?_, ρ, ?_, ?_, ?_⟩
  · rcases hb : big j with _ | s
    · rw [hσsmall j hb]; have := (hτ j (mem_filter.2 ⟨mem_univ _, hb⟩)).1
      simp only [hiv] at this; omega
    · rw [hσbig j s hb]; have := hbigkb j s hb; simp only [hiv] at this; omega
  · have : dec β pre fin (binInterval N β t) c t =
        ((pre t).L c : ℕ) - ((afterBin N β pre fin t).L c : ℕ) := by
      unfold dec; rw [if_pos rfl]
    rw [← this, ← hcount]
    congr 1; ext j; simp only [mem_filter, mem_univ, true_and, hclv]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, h3, ?_⟩
      rcases hb : big j with _ | s
      · exfalso; rw [hσsmall j hb] at h1
        have := (hτ j (mem_filter.2 ⟨mem_univ _, hb⟩)).1
        rw [h1] at this; simp only [hiv] at this h2; omega
      · rw [hσbig j s hb] at h1; rw [h1]
    · rintro ⟨h1, h2, h3⟩; exact ⟨hσbig j t h3, h1, h2⟩
  · have : dec β pre fin (binInterval N β t + 1) c t =
        ((pre t).M c : ℕ) - ((afterBin N β pre fin t).M c : ℕ) := by
      unfold dec; rw [if_neg (by omega), if_pos rfl]
    rw [← this, ← hcount]
    congr 1; ext j; simp only [mem_filter, mem_univ, true_and, hclv]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, h3, ?_⟩
      rcases hb : big j with _ | s
      · exfalso; rw [hσsmall j hb] at h1
        have := (hτ j (mem_filter.2 ⟨mem_univ _, hb⟩)).1
        rw [h1] at this; simp only [hiv] at this h2; omega
      · rw [hσbig j s hb] at h1; rw [h1]
    · rintro ⟨h1, h2, h3⟩; exact ⟨hσbig j t h3, h1, h2⟩
  · intro a b hab
    have h1 := congrArg (· % n) hab
    simp only [hρ, Nat.mul_comm _ n, Nat.mul_add_mod, Nat.mod_eq_of_lt a.2,
      Nat.mod_eq_of_lt b.2] at h1
    exact Fin.ext h1
  · intro j j' _ _ hph
    have hlt : iv j < iv j' := by
      by_contra hc; push Not at hc
      have : smallPhase N β (π j') ≤ smallPhase N β (π j) := by
        unfold smallPhase
        apply sup_mono
        intro s hs
        simp only [mem_filter, mem_univ, true_and] at hs ⊢
        simp only [hiv] at hc; omega
      omega
    have h1 : (iv j + 1) * n ≤ iv j' * n := Nat.mul_le_mul_right _ hlt
    have h2 := j.2
    simp only [hρ]
    nlinarith
  · intro j hj
    have hjS : big j = none := (hsmall j).1 hj
    have := (hτ j (mem_filter.2 ⟨mem_univ _, hjS⟩)).2
    rw [hσsmall j hjS]
    convert this using 2
    ext j'; simp only [mem_filter, mem_univ, true_and, hsmall, hS]
    constructor
    · rintro ⟨h1, h2, h3⟩; simp only [hσsmall j' h1, hσsmall j hjS] at h2; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; refine ⟨h1, ?_, h3⟩; simp only [hσsmall j' h1, hσsmall j hjS]; exact h2

end Assemble

end X4HS

open HochbaumShmoys.Uniform in
theorem solution (N : ℕ) (hN : 2 ≤ N) (m n : ℕ) (hm : 0 < m) (β : Fin m → ℝ) (π : Fin n → ℝ)
    (hβ : Antitone β) (hβ0 : β ⟨0, hm⟩ = 1) (hβpos : ∀ t, 0 < β t)
    (hπ : ∀ j, 0 < π j ∧ π j ≤ 1)
    (hpath : Relation.ReflTransGen (Arc N β π) (initialNode N π hm) Node.success) :
    ∃ σ : Fin n → Fin m,
      IsRelaxedFeasible (2 * (N : ℝ)⁻¹ + ((N : ℝ)⁻¹) ^ 2) π β σ := by
  obtain ⟨pre, fin, hlp, h0⟩ := X4HS.layered_of_reach β π hm hpath
  obtain ⟨σ, hσ⟩ := X4HS.traced_exists hN hm hβ hβ0 hβpos hπ hlp h0
  exact ⟨σ, X4HS.traced_feasible N hN m n hm β π hβ hβ0 hβpos hπ σ ⟨pre, fin, hlp, hσ⟩⟩
