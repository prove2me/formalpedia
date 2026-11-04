-- Prove2me | solution 1 for InfoRelaxTS.Gap.eq_269_275
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:10:07.924498+00:00
-- url     : https://prove2.me/submissions/ee19c1bb-82fd-4531-a8df-cb00fdfb341a

import Mathlib
import Definitions.Def_InfoRelaxTS_Gap_Setting

namespace InfoRelaxTS.Gap

private lemma pullsBefore_lt_of_lt {K T : ℕ} (s : Fin T → Fin K) (a : Fin K)
    (t₁ t₂ : Fin T) (h₁ : s t₁ = a) (h12 : t₁ < t₂) :
    pullsBefore s t₁ a < pullsBefore s t₂ a := by
  unfold pullsBefore
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨t₁, ?_, ?_⟩
    · simp [h12, h₁]
    · simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨lt_trans hx.1 h12, hx.2⟩

private lemma pullsBefore_lt_pullCount {K T : ℕ} (s : Fin T → Fin K) (t : Fin T) :
    pullsBefore s t (s t) < pullCount s (s t) := by
  unfold pullsBefore pullCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨t, ?_, ?_⟩
    · simp
    · simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2

/-- Regrouping a sum over time by arms. -/
private lemma sum_regroup {K T : ℕ} (s : Fin T → Fin K) (f : Fin K → ℕ → ℝ) :
    ∑ t, f (s t) (pullsBefore s t (s t)) =
      ∑ a, ∑ n ∈ Finset.range (pullCount s a), f a n := by
  rw [← Finset.sum_fiberwise Finset.univ s]
  refine Finset.sum_congr rfl fun a _ => ?_
  set S := Finset.univ.filter fun t : Fin T => s t = a with hS
  have hfib : ∀ t ∈ S, f (s t) (pullsBefore s t (s t)) = f a (pullsBefore s t a) := by
    intro t ht
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht]
  rw [Finset.sum_congr rfl hfib]
  have hinj : Set.InjOn (fun t => pullsBefore s t a) S := by
    intro x hx y hy hxy
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hxy (ne_of_lt (pullsBefore_lt_of_lt s a x y hx h))
    · exact absurd hxy (ne_of_gt (pullsBefore_lt_of_lt s a y x hy h))
  have hcount : pullCount s a = S.card := rfl
  have himg : S.image (fun t => pullsBefore s t a) = Finset.range (pullCount s a) := by
    apply Finset.eq_of_subset_of_card_le
    · intro n hn
      simp only [Finset.mem_image] at hn
      obtain ⟨t, ht, rfl⟩ := hn
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have := pullsBefore_lt_pullCount s t
      rw [ht] at this
      simpa using this
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range, hcount]
  rw [← himg, Finset.sum_image hinj]

private lemma sum_pullCount {K T : ℕ} (s : Fin T → Fin K) :
    ∑ a, (pullCount s a : ℝ) = T := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin T)))
    (t := (Finset.univ : Finset (Fin K))) (f := s) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have : (T : ℝ) = ((∑ b, (Finset.univ.filter fun a => s a = b).card : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [this]
  push_cast
  rfl

private lemma inv_sqrt_succ_le (N : ℕ) :
    1 / Real.sqrt ((N : ℝ) + 1) ≤ 2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set a := Real.sqrt ((N : ℝ) + 1)
  set b := Real.sqrt (N : ℝ)
  have ha2 : a ^ 2 = N + 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = N := Real.sq_sqrt hN
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  rw [div_le_iff₀ ha]
  nlinarith

private lemma sum_inv_sqrt_le (ν : ℝ) (hν : 0 < ν) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), 1 / Real.sqrt (ν + n) ≤ 1 / Real.sqrt ν + 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h1 : 1 / Real.sqrt (ν + ((N + 1 : ℕ) : ℝ)) ≤ 1 / Real.sqrt ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · exact Real.sqrt_pos.mpr (by positivity)
      · apply Real.sqrt_le_sqrt; push_cast; linarith
    have h2 := inv_sqrt_succ_le N
    push_cast at h1 ⊢
    linarith

private lemma cs_bound {K T : ℕ} (s : Fin T → Fin K) :
    ∑ a, Real.sqrt (pullCount s a) ≤ Real.sqrt ((K : ℝ) * T) := by
  apply Real.le_sqrt_of_sq_le
  have hcs : (∑ a : Fin K, 1 * Real.sqrt (pullCount s a)) ^ 2 ≤
      (∑ a : Fin K, (1 : ℝ) ^ 2) * ∑ a : Fin K, Real.sqrt (pullCount s a) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  have hsq : ∀ a, Real.sqrt (pullCount s a : ℝ) ^ 2 = pullCount s a :=
    fun a => Real.sq_sqrt (Nat.cast_nonneg _)
  simp_rw [hsq, sum_pullCount] at hcs
  exact hcs


private lemma step_D (T : ℝ) (hT : 0 < T) (N : ℕ) :
    1 / Real.sqrt ((N : ℝ) + 1) - Real.sqrt ((N : ℝ) + 1) / (2 * T) ≤
      (2 * Real.sqrt ((N : ℝ) + 1) - ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1) / (3 * T)) -
      (2 * Real.sqrt (N : ℝ) - (N : ℝ) * Real.sqrt (N : ℝ) / (3 * T)) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 := inv_sqrt_succ_le N
  set a := Real.sqrt ((N : ℝ) + 1)
  set b := Real.sqrt (N : ℝ)
  have ha2 : a ^ 2 = N + 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = N := Real.sq_sqrt hN
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have key : 2 * (((N : ℝ) + 1) * a - (N : ℝ) * b) ≤ 3 * a := by
    rw [← ha2, ← hb2]
    have hab : a ^ 2 - b ^ 2 = 1 := by rw [ha2, hb2]; ring
    nlinarith [mul_nonneg (show 0 ≤ a ^ 2 + a * b - 2 * b ^ 2 by nlinarith) (sub_nonneg.mpr hba)]
  have : (((N : ℝ) + 1) * a - (N : ℝ) * b) / (3 * T) ≤ a / (2 * T) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e : (2 * a - ((N : ℝ) + 1) * a / (3 * T)) - (2 * b - (N : ℝ) * b / (3 * T)) =
      2 * (a - b) - (((N : ℝ) + 1) * a - (N : ℝ) * b) / (3 * T) := by ring
  rw [e]
  linarith

private lemma g_le_f (ν : ℝ) (hν : 0 < ν) (T : ℕ) (n : ℕ) (hn1 : 1 ≤ n) (hnT : n ≤ T) :
    Real.sqrt (1 / (ν + n) - 1 / (ν + T)) ≤
      1 / Real.sqrt (n : ℝ) - Real.sqrt (n : ℝ) / (2 * T) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnT' : (n : ℝ) ≤ T := by exact_mod_cast hnT
  have hT : (0 : ℝ) < T := by linarith
  have e1 : 1 / (ν + n) - 1 / (ν + T) = ((T : ℝ) - n) / ((ν + n) * (ν + T)) := by
    field_simp; ring
  have e2 : 1 / (n : ℝ) - 1 / T = ((T : ℝ) - n) / (n * T) := by
    field_simp
  have h1 : 1 / (ν + n) - 1 / (ν + T) ≤ 1 / (n : ℝ) - 1 / T := by
    rw [e1, e2]
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  set c := Real.sqrt (n : ℝ)
  have hc2 : c ^ 2 = n := Real.sq_sqrt (by linarith)
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hbase : 0 ≤ 1 / c - c / (2 * T) := by
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) hc]
    nlinarith
  have h2 : 1 / (n : ℝ) - 1 / T ≤ (1 / c - c / (2 * T)) ^ 2 := by
    have : (1 / c - c / (2 * T)) ^ 2 = 1 / (n : ℝ) - 1 / T + n / (4 * T ^ 2) := by
      rw [← hc2]; field_simp; ring
    rw [this]
    have : (0 : ℝ) ≤ n / (4 * T ^ 2) := by positivity
    linarith
  calc Real.sqrt (1 / (ν + n) - 1 / (ν + T)) ≤ Real.sqrt ((1 / c - c / (2 * T)) ^ 2) :=
        Real.sqrt_le_sqrt (le_trans h1 h2)
    _ = 1 / c - c / (2 * T) := Real.sqrt_sq hbase

private lemma f_nonneg (T : ℕ) (n : ℕ) (hn1 : 1 ≤ n) (hnT : n ≤ T) :
    0 ≤ 1 / Real.sqrt (n : ℝ) - Real.sqrt (n : ℝ) / (2 * T) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnT' : (n : ℝ) ≤ T := by exact_mod_cast hnT
  have hT : (0 : ℝ) < T := by linarith
  set c := Real.sqrt (n : ℝ)
  have hc2 : c ^ 2 = n := Real.sq_sqrt (by linarith)
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  rw [sub_nonneg, div_le_div_iff₀ (by positivity) hc]
  nlinarith

private lemma partial_bound (ν : ℝ) (hν : 0 < ν) (T : ℕ) :
    ∀ N : ℕ, N + 1 ≤ T →
      ∑ n ∈ Finset.range (N + 1), Real.sqrt (1 / (ν + n) - 1 / (ν + T)) ≤
        1 / Real.sqrt ν + (2 * Real.sqrt (N : ℝ) - (N : ℝ) * Real.sqrt (N : ℝ) / (3 * T)) := by
  intro N
  induction N with
  | zero =>
    intro _
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, add_zero,
      Real.sqrt_zero, mul_zero, zero_div, sub_zero]
    rw [one_div (Real.sqrt ν), ← Real.sqrt_inv, ← one_div]
    apply Real.sqrt_le_sqrt
    have : (0 : ℝ) ≤ 1 / (ν + T) := by positivity
    linarith
  | succ N ih =>
    intro hN
    have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    rw [Finset.sum_range_succ]
    have h1 := ih (by omega)
    have h2 := g_le_f ν hν T (N + 1) (by omega) (by omega)
    have h3 := step_D (T : ℝ) hT N
    push_cast at h1 h2 h3 ⊢
    linarith

private lemma arm_bound2 (ν : ℝ) (hν : 0 < ν) (T : ℕ) (N : ℕ) (hNT : N ≤ T) :
    ∑ n ∈ Finset.range N, Real.sqrt (1 / (ν + n) - 1 / (ν + T)) ≤
      1 / Real.sqrt ν + (2 * Real.sqrt (N : ℝ) - (N : ℝ) * Real.sqrt (N : ℝ) / (3 * T)) := by
  rcases N with _ | M
  · simp
  · have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    have h1 := partial_bound ν hν T M hNT
    have h2 := step_D (T : ℝ) hT M
    have h3 := f_nonneg T (M + 1) (by omega) hNT
    push_cast at h1 h2 h3 ⊢
    linarith

private lemma pullCount_le {K T : ℕ} (s : Fin T → Fin K) (a : Fin K) : pullCount s a ≤ T := by
  unfold pullCount
  calc (Finset.univ.filter fun t : Fin T => s t = a).card ≤ (Finset.univ : Finset (Fin T)).card :=
        Finset.card_filter_le _ _
    _ = T := by simp

private lemma tangent (x m : ℝ) (hx : 0 ≤ x) (hm : 0 ≤ m) :
    m * Real.sqrt m + 3 / 2 * Real.sqrt m * (x - m) ≤ x * Real.sqrt x := by
  set p := Real.sqrt x
  set q := Real.sqrt m
  have hp2 : p ^ 2 = x := Real.sq_sqrt hx
  have hq2 : q ^ 2 = m := Real.sq_sqrt hm
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  rw [← hp2, ← hq2]
  nlinarith [mul_nonneg (sq_nonneg (p - q)) (show 0 ≤ p + q / 2 by linarith)]

theorem solution_aux {K : ℕ} [NeZero K] (T : ℕ) (hT : 1 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (s : Fin T → Fin K) :
    ∑ t, Real.sqrt (1 / (ν + pullsBefore s t (s t)) - 1 / (ν + T)) ≤
      (K : ℝ) / Real.sqrt ν + 2 * Real.sqrt ((K : ℝ) * T)
        - (1 / 3) * Real.sqrt ((T : ℝ) / K) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hK : (0 : ℝ) < K := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne K))
  rw [sum_regroup s (fun _ n => Real.sqrt (1 / (ν + n) - 1 / (ν + T)))]
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ (Finset.univ : Finset (Fin K))) =>
    arm_bound2 ν hν T (pullCount s a) (pullCount_le s a)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div] at hsum
  have hcs := cs_bound s
  set m : ℝ := (T : ℝ) / K
  have hm : 0 ≤ m := by positivity
  have htan := Finset.sum_le_sum fun a (_ : a ∈ (Finset.univ : Finset (Fin K))) =>
    tangent (pullCount s a : ℝ) m (Nat.cast_nonneg _) hm
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, sum_pullCount] at htan
  have hKm : (K : ℝ) * m = T := by simp only [m]; field_simp
  have hlow : (T : ℝ) * Real.sqrt m ≤ ∑ a, (pullCount s a : ℝ) * Real.sqrt (pullCount s a) := by
    have : (K : ℝ) * (m * Real.sqrt m) + 3 / 2 * Real.sqrt m * ((T : ℝ) - K * m) =
        (T : ℝ) * Real.sqrt m := by
      rw [show (K : ℝ) * (m * Real.sqrt m) = (K * m) * Real.sqrt m by ring, hKm]; ring
    linarith
  have hdiv : (T : ℝ) * Real.sqrt m / (3 * T) ≤
      (∑ a, (pullCount s a : ℝ) * Real.sqrt (pullCount s a)) / (3 * T) :=
    div_le_div_of_nonneg_right hlow (by positivity)
  have e : (T : ℝ) * Real.sqrt m / (3 * T) = 1 / 3 * Real.sqrt m := by field_simp
  rw [e] at hdiv
  have e2 : (K : ℝ) * (1 / Real.sqrt ν) = K / Real.sqrt ν := mul_one_div _ _
  linarith

end InfoRelaxTS.Gap

open InfoRelaxTS.Gap in
theorem solution {K : ℕ} [NeZero K] (T : ℕ) (hT : 1 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (s : Fin T → Fin K) :
    ∑ t, Real.sqrt (1 / (ν + pullsBefore s t (s t)) - 1 / (ν + T)) ≤
      (K : ℝ) / Real.sqrt ν + 2 * Real.sqrt ((K : ℝ) * T)
        - (1 / 3) * Real.sqrt ((T : ℝ) / K) :=
  InfoRelaxTS.Gap.solution_aux T hT ν hν s
