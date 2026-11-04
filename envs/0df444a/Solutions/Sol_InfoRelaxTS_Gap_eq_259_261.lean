-- Prove2me | solution 1 for InfoRelaxTS.Gap.eq_259_261
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:07:57.070221+00:00
-- url     : https://prove2.me/submissions/3b9be06f-3fb2-4ae5-ab58-48c27bfe8c5b

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

private lemma arm_bound (L ν : ℝ) (hL : 0 ≤ L) (hν : 0 < ν) (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.sqrt (L / (ν + n)) ≤
      Real.sqrt L / Real.sqrt ν + 2 * Real.sqrt L * Real.sqrt N := by
  have hterm : ∀ n : ℕ, Real.sqrt (L / (ν + n)) = Real.sqrt L * (1 / Real.sqrt (ν + n)) := by
    intro n
    rw [Real.sqrt_div hL, mul_one_div]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hsL := Real.sqrt_nonneg L
  rcases N with _ | N
  · simp only [Finset.range_zero, Finset.sum_empty, mul_zero, CharP.cast_eq_zero,
      Real.sqrt_zero, add_zero]
    positivity
  · have h := sum_inv_sqrt_le ν hν N
    have hmono : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    calc Real.sqrt L * ∑ n ∈ Finset.range (N + 1), 1 / Real.sqrt (ν + n)
        ≤ Real.sqrt L * (1 / Real.sqrt ν + 2 * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h hsL
      _ ≤ Real.sqrt L / Real.sqrt ν + 2 * Real.sqrt L * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
          rw [mul_add, mul_one_div]
          nlinarith

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

theorem solution_aux {K : ℕ} (T : ℕ) (L ν : ℝ) (hL : 0 ≤ L) (hν : 0 < ν) (s : Fin T → Fin K) :
    ∑ t, Real.sqrt (L / (ν + pullsBefore s t (s t))) ≤
        (K : ℝ) * Real.sqrt L / Real.sqrt ν + 2 * Real.sqrt L * ∑ a, Real.sqrt (pullCount s a) ∧
      ∑ a, Real.sqrt (pullCount s a) ≤ Real.sqrt ((K : ℝ) * T) := by
  refine ⟨?_, cs_bound s⟩
  rw [sum_regroup s (fun _ n => Real.sqrt (L / (ν + n)))]
  calc ∑ a, ∑ n ∈ Finset.range (pullCount s a), Real.sqrt (L / (ν + n))
      ≤ ∑ a : Fin K, (Real.sqrt L / Real.sqrt ν + 2 * Real.sqrt L * Real.sqrt (pullCount s a)) :=
        Finset.sum_le_sum fun a _ => arm_bound L ν hL hν _
    _ = (K : ℝ) * Real.sqrt L / Real.sqrt ν + 2 * Real.sqrt L * ∑ a, Real.sqrt (pullCount s a) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring

end InfoRelaxTS.Gap

open InfoRelaxTS.Gap in
theorem solution {K : ℕ} (T : ℕ) (L ν : ℝ) (hL : 0 ≤ L) (hν : 0 < ν) (s : Fin T → Fin K) :
    ∑ t, Real.sqrt (L / (ν + pullsBefore s t (s t))) ≤
        (K : ℝ) * Real.sqrt L / Real.sqrt ν + 2 * Real.sqrt L * ∑ a, Real.sqrt (pullCount s a) ∧
      ∑ a, Real.sqrt (pullCount s a) ≤ Real.sqrt ((K : ℝ) * T) :=
  InfoRelaxTS.Gap.solution_aux T L ν hL hν s
