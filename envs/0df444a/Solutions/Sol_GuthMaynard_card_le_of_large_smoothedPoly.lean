-- Prove2me | solution 1 for GuthMaynard.card_le_of_large_smoothedPoly
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:32:42.625656+00:00
-- url     : https://prove2.me/submissions/406587cc-ac59-4cc5-9487-cab6fd318a9c

import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_norm_S_one_le
import Theorems.Thm_GuthMaynard_norm_S_two_le
import Theorems.Thm_GuthMaynard_norm_S_three_le
import Theorems.Thm_GuthMaynard_card_le_of_large_smoothedPoly_Iterm_pos
import Mathlib

section
section
namespace GuthMaynardGoal

open GuthMaynard

lemma card_filter_pos_of_ne_zero (m : Fin 3 → ℤ) (hm : m ≠ 0) :
    (Finset.univ.filter fun i => m i ≠ 0).card = 1 ∨
    (Finset.univ.filter fun i => m i ≠ 0).card = 2 ∨
    (Finset.univ.filter fun i => m i ≠ 0).card = 3 := by
  have h1 : 0 < (Finset.univ.filter fun i => m i ≠ 0).card := by
    apply Finset.card_pos.2
    by_contra h
    apply hm
    funext i
    by_contra hi
    exact h ⟨i, by simpa using hi⟩
  have h2 : (Finset.univ.filter fun i => m i ≠ 0).card ≤ 3 := by
    calc _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_univ _
      _ = 3 := by simp
  omega

lemma norm_tsum_ne_zero_le (f : (Fin 3 → ℤ) → ℂ) :
    ‖∑' m : {m : Fin 3 → ℤ // m ≠ 0}, f m‖ ≤
      ‖∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 1}, f m‖ +
      ‖∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 2}, f m‖ +
      ‖∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 3}, f m‖ := by
  by_cases hs : Summable (fun m : {m : Fin 3 → ℤ // m ≠ 0} => f m)
  · set A : Set (Fin 3 → ℤ) := {m | m ≠ 0} with hA
    set B : ℕ → Set (Fin 3 → ℤ) := fun k => {m | (Finset.univ.filter fun i => m i ≠ 0).card = k} with hB
    have hsA : Summable (A.indicator f) := (summable_subtype_iff_indicator).1 hs
    have hBA : ∀ k, k ≠ 0 → B k ⊆ A := by
      intro k hk m hm
      simp only [hB, hA, Set.mem_ofPred_eq] at hm ⊢
      rintro rfl
      simp at hm
      exact hk hm.symm
    have hsB : ∀ k, k ≠ 0 → Summable ((B k).indicator f) := by
      intro k hk
      have h : (B k).indicator f = (B k).indicator (A.indicator f) := by
        funext m
        by_cases hm : m ∈ B k
        · simp [Set.indicator_of_mem hm, Set.indicator_of_mem (hBA k hk hm)]
        · simp [Set.indicator_of_notMem hm]
      rw [h]
      exact hsA.indicator _
    have hsum : A.indicator f = ∑ k ∈ ({1, 2, 3} : Finset ℕ), (B k).indicator f := by
      funext m
      simp only [Finset.sum_apply]
      by_cases hm : m ∈ A
      · rw [Set.indicator_of_mem hm]
        have hm' : m ≠ 0 := hm
        rcases card_filter_pos_of_ne_zero m hm' with h | h | h <;>
          simp [Set.indicator, hB, h]
      · have hm0 : m = 0 := by simpa [hA] using hm
        subst hm0
        simp [Set.indicator, hB]
        intro h
        exact absurd h hm
    have e1 : ∀ k, ∑' m : B k, f m = ∑' m, (B k).indicator f m := fun k => tsum_subtype (B k) f
    have e0 : ∑' m : A, f m = ∑' m, A.indicator f m := tsum_subtype A f
    show ‖∑' m : A, f m‖ ≤ ‖∑' m : B 1, f m‖ + ‖∑' m : B 2, f m‖ + ‖∑' m : B 3, f m‖
    rw [e0, e1, e1, e1, hsum]
    have := Summable.tsum_finsetSum (s := ({1, 2, 3} : Finset ℕ)) (f := fun k m => (B k).indicator f m)
      (fun k hk => hsB k (by simp at hk; omega))
    simp only [Finset.sum_apply]
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    simp [Finset.sum_insert, add_assoc]
  · rw [tsum_eq_zero_of_not_summable hs]
    simp only [norm_zero]
    positivity

end GuthMaynardGoal

end
end

section
section
namespace GuthMaynardGoal

lemma eq_of_log_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Real.log a = Real.log b) : a = b :=
  Real.log_injOn_pos ha hb h

lemma term_bound {N X x0 q e p c : ℝ} (hN : 1 ≤ N) (hX : N ^ x0 ≤ X) (hp : p ≤ 3)
    (hc : q + e + x0 * (p - 3) ≤ c) : N ^ q * (N ^ e * X ^ p) ≤ X ^ (3:ℝ) * N ^ c := by
  have hN0 : 0 < N := by linarith
  have hNx : 0 < N ^ x0 := Real.rpow_pos_of_pos hN0 _
  have hX0 : 0 < X := lt_of_lt_of_le hNx hX
  have h1 : X ^ p = X ^ (3:ℝ) * X ^ (p - 3) := by
    rw [← Real.rpow_add hX0]; congr 1; ring
  have h2 : X ^ (p - 3) ≤ N ^ (x0 * (p - 3)) := by
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow_of_nonpos hNx hX (by linarith)
  have h3 : N ^ q * (N ^ e * X ^ p) = X ^ (3:ℝ) * (N ^ (q + e) * X ^ (p - 3)) := by
    rw [h1, Real.rpow_add hN0]; ring
  rw [h3]
  have h4 : N ^ (q + e) * X ^ (p - 3) ≤ N ^ (q + e) * N ^ (x0 * (p - 3)) :=
    mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN0.le _)
  have h5 : N ^ (q + e) * N ^ (x0 * (p - 3)) ≤ N ^ c := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h6 : 0 ≤ X ^ (3:ℝ) := Real.rpow_nonneg hX0.le _
  exact mul_le_mul_of_nonneg_left (h4.trans h5) h6


/-- The bound on `‖S₁‖ + ‖S₂‖ + ‖S₃‖` assembled from Props 5.1, 6.1 (`k = 4`), 11.2. -/
noncomputable def Sm (C1 C2 C3 δ T N X s : ℝ) : ℝ :=
  C1 * T ^ (-10 : ℝ) +
  C2 * T ^ δ * (N ^ 2 * X ^ 2 + T * N * X ^ (2 - 1 / ((4:ℕ):ℝ)) +
    N ^ 2 * X ^ 2 * (T ^ (1 / 2 : ℝ) / X ^ (3 / 4 : ℝ)) ^ (1 / ((4:ℕ):ℝ))) +
  C3 * T ^ δ * (T ^ 2 * X ^ (3 / 2 : ℝ) + T * X * N ^ (3 - 2 * s) +
    T * X ^ 2 * N ^ (3 / 2 - s) + T ^ (9 / 8 : ℝ) * X ^ (29 / 16 : ℝ) * N ^ (3 / 2 - s))

lemma Sm_nonneg {C1 C2 C3 δ T N X s : ℝ} (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) (h3 : 0 ≤ C3)
    (hT : 0 < T) (hN : 0 < N) (hX : 0 < X) : 0 ≤ Sm C1 C2 C3 δ T N X s := by
  unfold Sm; positivity


set_option maxHeartbeats 1600000 in
lemma Sm_bound {C1 C2 C3 δ N X σ T : ℝ} (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) (h3 : 0 ≤ C3)
    (hδ : 0 < δ) (hN : 1 < N) (hT : T = N ^ (6 / 5 : ℝ)) (hσ : 7 / 10 ≤ σ) (hσ' : σ ≤ 4 / 5)
    (hX : N ^ (18 / 5 - 4 * σ + δ) ≤ X) :
    N ^ (3 - 6 * (σ - δ / 100)) * Sm C1 C2 C3 (δ / 100) T N X (σ - δ / 100) ≤
      X ^ (3:ℝ) * N ^ (-δ / 2) * (C1 + 3 * C2 + 4 * C3) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := hN.le
  have hXp : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hX
  have hTp : 0 < T := by rw [hT]; positivity
  set q := 3 - 6 * (σ - δ / 100) with hq
  set x0 := 18 / 5 - 4 * σ + δ with hx0
  have e1 : T ^ (-10 : ℝ) = N ^ (-12 : ℝ) * X ^ (0:ℝ) := by
    subst hT; simp only [Real.rpow_zero, mul_one]; rw [← Real.rpow_mul hN0.le]; norm_num
  have e2 : T ^ (δ / 100) * (N ^ 2 * X ^ 2) = N ^ (2 + 6 / 5 * (δ / 100)) * X ^ (2:ℝ) := by
    subst hT
    apply eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
    push_cast
    ring
  have e3 : T ^ (δ / 100) * (T * N * X ^ (2 - 1 / ((4:ℕ):ℝ))) =
      N ^ (6 / 5 + 1 + 6 / 5 * (δ / 100)) * X ^ (7 / 4 : ℝ) := by
    subst hT
    apply eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
    push_cast
    ring
  have e4 : T ^ (δ / 100) * (N ^ 2 * X ^ 2 * (T ^ (1 / 2 : ℝ) / X ^ (3 / 4 : ℝ)) ^ (1 / ((4:ℕ):ℝ))) =
      N ^ (2 + 3 / 20 + 6 / 5 * (δ / 100)) * X ^ (29 / 16 : ℝ) := by
    subst hT
    apply eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
    push_cast
    ring
  have e5 : T ^ (δ / 100) * (T ^ 2 * X ^ (3 / 2 : ℝ)) =
      N ^ (12 / 5 + 6 / 5 * (δ / 100)) * X ^ (3 / 2 : ℝ) := by
    subst hT
    apply eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
    push_cast
    ring
  have e6 : T ^ (δ / 100) * (T * X * N ^ (3 - 2 * (σ - δ / 100))) =
      N ^ (6 / 5 + (3 - 2 * (σ - δ / 100)) + 6 / 5 * (δ / 100)) * X ^ (1:ℝ) := by
    subst hT
    apply eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
    push_cast
    ring
  have e7 : T ^ (δ / 100) * (T * X ^ 2 * N ^ (3 / 2 - (σ - δ / 100))) =
      N ^ (6 / 5 + (3 / 2 - (σ - δ / 100)) + 6 / 5 * (δ / 100)) * X ^ (2:ℝ) := by
    subst hT
    apply eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
    push_cast
    ring
  have e8 : T ^ (δ / 100) * (T ^ (9 / 8 : ℝ) * X ^ (29 / 16 : ℝ) * N ^ (3 / 2 - (σ - δ / 100))) =
      N ^ (27 / 20 + (3 / 2 - (σ - δ / 100)) + 6 / 5 * (δ / 100)) * X ^ (29 / 16 : ℝ) := by
    subst hT
    apply eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
    push_cast
    ring
  have b1 : N ^ q * (N ^ (-12:ℝ) * X ^ (0:ℝ)) ≤ X ^ (3:ℝ) * N ^ (-δ / 2) :=
    term_bound hN1 hX (by norm_num) (by rw [hq, hx0]; nlinarith)
  have b2 := term_bound (q := q) (c := -δ / 2) hN1 hX (p := 2) (e := 2 + 6 / 5 * (δ / 100)) (by norm_num)
    (by rw [hq, hx0]; nlinarith)
  have b3 := term_bound (q := q) (c := -δ / 2) hN1 hX (p := 7 / 4) (e := 6 / 5 + 1 + 6 / 5 * (δ / 100)) (by norm_num)
    (by rw [hq, hx0]; nlinarith)
  have b4 := term_bound (q := q) (c := -δ / 2) hN1 hX (p := 29 / 16) (e := 2 + 3 / 20 + 6 / 5 * (δ / 100)) (by norm_num)
    (by rw [hq, hx0]; nlinarith)
  have b5 := term_bound (q := q) (c := -δ / 2) hN1 hX (p := 3 / 2) (e := 12 / 5 + 6 / 5 * (δ / 100)) (by norm_num)
    (by rw [hq, hx0]; nlinarith)
  have b6 := term_bound (q := q) (c := -δ / 2) hN1 hX (p := 1) (e := 6 / 5 + (3 - 2 * (σ - δ / 100)) + 6 / 5 * (δ / 100)) (by norm_num)
    (by rw [hq, hx0]; nlinarith)
  have b7 := term_bound (q := q) (c := -δ / 2) hN1 hX (p := 2) (e := 6 / 5 + (3 / 2 - (σ - δ / 100)) + 6 / 5 * (δ / 100)) (by norm_num)
    (by rw [hq, hx0]; nlinarith)
  have b8 := term_bound (q := q) (c := -δ / 2) hN1 hX (p := 29 / 16) (e := 27 / 20 + (3 / 2 - (σ - δ / 100)) + 6 / 5 * (δ / 100)) (by norm_num)
    (by rw [hq, hx0]; nlinarith)
  rw [← e2] at b2
  rw [← e3] at b3
  rw [← e4] at b4
  rw [← e5] at b5
  rw [← e6] at b6
  rw [← e7] at b7
  rw [← e8] at b8
  rw [← e1] at b1
  unfold Sm
  have hq0 : 0 ≤ N ^ q := Real.rpow_nonneg hN0.le _
  have : N ^ q * (C1 * T ^ (-10 : ℝ) +
      C2 * T ^ (δ / 100) * (N ^ 2 * X ^ 2 + T * N * X ^ (2 - 1 / ((4:ℕ):ℝ)) +
        N ^ 2 * X ^ 2 * (T ^ (1 / 2 : ℝ) / X ^ (3 / 4 : ℝ)) ^ (1 / ((4:ℕ):ℝ))) +
      C3 * T ^ (δ / 100) * (T ^ 2 * X ^ (3 / 2 : ℝ) + T * X * N ^ (3 - 2 * (σ - δ / 100)) +
        T * X ^ 2 * N ^ (3 / 2 - (σ - δ / 100)) + T ^ (9 / 8 : ℝ) * X ^ (29 / 16 : ℝ) * N ^ (3 / 2 - (σ - δ / 100)))) =
      C1 * (N ^ q * T ^ (-10:ℝ)) + C2 * (N ^ q * (T ^ (δ / 100) * (N ^ 2 * X ^ 2))
        + N ^ q * (T ^ (δ / 100) * (T * N * X ^ (2 - 1 / ((4:ℕ):ℝ))))
        + N ^ q * (T ^ (δ / 100) * (N ^ 2 * X ^ 2 * (T ^ (1 / 2 : ℝ) / X ^ (3 / 4 : ℝ)) ^ (1 / ((4:ℕ):ℝ)))))
      + C3 * (N ^ q * (T ^ (δ / 100) * (T ^ 2 * X ^ (3 / 2 : ℝ)))
        + N ^ q * (T ^ (δ / 100) * (T * X * N ^ (3 - 2 * (σ - δ / 100))))
        + N ^ q * (T ^ (δ / 100) * (T * X ^ 2 * N ^ (3 / 2 - (σ - δ / 100))))
        + N ^ q * (T ^ (δ / 100) * (T ^ (9 / 8 : ℝ) * X ^ (29 / 16 : ℝ) * N ^ (3 / 2 - (σ - δ / 100))))) := by
    ring
  rw [this]
  have hu : 0 ≤ X ^ (3:ℝ) * N ^ (-δ / 2) := by positivity
  linarith [mul_le_mul_of_nonneg_left b1 h1, mul_le_mul_of_nonneg_left b2 h2, mul_le_mul_of_nonneg_left b3 h2,
    mul_le_mul_of_nonneg_left b4 h2, mul_le_mul_of_nonneg_left b5 h3, mul_le_mul_of_nonneg_left b6 h3,
    mul_le_mul_of_nonneg_left b7 h3, mul_le_mul_of_nonneg_left b8 h3]


lemma core {C1 C2 C3 C4 δ : ℝ} (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) (h3 : 0 ≤ C3) (h4 : 0 ≤ C4)
    (hδ : 0 < δ) :
    ∃ N₀ : ℝ, 1 < N₀ ∧ ∀ N X σ T : ℝ, N₀ ≤ N → T = N ^ (6 / 5 : ℝ) → 7 / 10 ≤ σ → σ ≤ 4 / 5 → 0 ≤ X →
      X ≤ C4 * (N ^ (2 - 2 * (σ - δ / 100)) + N ^ (1 - 2 * (σ - δ / 100)) *
        (Sm C1 C2 C3 (δ / 100) T N X (σ - δ / 100)) ^ (1 / 3 : ℝ)) →
      X ≤ N ^ (18 / 5 - 4 * σ + δ) := by
  have hd2 : 0 < δ / 2 := by linarith
  have ev1 : ∀ᶠ N : ℝ in Filter.atTop, 2 * C4 + 1 ≤ N ^ (δ / 2) :=
    (tendsto_rpow_atTop hd2).eventually_ge_atTop _
  have ev2 : ∀ᶠ N : ℝ in Filter.atTop, 8 * C4 ^ 3 * (C1 + 3 * C2 + 4 * C3) + 1 ≤ N ^ (δ / 2) :=
    (tendsto_rpow_atTop hd2).eventually_ge_atTop _
  have ev3 : ∀ᶠ N : ℝ in Filter.atTop, 2 ≤ N := Filter.eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (ev1.and (ev2.and ev3))
  refine ⟨N₀, ?_, ?_⟩
  · have := (hN₀ N₀ le_rfl).2.2; linarith
  intro N X σ T hN hT hσ hσ' hX0 hX
  obtain ⟨hA, hB, hC⟩ := hN₀ N hN
  have hN1 : 1 < N := by linarith
  have hN0 : 0 < N := by linarith
  by_contra hlt
  push_neg at hlt
  have hXp : 0 < X := lt_trans (Real.rpow_pos_of_pos hN0 _) hlt
  have hTp : 0 < T := by rw [hT]; positivity
  set s := σ - δ / 100 with hs
  set Sm' := Sm C1 C2 C3 (δ / 100) T N X s with hSm
  have hSm0 : 0 ≤ Sm' := Sm_nonneg h1 h2 h3 hTp hN0 hXp
  set P := N ^ (2 - 2 * s) with hP
  set Q := N ^ (1 - 2 * s) with hQ
  have hP0 : 0 < P := Real.rpow_pos_of_pos hN0 _
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hN0 _
  set c := Sm' ^ (1 / 3 : ℝ) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hSm0 _
  have hc3 : c ^ 3 = Sm' := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hSm0]; norm_num
  have hN_half : 0 < N ^ (δ / 2) := Real.rpow_pos_of_pos hN0 _
  by_cases hcase : Q * c ≤ P
  · -- first term dominates
    have hX1 : X ≤ 2 * C4 * P := by nlinarith [mul_nonneg h4 hc0, mul_pos hQ0 hXp]
    have hPN : P * N ^ (δ / 2) ≤ N ^ (18 / 5 - 4 * σ + δ) := by
      rw [hP, ← Real.rpow_add hN0]
      apply Real.rpow_le_rpow_of_exponent_le hN1.le
      rw [hs]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hA hP0.le]
  · push_neg at hcase
    have hX2 : X ≤ 2 * C4 * (Q * c) := by nlinarith [mul_nonneg h4 hc0, mul_pos hQ0 hXp]
    have hX3 : X ^ 3 ≤ 8 * C4 ^ 3 * (Q ^ 3 * Sm') := by
      have := pow_le_pow_left₀ hXp.le hX2 3
      calc X ^ 3 ≤ (2 * C4 * (Q * c)) ^ 3 := this
        _ = 8 * C4 ^ 3 * (Q ^ 3 * c ^ 3) := by ring
        _ = _ := by rw [hc3]
    have hQ3 : Q ^ 3 = N ^ (3 - 6 * s) := by
      rw [hQ, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have hbound := Sm_bound (C1 := C1) (C2 := C2) (C3 := C3) h1 h2 h3 hδ hN1 hT hσ hσ' hlt.le
    rw [← hs, ← hSm, ← hQ3] at hbound
    have hX3' : X ^ 3 = X ^ (3:ℝ) := by rw [← Real.rpow_natCast]; norm_num
    have hXp3 : 0 < X ^ (3:ℝ) := Real.rpow_pos_of_pos hXp _
    have hr : 0 < N ^ (-δ / 2) := Real.rpow_pos_of_pos hN0 _
    have hrr : N ^ (-δ / 2) * N ^ (δ / 2) = 1 := by
      rw [← Real.rpow_add hN0, show -δ / 2 + δ / 2 = 0 by ring, Real.rpow_zero]
    have hK : 0 ≤ C1 + 3 * C2 + 4 * C3 := by linarith
    -- X^3 ≤ 8 C4^3 * X^3 * N^{-δ/2} * K
    have hfin : X ^ (3:ℝ) ≤ 8 * C4 ^ 3 * (X ^ (3:ℝ) * N ^ (-δ / 2) * (C1 + 3 * C2 + 4 * C3)) := by
      rw [← hX3'] at hbound ⊢
      calc X ^ 3 ≤ 8 * C4 ^ 3 * (Q ^ 3 * Sm') := hX3
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)
    -- K' := 8 C4^3 K ≤ N^{δ/2} - 1
    have hK' : 8 * C4 ^ 3 * (C1 + 3 * C2 + 4 * C3) * N ^ (-δ / 2) < 1 := by
      have : 8 * C4 ^ 3 * (C1 + 3 * C2 + 4 * C3) * N ^ (-δ / 2) ≤ (N ^ (δ / 2) - 1) * N ^ (-δ / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hr.le
      nlinarith
    have : X ^ (3:ℝ) * (8 * C4 ^ 3 * (C1 + 3 * C2 + 4 * C3) * N ^ (-δ / 2)) < X ^ (3:ℝ) * 1 :=
      mul_lt_mul_of_pos_left hK' hXp3
    nlinarith

end GuthMaynardGoal

end
end

section
section
namespace GuthMaynardGoal

open GuthMaynard

theorem card_le_of_large_smoothedPoly_dev (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ σ : ℝ, σ ∈ Set.Icc (7 / 10 : ℝ) (8 / 10) →
      ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) → ∀ (W : Finset ℝ) (a : ℝ),
      IsSeparated (((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + (N : ℝ) ^ (6 / 5 : ℝ))) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedPoly w N b t‖) →
      (W.card : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5 + δ) := by
  intro δ hδ
  obtain ⟨C4, hC4⟩ := card_le_of_large_smoothedPoly_Iterm_pos w hw ε hε
  obtain ⟨C1, hC1⟩ := norm_S_one_le w hw ε hε
  have hd : 0 < δ / 100 := by positivity
  obtain ⟨C2, T2, hC2⟩ := norm_S_two_le w hw ε hε 4 (by norm_num) (δ / 100) hd
  obtain ⟨C3, T3, hC3⟩ := norm_S_three_le w hw ε hε (δ / 100) hd
  obtain ⟨N₀', hN₀'1, hcore⟩ := core (C1 := max C1 0) (C2 := max C2 0) (C3 := max C3 0)
    (C4 := |C4|) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (abs_nonneg _) hδ
  have ev1 : ∀ᶠ N : ℕ in Filter.atTop, N₀' ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have ev2 : ∀ᶠ N : ℕ in Filter.atTop, max T2 T3 ≤ (N : ℝ) ^ (6 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 6 / 5)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (ev1.and ev2)
  refine ⟨N₀, ?_⟩
  intro N hN σ hσ b hb W a hsep hwin hD
  obtain ⟨hNr, hTT⟩ := hN₀ N hN
  have hN1 : 1 < (N : ℝ) := lt_of_lt_of_le hN₀'1 hNr
  have hN0 : 0 < (N : ℝ) := by linarith
  set Nr : ℝ := (N : ℝ) with hNr_def
  set T : ℝ := Nr ^ (6 / 5 : ℝ) with hT
  have hTp : 0 < T := by positivity
  have hT2 : T2 ≤ T := le_trans (le_max_left _ _) hTT
  have hT3 : T3 ≤ T := le_trans (le_max_right _ _) hTT
  have hmem : Nr ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T := by
    constructor
    · rw [hT, ← Real.rpow_mul hN0.le]
      calc Nr ^ (6 / 5 * (3 / 4) : ℝ) ≤ Nr ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
        _ = Nr := Real.rpow_one _
    · calc Nr = Nr ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ T := Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
  set σ' : ℝ := σ - δ / 100 with hσ'
  have hlt : Nr ^ σ' < Nr ^ σ := Real.rpow_lt_rpow_of_exponent_lt hN1 (by rw [hσ']; linarith)
  have hD1 : ∀ t ∈ W, Nr ^ σ' < ‖smoothedPoly w N b t‖ := fun t ht => lt_of_lt_of_le hlt (hD t ht)
  have hD2 : ∀ t ∈ W, Nr ^ σ' ≤ ‖smoothedPoly w N b t‖ := fun t ht => (hD1 t ht).le
  have h46 := hC4 T N hmem σ' b hb W a hsep hwin hD1
  have h51 := hC1 T N hmem W a hsep hwin
  have h61 := hC2 T hT2 N hmem W a hsep hwin
  have h111 := hC3 T hT3 N hmem σ' b hb W a hsep hwin hD2
  have hX0 : (0:ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hE2 : 0 ≤ (Nr ^ 2 * (W.card : ℝ) ^ 2 + T * Nr * (W.card : ℝ) ^ (2 - 1 / ((4:ℕ):ℝ)) +
      Nr ^ 2 * (W.card : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / ((4:ℕ):ℝ))) := by
    positivity
  have hE3 : 0 ≤ (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) + T * (W.card : ℝ) * Nr ^ (3 - 2 * σ') +
      T * (W.card : ℝ) ^ 2 * Nr ^ (3 / 2 - σ') +
      T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * Nr ^ (3 / 2 - σ')) := by
    positivity
  have m1 : ‖S 1 w N W‖ ≤ max C1 0 * T ^ (-10 : ℝ) :=
    h51.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hTp.le _))
  have m2 : ‖S 2 w N W‖ ≤ max C2 0 * T ^ (δ / 100) * (Nr ^ 2 * (W.card : ℝ) ^ 2 +
      T * Nr * (W.card : ℝ) ^ (2 - 1 / ((4:ℕ):ℝ)) +
      Nr ^ 2 * (W.card : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / ((4:ℕ):ℝ))) :=
    h61.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hTp.le _)) hE2)
  have m3 : ‖S 3 w N W‖ ≤ max C3 0 * T ^ (δ / 100) * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
      T * (W.card : ℝ) * Nr ^ (3 - 2 * σ') +
      T * (W.card : ℝ) ^ 2 * Nr ^ (3 / 2 - σ') +
      T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * Nr ^ (3 / 2 - σ')) :=
    h111.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hTp.le _)) hE3)
  have hnorm : ‖∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm w N W m‖ ≤
      Sm (max C1 0) (max C2 0) (max C3 0) (δ / 100) T Nr (W.card : ℝ) σ' := by
    refine (norm_tsum_ne_zero_le (Iterm w N W)).trans ?_
    unfold Sm
    have e1 : S 1 w N W = ∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 1}, Iterm w N W m := rfl
    have e2 : S 2 w N W = ∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 2}, Iterm w N W m := rfl
    have e3 : S 3 w N W = ∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 3}, Iterm w N W m := rfl
    rw [← e1, ← e2, ← e3]
    linarith
  simp only at h46
  set Sm' := Sm (max C1 0) (max C2 0) (max C3 0) (δ / 100) T Nr (W.card : ℝ) σ' with hSm'
  have hSm0 : 0 ≤ Sm' := (norm_nonneg _).trans hnorm
  set s : ℝ := (∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm w N W m).re with hs
  have hsle : |s| ≤ Sm' := (Complex.abs_re_le_norm _).trans hnorm
  have hc : |max s 0 ^ (1 / 3 : ℝ)| ≤ Sm' ^ (1 / 3 : ℝ) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
    exact Real.rpow_le_rpow (le_max_right _ _) (max_le ((le_abs_self s).trans hsle) hSm0) (by norm_num)
  have hQ : 0 ≤ Nr ^ (1 - 2 * σ') := Real.rpow_nonneg hN0.le _
  have hP : 0 ≤ Nr ^ (2 - 2 * σ') := Real.rpow_nonneg hN0.le _
  have hineq : (W.card : ℝ) ≤ |C4| * (Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * Sm' ^ (1 / 3 : ℝ)) := by
    refine h46.trans ?_
    set c := max s 0 ^ (1 / 3 : ℝ)
    calc C4 * (Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * c)
        ≤ |C4 * (Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * c)| := le_abs_self _
      _ = |C4| * |Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * c| := abs_mul _ _
      _ ≤ |C4| * (Nr ^ (2 - 2 * σ') + Nr ^ (1 - 2 * σ') * Sm' ^ (1 / 3 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg hP, abs_mul, abs_of_nonneg hQ]
        have := mul_le_mul_of_nonneg_left hc hQ
        linarith
  have hfin := hcore Nr (W.card : ℝ) σ T hNr hT hσ.1 (by linarith [hσ.2]) hX0 hineq
  calc (W.card : ℝ) ≤ Nr ^ (18 / 5 - 4 * σ + δ) := hfin
    _ = Nr ^ (6 / 5 : ℝ) * Nr ^ ((12 - 20 * σ) / 5 + δ) := by
      rw [← Real.rpow_add hN0]; congr 1; ring

end GuthMaynardGoal

end
end

section
open GuthMaynard

theorem solution (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ σ : ℝ, σ ∈ Set.Icc (7 / 10 : ℝ) (8 / 10) →
      ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) → ∀ (W : Finset ℝ) (a : ℝ),
      IsSeparated (((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + (N : ℝ) ^ (6 / 5 : ℝ))) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedPoly w N b t‖) →
      (W.card : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5 + δ) := by
  apply GuthMaynardGoal.card_le_of_large_smoothedPoly_dev <;> assumption

end
