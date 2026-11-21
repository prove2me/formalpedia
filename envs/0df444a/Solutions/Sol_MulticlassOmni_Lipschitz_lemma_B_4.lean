-- Prove2me | solution 1 for MulticlassOmni.Lipschitz.lemma_B_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T19:51:02.088277+00:00
-- url     : https://prove2.me/submissions/300c4374-2659-418d-94ce-fa37c199f7b7

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings
import Definitions.Def_MulticlassOmni_Lipschitz_Construction
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses
import Definitions.Def_MulticlassOmni_Lipschitz_StatLowerBound
import Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_3

section
namespace MulticlassOmni.Dev.B3
open MulticlassOmni.Lipschitz

theorem eOne_eq {k : ℕ} (h : 0 < k) : eOne k = Pi.single (⟨0, h⟩ : Fin k) (1:ℝ) := by
  funext y
  by_cases hy : (y : ℕ) = 0
  · have : y = ⟨0, h⟩ := Fin.ext hy
    subst this; simp [eOne]
  · have : y ≠ ⟨0, h⟩ := fun e => hy (by simp [e])
    simp [eOne, hy, Pi.single_apply, this]

theorem dot_eOne {k : ℕ} (h : 0 < k) (v : Fin k → ℝ) : dot (eOne k) v = v ⟨0, h⟩ := by
  rw [eOne_eq h]
  simp only [dot]
  rw [Finset.sum_eq_single (⟨0, h⟩ : Fin k)]
  · simp
  · intro y _ hy; simp [Pi.single_apply, hy]
  · intro hh; exact absurd (Finset.mem_univ _) hh

theorem sum_eOne {k : ℕ} (h : 0 < k) : ∑ y, eOne k y = 1 := by
  rw [eOne_eq h]; simp

end MulticlassOmni.Dev.B3
end

section
namespace MulticlassOmni.Dev.F43
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.B3

variable {k N : ℕ}

end MulticlassOmni.Dev.F43
end

section
namespace MulticlassOmni.Dev.F43
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.B3

variable {k N : ℕ}

theorem delta_e1 (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (j : Fin N) :
    dot (eOne k) (costB x η j - costA k) = 1 + 1 / 256 - (k:ℝ) * x j ⟨0, hk⟩ - 2 * η := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  simp [costB, costA, vbar, dot_eOne hk]
  field_simp
  ring

section gaps
variable (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ)
  (hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k))
  (hsph : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k:ℝ)))
  (hsep : ∀ i j, i ≠ j → dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k:ℝ)))

end gaps

end MulticlassOmni.Dev.F43
end

section
namespace MulticlassOmni.Dev.F43
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.B3

variable {k N : ℕ}

theorem alpha_facts (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 16384)
    (h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ))) (b : Fin 2) (i : Fin N) :
    0 ≤ alpha x η b i ∧ alpha x η b i ≤ 1 ∧
      alpha x η b i * (dot (eOne k) (costB x η i - costA k) + 2 * η) = (3 - 2 * ((b : ℕ) : ℝ)) * η := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx1 : (k:ℝ) * x i ⟨0, hk⟩ ≤ 15 / 16 := by
    have := h1 i ⟨0, hk⟩ rfl
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hDpos : 17 / 256 ≤ dot (eOne k) (costB x η i - costA k) + 2 * η := by
    rw [delta_e1 hk]; linarith
  have hbl : ((b : ℕ) : ℝ) = 0 ∨ ((b : ℕ) : ℝ) = 1 := by
    have := b.isLt
    interval_cases hb : (b : ℕ) <;> simp
  refine ⟨?_, ?_, ?_⟩
  · unfold alpha
    apply div_nonneg
    · rcases hbl with h | h <;> rw [h] <;> nlinarith
    · linarith
  · unfold alpha
    rw [div_le_one (by linarith)]
    rcases hbl with h | h <;> rw [h] <;> nlinarith
  · unfold alpha
    field_simp

end MulticlassOmni.Dev.F43
end

section
noncomputable section

open Classical

namespace MulticlassOmni.Dev.B4
open MulticlassOmni.Lipschitz

/-- The likelihood of a data set `S` under `D_θ^n`. -/
def P {N k n : ℕ} (q : Fin 2 → Fin N → Fin k → ℝ) (θ : Fin N → Fin 2)
    (S : Fin n → Fin N × Fin k) : ℝ :=
  ∏ j, dataDist q θ (S j)

/-- Indicator of the "bad" (success) event `d(t, θ) < N/4`. -/
def ind {N : ℕ} (t θ : Fin N → Fin 2) : ℝ :=
  if (hammingErr t θ : ℝ) < (N : ℝ) / 4 then 1 else 0

/-- Conditional probability (given `θ`, `S`) of the bad event. -/
def G {N k n : ℕ} (est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ)
    (θ : Fin N → Fin 2) (S : Fin n → Fin N × Fin k) : ℝ :=
  ∑ t, est S t * ind t θ

theorem ind_nonneg {N : ℕ} (t θ : Fin N → Fin 2) : 0 ≤ ind t θ := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one {N : ℕ} (t θ : Fin N → Fin 2) : ind t θ ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem G_nonneg {N k n : ℕ} {est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ}
    (hest : IsRandEstimator est) (θ : Fin N → Fin 2) (S : Fin n → Fin N × Fin k) :
    0 ≤ G est θ S :=
  Finset.sum_nonneg fun t _ => mul_nonneg ((hest S).1 t) (ind_nonneg t θ)

theorem G_le_one {N k n : ℕ} {est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ}
    (hest : IsRandEstimator est) (θ : Fin N → Fin 2) (S : Fin n → Fin N × Fin k) :
    G est θ S ≤ 1 := by
  rw [← (hest S).2]
  exact Finset.sum_le_sum fun t _ =>
    mul_le_of_le_one_right ((hest S).1 t) (ind_le_one t θ)

theorem sum_dataDist {N k : ℕ} (hN : 0 < N) (q : Fin 2 → Fin N → Fin k → ℝ)
    (hs : ∀ b i, ∑ y, q b i y = 1) (θ : Fin N → Fin 2) :
    ∑ z, dataDist q θ z = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [Fintype.sum_prod_type]
  simp only [dataDist, ← Finset.sum_div, hs]
  simp
  omega

theorem sum_P {N k n : ℕ} (hN : 0 < N) (q : Fin 2 → Fin N → Fin k → ℝ)
    (hs : ∀ b i, ∑ y, q b i y = 1) (θ : Fin N → Fin 2) :
    ∑ S : Fin n → Fin N × Fin k, P q θ S = 1 := by
  unfold P
  rw [← Fintype.prod_sum (fun (_ : Fin n) (z : Fin N × Fin k) => dataDist q θ z)]
  simp [sum_dataDist hN q hs θ]

theorem fail_eq {N k n : ℕ} (hN : 0 < N) (q : Fin 2 → Fin N → Fin k → ℝ)
    (hs : ∀ b i, ∑ y, q b i y = 1)
    {est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ} (hest : IsRandEstimator est) :
    hammingFailProb q est =
      1 - ∑ θ, ∑ S, (1 / (2 : ℝ) ^ N) * (P q θ S * G est θ S) := by
  have h1 : ∀ θ S, ∑ t, est S t * (if (N : ℝ) / 4 ≤ (hammingErr t θ : ℝ) then 1 else 0)
      = 1 - G est θ S := by
    intro θ S
    unfold G
    conv_rhs => rw [← (hest S).2]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold ind
    by_cases h : (N : ℝ) / 4 ≤ (hammingErr t θ : ℝ)
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  have h2 : ∀ θ, (1 / (2 : ℝ) ^ N) * ∑ S, (∏ j, dataDist q θ (S j)) *
      ∑ t, est S t * (if (N : ℝ) / 4 ≤ (hammingErr t θ : ℝ) then 1 else 0)
      = 1 / (2 : ℝ) ^ N - ∑ S, (1 / (2 : ℝ) ^ N) * (P q θ S * G est θ S) := by
    intro θ
    simp only [h1]
    have : ∑ S : Fin n → Fin N × Fin k, (∏ j, dataDist q θ (S j)) * (1 - G est θ S)
        = 1 - ∑ S, P q θ S * G est θ S := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [show (∑ S : Fin n → Fin N × Fin k, ∏ j, dataDist q θ (S j)) = 1 from sum_P hN q hs θ]
      rfl
    rw [this, ← Finset.mul_sum]
    ring
  unfold hammingFailProb
  rw [Finset.sum_congr rfl (fun θ _ => h2 θ), Finset.sum_sub_distrib]
  congr 1
  simp

/-- Chernoff by counting. -/
theorem count_bound {N : ℕ} (t : Fin N → Fin 2) :
    ∑ θ, ind t θ ≤ (2 : ℝ) ^ ((N : ℝ) / 4) * (3 / 2) ^ N := by
  have hpt : ∀ θ, ind t θ ≤ (2 : ℝ) ^ ((N : ℝ) / 4) * (1 / 2) ^ hammingErr t θ := by
    intro θ
    unfold ind
    split_ifs with h
    · rw [one_div_pow, ← div_eq_mul_one_div, one_le_div (by positivity),
        ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h.le
    · positivity
  have hsum : ∑ θ : Fin N → Fin 2, (1 / 2 : ℝ) ^ hammingErr t θ = (3 / 2) ^ N := by
    have e : ∀ θ : Fin N → Fin 2, (1 / 2 : ℝ) ^ hammingErr t θ =
        ∏ i, (fun (i : Fin N) (b : Fin 2) => if t i ≠ b then (1 / 2 : ℝ) else 1) i (θ i) := by
      intro θ
      simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one, hammingErr]
    simp only [e]
    have hps := Fintype.prod_sum (fun (i : Fin N) (b : Fin 2) => if t i ≠ b then (1 / 2 : ℝ) else 1)
    rw [← hps]
    have h3 : ∀ c : Fin 2, ∑ b : Fin 2, (if c ≠ b then (1 / 2 : ℝ) else 1) = 3 / 2 := by
      intro c; fin_cases c <;> simp [Fin.sum_univ_two] <;> norm_num
    simp only [h3, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ∑ θ, ind t θ ≤ ∑ θ, (2 : ℝ) ^ ((N : ℝ) / 4) * (1 / 2) ^ hammingErr t θ :=
        Finset.sum_le_sum fun θ _ => hpt θ
    _ = _ := by rw [← Finset.mul_sum, hsum]

/-- The chi-square identity per point. -/
theorem sum_sq_div_le {N k : ℕ} (q : Fin 2 → Fin N → Fin k → ℝ)
    (hs : ∀ b i, ∑ y, q b i y = 1) (hpos : ∀ i y, 0 < q 0 i y) (K : ℝ) (hK : 0 ≤ K)
    (hchi : ∀ i, ∑ y, (q 1 i y - q 0 i y) ^ 2 / q 0 i y ≤ K) (b : Fin 2) (i : Fin N) :
    ∑ y, q b i y ^ 2 / q 0 i y ≤ 1 + K := by
  have e : ∀ y, q b i y ^ 2 / q 0 i y =
      (q b i y - q 0 i y) ^ 2 / q 0 i y + 2 * q b i y - q 0 i y := by
    intro y
    have := (hpos i y).ne'
    field_simp
    ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
  fin_cases b
  · simp; linarith
  · simp; linarith [hchi i]

theorem sum_ratio {N k n : ℕ} (hN : 0 < N) (q : Fin 2 → Fin N → Fin k → ℝ)
    (hs : ∀ b i, ∑ y, q b i y = 1) (hpos : ∀ i y, 0 < q 0 i y) (K : ℝ) (hK : 0 ≤ K)
    (hchi : ∀ i, ∑ y, (q 1 i y - q 0 i y) ^ 2 / q 0 i y ≤ K) (θ : Fin N → Fin 2) :
    ∑ S : Fin n → Fin N × Fin k, P q θ S ^ 2 / P q (fun _ => 0) S ≤ (1 + K) ^ n := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold P
  simp only [← Finset.prod_pow, ← Finset.prod_div_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (z : Fin N × Fin k) =>
    dataDist q θ z ^ 2 / dataDist q (fun _ => 0) z)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hnn : 0 ≤ ∑ z, dataDist q θ z ^ 2 / dataDist q (fun _ => 0) z := by
    refine Finset.sum_nonneg fun z _ => div_nonneg (sq_nonneg _) ?_
    exact div_nonneg (hpos _ _).le hN'.le
  refine pow_le_pow_left₀ hnn ?_ n
  rw [Fintype.sum_prod_type]
  have e : ∀ i y, dataDist q θ (i, y) ^ 2 / dataDist q (fun _ => 0) (i, y)
      = (q (θ i) i y ^ 2 / q 0 i y) / N := by
    intro i y
    have := (hpos i y).ne'
    simp only [dataDist]
    field_simp
  simp only [e]
  calc ∑ i, ∑ y, q (θ i) i y ^ 2 / q 0 i y / (N : ℝ)
        = ∑ i, (∑ y, q (θ i) i y ^ 2 / q 0 i y) / (N : ℝ) := by simp only [Finset.sum_div]
    _ ≤ ∑ _i : Fin N, (1 + K) / N :=
        Finset.sum_le_sum fun i _ =>
          div_le_div_of_nonneg_right (sum_sq_div_le q hs hpos K hK hchi (θ i) i) hN'.le
    _ = 1 + K := by simp; field_simp

/-- Numerics. -/
theorem numeric {N : ℕ} (hN : 128 ≤ N) :
    (1 / (2 : ℝ) ^ N) * ((2 : ℝ) ^ ((N : ℝ) / 4) * (3 / 2) ^ N) * Real.exp ((N : ℝ) / 160)
      ≤ 1 / 100 := by
  set r : ℝ := (2 : ℝ) ^ (1 / 4 : ℝ) * (3 / 4) * Real.exp (1 / 160) with hr
  have e : (1 / (2 : ℝ) ^ N) * ((2 : ℝ) ^ ((N : ℝ) / 4) * (3 / 2) ^ N) *
      Real.exp ((N : ℝ) / 160) = r ^ N := by
    have h1 : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ N = (2 : ℝ) ^ ((N : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
    have h2 : Real.exp (1 / 160) ^ N = Real.exp ((N : ℝ) / 160) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h3 : (3 / 4 : ℝ) ^ N = (1 / 2 ^ N) * (3 / 2) ^ N := by
      rw [← one_div_pow, ← mul_pow]; norm_num
    rw [hr, mul_pow, mul_pow, h1, h2, h3]
    ring
  rw [e]
  have hr0 : 0 ≤ r := by positivity
  have hexp : Real.exp (1 / 40) < 11 / 10 := by
    have h1 : Real.exp (1 / 40) ^ 40 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 1 < (11 / 10 : ℝ) ^ 40 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [← h1] at h2
    exact lt_of_pow_lt_pow_left₀ 40 (by norm_num) h2
  have hr4 : r ^ 4 ≤ 7 / 10 := by
    have : r ^ 4 = 2 * (81 / 256) * Real.exp (1 / 40) := by
      have h1 : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      have h2 : Real.exp (1 / 160) ^ 4 = Real.exp (1 / 40) := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [hr, mul_pow, mul_pow, h1, h2]
      norm_num
    rw [this]; nlinarith
  have hr1 : r ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < r ^ 4 := one_lt_pow₀ h (by norm_num)
    linarith
  calc r ^ N ≤ r ^ 128 := pow_le_pow_of_le_one hr0 hr1 hN
    _ = (r ^ 4) ^ 32 := by rw [← pow_mul]
    _ ≤ (7 / 10) ^ 32 := pow_le_pow_left₀ (by positivity) hr4 32
    _ ≤ 1 / 100 := by norm_num

/-- **Generic statistical lower bound.** -/
theorem generic {N k n : ℕ} (hN : 128 ≤ N) (q : Fin 2 → Fin N → Fin k → ℝ)
    (hsimp : ∀ b i, q b i ∈ stdSimplex ℝ (Fin k)) (hpos : ∀ i y, 0 < q 0 i y)
    (K : ℝ) (hK : 0 ≤ K) (hchi : ∀ i, ∑ y, (q 1 i y - q 0 i y) ^ 2 / q 0 i y ≤ K)
    (hnK : (n : ℝ) * K ≤ (N : ℝ) / 160)
    (est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ) (hest : IsRandEstimator est) :
    9 / 10 ≤ hammingFailProb q est := by
  have hN0 : 0 < N := by omega
  have hs : ∀ b i, ∑ y, q b i y = 1 := fun b i => (hsimp b i).2
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  set c : ℝ := 1 / (2 : ℝ) ^ N with hc
  have hc0 : 0 < c := by positivity
  set P0 : (Fin n → Fin N × Fin k) → ℝ := fun S => P (n := n) q (fun _ => 0) S with hP0
  have hP0pos : ∀ S, 0 < P0 S := by
    intro S
    exact Finset.prod_pos fun j _ => div_pos (hpos _ _) hN'
  have hPnn : ∀ θ (S : Fin n → Fin N × Fin k), 0 ≤ P q θ S := by
    intro θ S
    exact Finset.prod_nonneg fun j _ => div_nonneg ((hsimp _ _).1 _) hN'.le
  rw [fail_eq hN0 q hs hest]
  set Bad := ∑ θ, ∑ S, c * (P q θ S * G est θ S) with hBad
  -- Cauchy–Schwarz
  have hCS : Bad ^ 2 ≤ (∑ θ, ∑ S, c * P0 S * G est θ S) *
      (∑ θ, ∑ S, c * G est θ S * (P q θ S ^ 2 / P0 S)) := by
    rw [hBad]
    simp only [← Fintype.sum_prod_type']
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ ?_ ?_ ?_
    · intro p _
      exact mul_nonneg (mul_nonneg hc0.le (hP0pos _).le) (G_nonneg hest _ _)
    · intro p _
      exact mul_nonneg (mul_nonneg hc0.le (G_nonneg hest _ _))
        (div_nonneg (sq_nonneg _) (hP0pos _).le)
    · intro p _
      have := (hP0pos p.2).ne'
      refine le_of_eq ?_
      field_simp
  -- first factor
  have hF1 : (∑ θ, ∑ S, c * P0 S * G est θ S) ≤ c * ((2 : ℝ) ^ ((N : ℝ) / 4) * (3 / 2) ^ N) := by
    rw [Finset.sum_comm]
    have hS : ∀ S, ∑ θ, c * P0 S * G est θ S ≤
        P0 S * (c * ((2 : ℝ) ^ ((N : ℝ) / 4) * (3 / 2) ^ N)) := by
      intro S
      have : ∑ θ, c * P0 S * G est θ S = P0 S * ∑ t, est S t * (c * ∑ θ, ind t θ) := by
        simp only [G, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun θ _ => ?_
        ring
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ (hP0pos S).le
      calc ∑ t, est S t * (c * ∑ θ, ind t θ)
          ≤ ∑ t, est S t * (c * ((2 : ℝ) ^ ((N : ℝ) / 4) * (3 / 2) ^ N)) :=
            Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (count_bound t) hc0.le) ((hest S).1 t)
        _ = _ := by rw [← Finset.sum_mul, (hest S).2, one_mul]
    calc ∑ S, ∑ θ, c * P0 S * G est θ S
        ≤ ∑ S, P0 S * (c * ((2 : ℝ) ^ ((N : ℝ) / 4) * (3 / 2) ^ N)) :=
          Finset.sum_le_sum fun S _ => hS S
      _ = _ := by rw [← Finset.sum_mul, sum_P hN0 q hs, one_mul]
  -- second factor
  have hF2 : (∑ θ, ∑ S, c * G est θ S * (P q θ S ^ 2 / P0 S)) ≤ Real.exp ((N : ℝ) / 160) := by
    have hθ : ∀ θ, ∑ S, c * G est θ S * (P q θ S ^ 2 / P0 S) ≤ c * (1 + K) ^ n := by
      intro θ
      calc ∑ S, c * G est θ S * (P q θ S ^ 2 / P0 S) ≤ ∑ S, c * (P q θ S ^ 2 / P0 S) :=
            Finset.sum_le_sum fun S _ => by
              have h0 : 0 ≤ P q θ S ^ 2 / P0 S := div_nonneg (sq_nonneg _) (hP0pos S).le
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (mul_le_of_le_one_left h0 (G_le_one hest θ S)) hc0.le
        _ = c * ∑ S, P q θ S ^ 2 / P0 S := by rw [Finset.mul_sum]
        _ ≤ c * (1 + K) ^ n :=
            mul_le_mul_of_nonneg_left (sum_ratio hN0 q hs hpos K hK hchi θ) hc0.le
    calc _ ≤ ∑ _θ : Fin N → Fin 2, c * (1 + K) ^ n := Finset.sum_le_sum fun θ _ => hθ θ
      _ = (1 + K) ^ n := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul, hc]
          push_cast
          field_simp
      _ ≤ Real.exp K ^ n := pow_le_pow_left₀ (by linarith) (by
            have := Real.add_one_le_exp K; linarith) n
      _ = Real.exp (n * K) := (Real.exp_nat_mul K n).symm
      _ ≤ Real.exp ((N : ℝ) / 160) := Real.exp_le_exp.mpr hnK
  have hBad0 : 0 ≤ Bad :=
    Finset.sum_nonneg fun θ _ => Finset.sum_nonneg fun S _ =>
      mul_nonneg hc0.le (mul_nonneg (hPnn θ S) (G_nonneg hest θ S))
  have hsq : Bad ^ 2 ≤ 1 / 100 := by
    refine hCS.trans ?_
    refine (mul_le_mul hF1 hF2 ?_ ?_).trans ?_
    · exact Finset.sum_nonneg fun θ _ => Finset.sum_nonneg fun S _ =>
        mul_nonneg (mul_nonneg hc0.le (G_nonneg hest _ _))
          (div_nonneg (sq_nonneg _) (hP0pos _).le)
    · positivity
    · rw [hc]; exact numeric hN
  nlinarith

end MulticlassOmni.Dev.B4
end
end

section
namespace MulticlassOmni.Dev.B4
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.B3 MulticlassOmni.Dev.F43

/-- Lipschitz construction: positivity of `q_0` and the chi-square bound. -/
theorem lip_facts {k N : ℕ} (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (hη0 : 0 < η)
    (hη : η ≤ 1 / 16384) (hsx : ∀ i, x i ∈ stdSimplex ℝ (Fin k))
    (hbx : ∀ i y, 7 / (8 * (k : ℝ)) ≤ x i y ∧ x i y ≤ 9 / (8 * (k : ℝ)))
    (h1x : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ))) (i : Fin N) :
    (∀ y, 7 / (16 * (k : ℝ)) ≤ qLip x η 0 i y) ∧
      ∑ y, (qLip x η 1 i y - qLip x η 0 i y) ^ 2 / qLip x η 0 i y
        ≤ 32768 / 7 * (k : ℝ) * η ^ 2 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨a0nn, -, h0⟩ := alpha_facts hk x η hη0 hη h1x 0 i
  obtain ⟨-, -, h1⟩ := alpha_facts hk x η hη0 hη h1x 1 i
  set D := dot (eOne k) (costB x η i - costA k) + 2 * η with hDdef
  set a0 := alpha x η 0 i with ha0
  set a1 := alpha x η 1 i with ha1
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one] at h0 h1
  have hx1 : (k : ℝ) * x i ⟨0, hk⟩ ≤ 15 / 16 := by
    have := h1x i ⟨0, hk⟩ rfl
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hD : 17 / 256 ≤ D := by
    rw [hDdef, delta_e1 hk]; linarith
  have ha0half : a0 ≤ 1 / 2 := by nlinarith
  have hdiff : (a0 - a1) * D = 2 * η := by linarith [show (a0 - a1) * D = a0 * D - a1 * D by ring]
  have hdpos : 0 ≤ a0 - a1 := by
    by_contra h
    push Not at h
    nlinarith
  have hdle : a0 - a1 ≤ 32 * η := by nlinarith
  have hq : ∀ (b : Fin 2) y, qLip x η b i y = alpha x η b i * eOne k y + (1 - alpha x η b i) * x i y := by
    intro b y; simp [qLip]
  have he : ∀ y, eOne k y = 0 ∨ eOne k y = 1 := by
    intro y; simp only [eOne]; split_ifs <;> simp
  have hxle1 : ∀ y, x i y ≤ 1 := by
    intro y
    rw [← (hsx i).2]
    exact Finset.single_le_sum (fun j _ => (hsx i).1 j) (Finset.mem_univ y)
  have hpos : ∀ y, 7 / (16 * (k : ℝ)) ≤ qLip x η 0 i y := by
    intro y
    rw [hq]
    have hx := (hbx i y).1
    have : 0 ≤ eOne k y := by rcases he y with h | h <;> rw [h] <;> norm_num
    have e7 : 7 / (16 * (k : ℝ)) = (1 / 2) * (7 / (8 * k)) := by field_simp; ring
    rw [e7]
    change 1 / 2 * (7 / (8 * (k : ℝ))) ≤ a0 * eOne k y + (1 - a0) * x i y
    have hx0 : 0 ≤ x i y := (hsx i).1 y
    nlinarith [mul_nonneg a0nn this, mul_nonneg (sub_nonneg.2 ha0half) hx0]
  refine ⟨hpos, ?_⟩
  have hterm : ∀ y, (qLip x η 1 i y - qLip x η 0 i y) ^ 2 / qLip x η 0 i y ≤
      (16 * (k : ℝ) / 7) * (1024 * η ^ 2) * (eOne k y + x i y) := by
    intro y
    have hq0 := hpos y
    have h7 : (0 : ℝ) < 7 / (16 * (k : ℝ)) := by positivity
    have hd : qLip x η 1 i y - qLip x η 0 i y = (a1 - a0) * (eOne k y - x i y) := by
      rw [hq, hq]; ring
    have hsq : (eOne k y - x i y) ^ 2 ≤ eOne k y + x i y := by
      have := (hsx i).1 y
      have := hxle1 y
      rcases he y with h | h <;> rw [h] <;> nlinarith
    have hsq2 : (qLip x η 1 i y - qLip x η 0 i y) ^ 2 ≤ (1024 * η ^ 2) * (eOne k y + x i y) := by
      rw [hd, mul_pow]
      have : (a1 - a0) ^ 2 ≤ 1024 * η ^ 2 := by nlinarith
      exact mul_le_mul this hsq (sq_nonneg _) (by positivity)
    calc (qLip x η 1 i y - qLip x η 0 i y) ^ 2 / qLip x η 0 i y
        ≤ (qLip x η 1 i y - qLip x η 0 i y) ^ 2 / (7 / (16 * (k : ℝ))) :=
          div_le_div_of_nonneg_left (sq_nonneg _) h7 hq0
      _ ≤ (1024 * η ^ 2) * (eOne k y + x i y) / (7 / (16 * (k : ℝ))) :=
          div_le_div_of_nonneg_right hsq2 h7.le
      _ = _ := by field_simp
  calc _ ≤ ∑ y, (16 * (k : ℝ) / 7) * (1024 * η ^ 2) * (eOne k y + x i y) :=
        Finset.sum_le_sum fun y _ => hterm y
    _ = (16 * (k : ℝ) / 7) * (1024 * η ^ 2) * 2 := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_eOne hk, (hsx i).2]; norm_num
    _ = _ := by ring

theorem qGLM_apply {k N : ℕ} (hk : 0 < k) (x : Fin N → Fin k → ℝ) (ε : ℝ) (b : Fin 2)
    (i : Fin N) (y : Fin k) :
    qGLM x ε b i y = (1 + 4 * (1 / 32 + 48 * ε * ((b : ℕ) : ℝ)) * x i y) / k := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [qGLM, vbar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- GLM construction: simplex membership, positivity and chi-square bound. -/
theorem glm_facts {k N : ℕ} (hk : 0 < k) (x : Fin N → Fin k → ℝ) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 512) (hbox : ∀ i y, x i y ∈ Set.Icc (-1 : ℝ) 1)
    (hsum : ∀ i, ∑ y, x i y = 0) (hsq : ∀ i, ∑ y, x i y ^ 2 = (k : ℝ) / 4) :
    (∀ b i, qGLM x ε b i ∈ stdSimplex ℝ (Fin k)) ∧
      (∀ i y, 0 < qGLM x ε 0 i y) ∧
      (∀ i, ∑ y, (qGLM x ε 1 i y - qGLM x ε 0 i y) ^ 2 / qGLM x ε 0 i y ≤ 16384 * ε ^ 2) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hbl : ∀ b : Fin 2, ((b : ℕ) : ℝ) = 0 ∨ ((b : ℕ) : ℝ) = 1 := by
    intro b
    have := b.isLt
    interval_cases hb : (b : ℕ) <;> simp
  refine ⟨?_, ?_, ?_⟩
  · intro b i
    refine ⟨fun y => ?_, ?_⟩
    · rw [qGLM_apply hk]
      apply div_nonneg _ hk'.le
      obtain ⟨h1, h2⟩ := hbox i y
      rcases hbl b with h | h <;> rw [h] <;> nlinarith
    · simp only [qGLM_apply hk, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
        hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      field_simp
      ring
  · intro i y
    rw [qGLM_apply hk]
    apply div_pos _ hk'
    obtain ⟨h1, h2⟩ := hbox i y
    simp; nlinarith
  · intro i
    have hterm : ∀ y, (qGLM x ε 1 i y - qGLM x ε 0 i y) ^ 2 / qGLM x ε 0 i y ≤
        (192 * ε) ^ 2 * 8 / (7 * k) * x i y ^ 2 := by
      intro y
      obtain ⟨h1, h2⟩ := hbox i y
      rw [qGLM_apply hk, qGLM_apply hk]
      simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero,
        mul_one]
      have hq0 : 7 / 8 ≤ 1 + 4 * (1 / 32) * x i y := by nlinarith
      rw [div_le_iff₀ (by apply div_pos (by linarith) hk')]
      have e : ((1 + 4 * (1 / 32 + 48 * ε) * x i y) / k - (1 + 4 * (1 / 32) * x i y) / k) ^ 2
          = (192 * ε) ^ 2 * x i y ^ 2 / k ^ 2 := by field_simp; ring
      rw [e]
      have e2 : (192 * ε) ^ 2 * 8 / (7 * k) * x i y ^ 2 * ((1 + 4 * (1 / 32) * x i y) / k)
          = (192 * ε) ^ 2 * x i y ^ 2 / k ^ 2 * (8 / 7 * (1 + 4 * (1 / 32) * x i y)) := by
        field_simp
      rw [e2]
      have : 0 ≤ (192 * ε) ^ 2 * x i y ^ 2 / k ^ 2 := by positivity
      nlinarith
    calc _ ≤ ∑ y, (192 * ε) ^ 2 * 8 / (7 * k) * x i y ^ 2 :=
          Finset.sum_le_sum fun y _ => hterm y
      _ = (192 * ε) ^ 2 * 8 / (7 * k) * (k / 4) := by rw [← Finset.mul_sum, hsq]
      _ ≤ 16384 * ε ^ 2 := by
          rw [show (192 * ε) ^ 2 * 8 / (7 * k) * (k / 4) = 73728 / 7 * ε ^ 2 by field_simp; ring]
          nlinarith [sq_nonneg ε]

end MulticlassOmni.Dev.B4

namespace MulticlassOmni.Lipschitz
open MulticlassOmni.Dev.B4

theorem chk_lemma_B_4 :
    ∃ c₀ c_stat : ℝ, 0 < c₀ ∧ 0 < c_stat ∧
      (∀ Cpack : ℝ, 0 < Cpack → ∃ η₀ : ℝ, 0 < η₀ ∧
        ∀ k : ℕ, 3 ≤ k → ∀ η : ℝ, 0 < η → η ≤ η₀ →
          ∀ (N : ℕ) (x : Fin N → Fin k → ℝ), IsSection41Packing Cpack k η x →
            (∀ (b : Fin 2) (i : Fin N), qLip x η b i ∈ stdSimplex ℝ (Fin k)) ∧
            ∀ n : ℕ, (n : ℝ) ≤ c₀ * N / (k * η ^ 2) →
              ∀ est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ, IsRandEstimator est →
                9 / 10 ≤ hammingFailProb (qLip x η) est) ∧
      (∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 512 →
        ∀ (N : ℕ) (x : Fin N → Fin k → ℝ), IsGLMPacking k ε x →
          (∀ (b : Fin 2) (i : Fin N), qGLM x ε b i ∈ stdSimplex ℝ (Fin k)) ∧
          ∀ n : ℕ, (n : ℝ) ≤ c_stat * N / ε ^ 2 →
            ∀ est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ, IsRandEstimator est →
              9 / 10 ≤ hammingFailProb (qGLM x ε) est) := by
  refine ⟨7 / (160 * 32768), 1 / (160 * 16384), by norm_num, by norm_num, ?_, ?_⟩
  · intro Cpack hC
    obtain ⟨C₁, η₁, -, hη₁, hB3⟩ := lemma_B_3 Cpack hC
    refine ⟨min η₁ (1 / 16384), lt_min hη₁ (by norm_num), ?_⟩
    intro k hk η hη0 hη N x hx
    have hk0 : 0 < k := by omega
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    obtain ⟨⟨-, -, hN128⟩, -, hqmem⟩ := hB3 k hk η hη0 (hη.trans (min_le_left _ _)) N x hx
    refine ⟨fun b i => hqmem i b, ?_⟩
    intro n hn est hest
    obtain ⟨X₀, ⟨-, hsimp, hb, h1, -, -⟩, -, hmem, -⟩ := hx
    have hη' : η ≤ 1 / 16384 := hη.trans (min_le_right _ _)
    have hfacts := fun i => lip_facts hk0 x η hη0 hη' (fun i => hsimp _ (hmem i))
      (fun i y => hb _ (hmem i) y) (fun i y hy => h1 _ (hmem i) y hy) i
    refine generic hN128 (qLip x η) (fun b i => hqmem i b)
      (fun i y => lt_of_lt_of_le (by positivity) ((hfacts i).1 y))
      (32768 / 7 * (k : ℝ) * η ^ 2) (by positivity) (fun i => (hfacts i).2) ?_ est hest
    calc (n : ℝ) * (32768 / 7 * (k : ℝ) * η ^ 2)
        ≤ (7 / (160 * 32768) * N / (k * η ^ 2)) * (32768 / 7 * (k : ℝ) * η ^ 2) :=
          mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (N : ℝ) / 160 := by field_simp
  · intro k hk ε hε0 hε N x hx
    have hk0 : 0 < k := by omega
    obtain ⟨-, ⟨hbox, hsum, hsq, -⟩, -, h512⟩ := hx
    have hm : ∀ i, x i ∈ Finset.univ.image x := fun i =>
      Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨hmem, hpos, hchi⟩ := glm_facts hk0 x ε hε0 hε (fun i y => hbox _ (hm i) y)
      (fun i => hsum _ (hm i)) (fun i => hsq _ (hm i))
    refine ⟨hmem, ?_⟩
    intro n hn est hest
    refine generic (by omega) (qGLM x ε) hmem hpos (16384 * ε ^ 2) (by positivity) hchi ?_ est hest
    calc (n : ℝ) * (16384 * ε ^ 2) ≤ (1 / (160 * 16384) * N / ε ^ 2) * (16384 * ε ^ 2) :=
          mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (N : ℝ) / 160 := by field_simp

end MulticlassOmni.Lipschitz
end

theorem solution : type_of% @MulticlassOmni.Lipschitz.chk_lemma_B_4 := @MulticlassOmni.Lipschitz.chk_lemma_B_4
