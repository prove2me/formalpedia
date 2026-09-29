-- Prove2me | solution 1 for MetodosNumericos.newton_local_convergence
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:09:47.096349+00:00
-- url     : https://prove2.me/submissions/3f24808f-dab4-4c2d-844c-8eb9f5b8fbdb

import Mathlib
import Definitions.Def_MetodosNumericos_zerosDefs
import Definitions.Def_MetodosNumericos_errosDefs
import Definitions.Def_MetodosNumericos_sistemasDefs
import Definitions.Def_MetodosNumericos_integracaoDefs

open Filter Topology
open MetodosNumericos

theorem W2m_MetodosNumericos_error_propagation_add_sub (x y xt yt : ℝ) :
    (x + y) - (xt + yt) = (x - xt) + (y - yt) ∧
      (x - y) - (xt - yt) = (x - xt) - (y - yt) := ⟨by ring, by ring⟩

theorem W2m_MetodosNumericos_error_propagation_mul (x y xt yt : ℝ) :
    x * y - xt * yt = xt * (y - yt) + yt * (x - xt) + (x - xt) * (y - yt) := by ring

theorem W2m_MetodosNumericos_error_propagation_div (x y xt yt : ℝ) (hy : y ≠ 0)
    (hyt : yt ≠ 0) :
    x / y - xt / yt = (yt * (x - xt) - xt * (y - yt)) / (y * yt) := by
  rw [div_sub_div _ _ hy hyt]
  ring

theorem W2m_MetodosNumericos_iter_mem (g : ℝ → ℝ) (a b x0 : ℝ)
    (hmaps : ∀ x ∈ Set.Icc a b, g x ∈ Set.Icc a b) (hx0 : x0 ∈ Set.Icc a b) :
    ∀ n, iterSeq g x0 n ∈ Set.Icc a b := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
    show g (iterSeq g x0 n) ∈ Set.Icc a b
    exact hmaps _ ih

theorem W2m_MetodosNumericos_lip (g g' : ℝ → ℝ) (a b L : ℝ)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Set.Icc a b, |g' x| ≤ L) {x y : ℝ} (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) : |g x - g y| ≤ L * |x - y| := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g')
    (fun z hz => (hderiv z hz).hasDerivWithinAt)
    (fun z hz => by rw [Real.norm_eq_abs]; exact hbound z hz) (convex_Icc a b) hy hx
  simpa [Real.norm_eq_abs] using H

theorem W2m_MetodosNumericos_mil_error_estimate (g g' : ℝ → ℝ) (a b L x0 xbar : ℝ)
    (hmaps : ∀ x ∈ Set.Icc a b, g x ∈ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Set.Icc a b, |g' x| ≤ L) (hL : L < 1)
    (hx0 : x0 ∈ Set.Icc a b) (hxbar : xbar ∈ Set.Icc a b) (hfix : g xbar = xbar) :
    ∀ n : ℕ, |xbar - iterSeq g x0 (n + 1)| ≤
      L / (1 - L) * |iterSeq g x0 (n + 1) - iterSeq g x0 n| := by
  intro n
  have hmem := W2m_MetodosNumericos_iter_mem g a b x0 hmaps hx0
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hbound x0 hx0)
  have h1 : |xbar - iterSeq g x0 (n + 1)| ≤ L * |xbar - iterSeq g x0 n| := by
    have H := W2m_MetodosNumericos_lip g g' a b L hderiv hbound hxbar (hmem n)
    rw [hfix] at H
    show |xbar - g (iterSeq g x0 n)| ≤ L * |xbar - iterSeq g x0 n|
    exact H
  have h2 : |xbar - iterSeq g x0 n| ≤
      |xbar - iterSeq g x0 (n + 1)| + |iterSeq g x0 (n + 1) - iterSeq g x0 n| :=
    abs_sub_le xbar (iterSeq g x0 (n + 1)) (iterSeq g x0 n)
  have h3 : (1 - L) * |xbar - iterSeq g x0 (n + 1)| ≤
      L * |iterSeq g x0 (n + 1) - iterSeq g x0 n| := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hL0]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

theorem W2m_MetodosNumericos_mil_convergence (g g' : ℝ → ℝ) (a b L x0 xbar : ℝ)
    (hmaps : ∀ x ∈ Set.Icc a b, g x ∈ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Set.Icc a b, |g' x| ≤ L) (hL : L < 1)
    (hx0 : x0 ∈ Set.Icc a b) (hxbar : xbar ∈ Set.Icc a b) (hfix : g xbar = xbar) :
    Tendsto (iterSeq g x0) atTop (𝓝 xbar) := by
  have hmem := W2m_MetodosNumericos_iter_mem g a b x0 hmaps hx0
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hbound x0 hx0)
  have hb : ∀ n, |iterSeq g x0 n - xbar| ≤ L ^ n * |x0 - xbar| := by
    intro n
    induction n with
    | zero => simp [iterSeq]
    | succ n ih =>
      have H := W2m_MetodosNumericos_lip g g' a b L hderiv hbound (hmem n) hxbar
      rw [hfix] at H
      show |g (iterSeq g x0 n) - xbar| ≤ L ^ (n + 1) * |x0 - xbar|
      calc |g (iterSeq g x0 n) - xbar| ≤ L * |iterSeq g x0 n - xbar| := H
        _ ≤ L * (L ^ n * |x0 - xbar|) := mul_le_mul_of_nonneg_left ih hL0
        _ = L ^ (n + 1) * |x0 - xbar| := by ring
  have ht : Tendsto (fun n : ℕ => L ^ n * |x0 - xbar|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hL0 hL).mul_const |x0 - xbar|
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => by rw [Real.norm_eq_abs]; exact hb n) ht

theorem W2m_MetodosNumericos_dec_bounds (x : ℝ) (hx : 0 < x) :
    (10 : ℝ) ^ (decExp x - 1) ≤ x ∧ x < (10 : ℝ) ^ (decExp x) := by
  have hlog := Int.floor_le (Real.logb 10 x)
  have hlog2 := Int.lt_floor_add_one (Real.logb 10 x)
  have e : decExp x = ⌊Real.logb 10 x⌋ + 1 := by simp [decExp, abs_of_pos hx]
  rw [e, add_sub_cancel_right]
  constructor
  · rw [← Real.rpow_intCast]
    exact (Real.le_logb_iff_rpow_le (by norm_num) hx).1 hlog
  · rw [← Real.rpow_intCast]
    push_cast
    exact (Real.logb_lt_iff_lt_rpow (by norm_num) hx).1 hlog2

theorem W2m_MetodosNumericos_floor_ge (t : ℕ) (ht : 1 ≤ t) (y : ℝ)
    (hy : (10 : ℝ) ^ ((t : ℤ) - 1) ≤ y) :
    (10 : ℝ) ^ ((t : ℤ) - 1) ≤ (⌊y⌋ : ℝ) := by
  have hm : ((10 ^ (t - 1) : ℕ) : ℝ) = (10 : ℝ) ^ ((t : ℤ) - 1) := by
    rw [show (t : ℤ) - 1 = ((t - 1 : ℕ) : ℤ) by omega, zpow_natCast]
    norm_cast
  have h1 : ((10 ^ (t - 1) : ℕ) : ℤ) ≤ ⌊y⌋ := by
    rw [Int.le_floor, Int.cast_natCast, hm]
    exact hy
  rw [← hm]
  exact_mod_cast h1

theorem W2m_MetodosNumericos_trunc_relative_error (t : ℕ) (ht : 1 ≤ t) (x : ℝ) (hx : 0 < x) :
    |x - truncRound t x| / |truncRound t x| < (10 : ℝ) ^ (1 - (t : ℤ)) := by
  obtain ⟨hlo, -⟩ := W2m_MetodosNumericos_dec_bounds x hx
  have h10 : (10 : ℝ) ≠ 0 := by norm_num
  have hPQ : (10 : ℝ) ^ ((t : ℤ) - decExp x) * (10 : ℝ) ^ (decExp x - (t : ℤ)) = 1 := by
    rw [← zpow_add₀ h10]; simp
  have hQpos : (0 : ℝ) < (10 : ℝ) ^ (decExp x - (t : ℤ)) := by positivity
  have hylo : (10 : ℝ) ^ ((t : ℤ) - 1) ≤ x * (10 : ℝ) ^ ((t : ℤ) - decExp x) := by
    have H : (10 : ℝ) ^ ((t : ℤ) - 1)
        = (10 : ℝ) ^ (decExp x - 1) * (10 : ℝ) ^ ((t : ℤ) - decExp x) := by
      rw [← zpow_add₀ h10]; congr 1; ring
    rw [H]
    exact mul_le_mul_of_nonneg_right hlo (by positivity)
  have hfl := W2m_MetodosNumericos_floor_ge t ht _ hylo
  have hkey : (10 : ℝ) ^ (1 - (t : ℤ)) * (10 : ℝ) ^ ((t : ℤ) - 1) = 1 := by
    rw [← zpow_add₀ h10]; simp
  have hA : (0 : ℝ) < (10 : ℝ) ^ (1 - (t : ℤ)) := by positivity
  have hB : (0 : ℝ) < (10 : ℝ) ^ ((t : ℤ) - 1) := by positivity
  unfold truncRound
  generalize (10 : ℝ) ^ ((t : ℤ) - decExp x) = P at hPQ hylo hfl ⊢
  generalize (10 : ℝ) ^ (decExp x - (t : ℤ)) = Q at hPQ hQpos ⊢
  have hF1 := Int.floor_le (x * P)
  have hF2 := Int.lt_floor_add_one (x * P)
  generalize (⌊x * P⌋ : ℝ) = F at hF1 hF2 hfl ⊢
  generalize (10 : ℝ) ^ ((t : ℤ) - 1) = B at hB hfl hkey
  generalize (10 : ℝ) ^ (1 - (t : ℤ)) = A at hkey hA ⊢
  have hxQ : x = x * P * Q := by rw [mul_assoc, hPQ, mul_one]
  have hFpos : 0 < F := lt_of_lt_of_le hB hfl
  have hFQ : 0 < F * Q := mul_pos hFpos hQpos
  have hd0 : 0 ≤ x - F * Q := by
    have := mul_nonneg (sub_nonneg.2 hF1) hQpos.le
    nlinarith
  rw [abs_of_nonneg hd0, abs_of_pos hFQ, div_lt_iff₀ hFQ]
  have h1 := mul_nonneg (mul_nonneg (sub_nonneg.2 hfl) hA.le) hQpos.le
  have h2 := mul_pos (by linarith : (0 : ℝ) < F + 1 - x * P) hQpos
  have hABQ : A * B * Q = Q := by rw [hkey, one_mul]
  nlinarith

theorem W2m_MetodosNumericos_sym_relative_error (t : ℕ) (ht : 1 ≤ t) (x : ℝ) (hx : 0 < x) :
    |x - symRound t x| / |symRound t x| ≤ (1 / 2 : ℝ) * (10 : ℝ) ^ (1 - (t : ℤ)) := by
  obtain ⟨hlo, -⟩ := W2m_MetodosNumericos_dec_bounds x hx
  have h10 : (10 : ℝ) ≠ 0 := by norm_num
  have hPQ : (10 : ℝ) ^ ((t : ℤ) - decExp x) * (10 : ℝ) ^ (decExp x - (t : ℤ)) = 1 := by
    rw [← zpow_add₀ h10]; simp
  have hQpos : (0 : ℝ) < (10 : ℝ) ^ (decExp x - (t : ℤ)) := by positivity
  have hylo : (10 : ℝ) ^ ((t : ℤ) - 1) ≤ x * (10 : ℝ) ^ ((t : ℤ) - decExp x) + 1 / 2 := by
    have H : (10 : ℝ) ^ ((t : ℤ) - 1)
        = (10 : ℝ) ^ (decExp x - 1) * (10 : ℝ) ^ ((t : ℤ) - decExp x) := by
      rw [← zpow_add₀ h10]; congr 1; ring
    rw [H]
    have := mul_le_mul_of_nonneg_right hlo (by positivity :
      (0 : ℝ) ≤ (10 : ℝ) ^ ((t : ℤ) - decExp x))
    linarith
  have hfl := W2m_MetodosNumericos_floor_ge t ht _ hylo
  have hkey : (10 : ℝ) ^ (1 - (t : ℤ)) * (10 : ℝ) ^ ((t : ℤ) - 1) = 1 := by
    rw [← zpow_add₀ h10]; simp
  have hA : (0 : ℝ) < (10 : ℝ) ^ (1 - (t : ℤ)) := by positivity
  have hB : (0 : ℝ) < (10 : ℝ) ^ ((t : ℤ) - 1) := by positivity
  unfold symRound
  generalize (10 : ℝ) ^ ((t : ℤ) - decExp x) = P at hPQ hylo hfl ⊢
  generalize (10 : ℝ) ^ (decExp x - (t : ℤ)) = Q at hPQ hQpos ⊢
  have hF1 := Int.floor_le (x * P + 1 / 2)
  have hF2 := Int.lt_floor_add_one (x * P + 1 / 2)
  generalize (⌊x * P + 1 / 2⌋ : ℝ) = F at hF1 hF2 hfl ⊢
  generalize (10 : ℝ) ^ ((t : ℤ) - 1) = B at hB hfl hkey
  generalize (10 : ℝ) ^ (1 - (t : ℤ)) = A at hkey hA ⊢
  have hxQ : x = x * P * Q := by rw [mul_assoc, hPQ, mul_one]
  have hFpos : 0 < F := lt_of_lt_of_le hB hfl
  have hFQ : 0 < F * Q := mul_pos hFpos hQpos
  rw [abs_of_pos hFQ, div_le_iff₀ hFQ]
  have hab : |x - F * Q| ≤ Q / 2 := by
    have e1 := mul_nonneg (sub_nonneg.2 hF1) hQpos.le
    have e2 := mul_pos (by linarith : (0 : ℝ) < F + 1 - (x * P + 1 / 2)) hQpos
    rw [abs_le]
    constructor <;> nlinarith
  have h1 := mul_nonneg (mul_nonneg (sub_nonneg.2 hfl) hA.le) hQpos.le
  have hABQ : A * B * Q = Q := by rw [hkey, one_mul]
  nlinarith

theorem W2m_MetodosNumericos_euler_local_error (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x h : ℝ)
    (hh : 0 < h)
    (hsol : ∀ t ∈ Set.Icc x (x + h), HasDerivAt phi (f t (phi t)) t)
    (hphi2 : ContDiffOn ℝ 2 phi (Set.Icc x (x + h))) :
    ∃ mu ∈ Set.Ioo x (x + h),
      phi (x + h) =
        phi x + h * f x (phi x) + h ^ 2 / 2 * iteratedDerivWithin 2 phi (Set.Icc x (x + h)) mu := by
  have hlt : x < x + h := by linarith
  have hle : x ≤ x + h := hlt.le
  have hU : UniqueDiffOn ℝ (Set.Icc x (x + h)) := uniqueDiffOn_Icc hlt
  have hf1 : ContDiffOn ℝ (1 : ℕ) phi (Set.uIcc x (x + h)) := by
    rw [Set.uIcc_of_le hle]
    exact hphi2.of_le (by first | norm_num | exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2) | simp)
  have hf2 : DifferentiableOn ℝ (iteratedDerivWithin 1 phi (Set.uIcc x (x + h)))
      (Set.uIoo x (x + h)) := by
    rw [Set.uIcc_of_le hle, Set.uIoo_of_le hle]
    exact (hphi2.differentiableOn_iteratedDerivWithin
      (by first | norm_num | exact_mod_cast (by norm_num : (1 : ℕ) < 2) | simp) hU).mono
      Set.Ioo_subset_Icc_self
  obtain ⟨mu, hmu, heq⟩ := taylor_mean_remainder_lagrange (n := 1) hlt.ne hf1 hf2
  rw [Set.uIoo_of_le hle] at hmu
  rw [Set.uIcc_of_le hle] at heq
  refine ⟨mu, hmu, ?_⟩
  have hxmem : x ∈ Set.Icc x (x + h) := ⟨le_refl x, hle⟩
  have hd' : derivWithin phi (Set.Icc x (x + h)) x = f x (phi x) :=
    ((hsol x hxmem).hasDerivWithinAt).derivWithin (hU x hxmem)
  have hd : iteratedDerivWithin 1 phi (Set.Icc x (x + h)) x = f x (phi x) := by
    rw [iteratedDerivWithin_one]; exact hd'
  simp only [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_zero,
    iteratedDerivWithin_zero, hd, smul_eq_mul] at heq
  norm_num at heq
  linear_combination heq

theorem W2m_MetodosNumericos_gs_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b x xstar : Fin n → ℝ) (hsol : A.mulVec xstar = b) (μ E : ℝ) (hdiag : ∀ i, A i i ≠ 0)
    (hμ : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ μ * |A i i|) (hμ1 : μ ≤ 1)
    (hE0 : 0 ≤ E) (hE : ∀ j, |x j - xstar j| ≤ E) :
    ∀ k : ℕ, (∀ j, |gsPartial A b x k j - xstar j| ≤ E) ∧
      (∀ j : Fin n, (j : ℕ) < k → |gsPartial A b x k j - xstar j| ≤ μ * E) := by
  intro k
  induction k with
  | zero =>
    exact ⟨fun j => by simpa [gsPartial] using hE j,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases hk : k < n
    · have hval : |(b ⟨k, hk⟩ - ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
          A ⟨k, hk⟩ j * gsPartial A b x k j) / A ⟨k, hk⟩ ⟨k, hk⟩ - xstar ⟨k, hk⟩| ≤ μ * E := by
        have hb : b ⟨k, hk⟩ = A ⟨k, hk⟩ ⟨k, hk⟩ * xstar ⟨k, hk⟩
            + ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n), A ⟨k, hk⟩ j * xstar j := by
          rw [← hsol]
          simp only [Matrix.mulVec, dotProduct]
          exact (Finset.add_sum_erase _ (fun j => A ⟨k, hk⟩ j * xstar j)
            (Finset.mem_univ _)).symm
        have hS : ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
              A ⟨k, hk⟩ j * (xstar j - gsPartial A b x k j)
            = ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n), A ⟨k, hk⟩ j * xstar j
              - ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n), A ⟨k, hk⟩ j * gsPartial A b x k j := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        have hd := hdiag ⟨k, hk⟩
        have e1 : (b ⟨k, hk⟩ - ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
              A ⟨k, hk⟩ j * gsPartial A b x k j) / A ⟨k, hk⟩ ⟨k, hk⟩ - xstar ⟨k, hk⟩
            = (∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
              A ⟨k, hk⟩ j * (xstar j - gsPartial A b x k j)) / A ⟨k, hk⟩ ⟨k, hk⟩ := by
          rw [hS, hb]
          first | (field_simp; ring1) | field_simp
        rw [e1, abs_div, div_le_iff₀ (abs_pos.2 hd)]
        calc |∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
              A ⟨k, hk⟩ j * (xstar j - gsPartial A b x k j)|
            ≤ ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
              |A ⟨k, hk⟩ j * (xstar j - gsPartial A b x k j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n), |A ⟨k, hk⟩ j| * E :=
              Finset.sum_le_sum fun j _ => by
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact ih1 j)
                  (abs_nonneg _)
          _ = (∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n), |A ⟨k, hk⟩ j|) * E := by
              rw [Finset.sum_mul]
          _ ≤ μ * |A ⟨k, hk⟩ ⟨k, hk⟩| * E := mul_le_mul_of_nonneg_right (hμ _) hE0
          _ = μ * E * |A ⟨k, hk⟩ ⟨k, hk⟩| := by ring
      have hstep : gsPartial A b x (k + 1) = Function.update (gsPartial A b x k) ⟨k, hk⟩
          ((b ⟨k, hk⟩ - ∑ j ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
              A ⟨k, hk⟩ j * gsPartial A b x k j) / A ⟨k, hk⟩ ⟨k, hk⟩) := by
        simp only [gsPartial, dif_pos hk]
      constructor
      · intro j
        rw [hstep]
        by_cases hj : j = ⟨k, hk⟩
        · subst hj
          rw [Function.update_self]
          exact le_trans hval (mul_le_of_le_one_left hE0 hμ1)
        · rw [Function.update_of_ne hj]
          exact ih1 j
      · intro j hjk
        rw [hstep]
        by_cases hj : j = ⟨k, hk⟩
        · subst hj
          rw [Function.update_self]
          exact hval
        · rw [Function.update_of_ne hj]
          apply ih2
          have : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
          omega
    · have hstep : gsPartial A b x (k + 1) = gsPartial A b x k := by
        simp only [gsPartial, dif_neg hk]
      rw [hstep]
      refine ⟨ih1, fun j hjk => ih2 j ?_⟩
      have := j.isLt
      omega

theorem W2m_MetodosNumericos_gauss_seidel_converges {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b xstar x0 : Fin n → ℝ)
    (hA : DiagDominant A) (hsol : A.mulVec xstar = b) :
    Tendsto (gaussSeidelSeq A b x0) atTop (𝓝 xstar) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have H : gaussSeidelSeq A b x0 = fun _ => xstar := funext fun k => Subsingleton.elim _ _
    rw [H]
    exact tendsto_const_nhds
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hdiag : ∀ i, A i i ≠ 0 := by
      intro i h
      have H := hA i
      rw [h, abs_zero] at H
      exact absurd H (not_lt.2 (Finset.sum_nonneg fun j _ => abs_nonneg _))
    have hpos : ∀ i, 0 < |A i i| := fun i => abs_pos.2 (hdiag i)
    obtain ⟨i0, hi0⟩ := Finite.exists_max
      (fun i : Fin n => (∑ j ∈ Finset.univ.erase i, |A i j|) / |A i i|)
    set μ := (∑ j ∈ Finset.univ.erase i0, |A i0 j|) / |A i0 i0| with hμdef
    have hμ1 : μ < 1 := by
      rw [hμdef, div_lt_one (hpos i0)]; exact hA i0
    have hμ0 : 0 ≤ μ := div_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (abs_nonneg _)
    have hμ : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ μ * |A i i| := by
      intro i
      rw [← div_le_iff₀ (hpos i)]
      exact hi0 i
    have hcontr : ∀ k, ‖gaussSeidelSeq A b x0 (k + 1) - xstar‖
        ≤ μ * ‖gaussSeidelSeq A b x0 k - xstar‖ := by
      intro k
      have hE : ∀ j, |gaussSeidelSeq A b x0 k j - xstar j|
          ≤ ‖gaussSeidelSeq A b x0 k - xstar‖ := by
        intro j
        have H := norm_le_pi_norm (gaussSeidelSeq A b x0 k - xstar) j
        rwa [Pi.sub_apply, Real.norm_eq_abs] at H
      have H := W2m_MetodosNumericos_gs_step A b (gaussSeidelSeq A b x0 k) xstar hsol μ
        ‖gaussSeidelSeq A b x0 k - xstar‖ hdiag hμ hμ1.le (norm_nonneg _) hE n
      show ‖gsPartial A b (gaussSeidelSeq A b x0 k) n - xstar‖
        ≤ μ * ‖gaussSeidelSeq A b x0 k - xstar‖
      refine (pi_norm_le_iff_of_nonneg (mul_nonneg hμ0 (norm_nonneg _))).2 fun j => ?_
      rw [Pi.sub_apply, Real.norm_eq_abs]
      exact H.2 j j.isLt
    have hb : ∀ k, ‖gaussSeidelSeq A b x0 k - xstar‖ ≤ μ ^ k * ‖x0 - xstar‖ := by
      intro k
      induction k with
      | zero => simp [gaussSeidelSeq]
      | succ k ih =>
        calc ‖gaussSeidelSeq A b x0 (k + 1) - xstar‖
            ≤ μ * ‖gaussSeidelSeq A b x0 k - xstar‖ := hcontr k
          _ ≤ μ * (μ ^ k * ‖x0 - xstar‖) := mul_le_mul_of_nonneg_left ih hμ0
          _ = μ ^ (k + 1) * ‖x0 - xstar‖ := by ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) hb ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hμ0 hμ1).mul_const ‖x0 - xstar‖

theorem W2m_MetodosNumericos_newton_mvt (f f' f'' : ℝ → ℝ) (a b xbar : ℝ)
    (hxbar : xbar ∈ Set.Ioo a b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x) (x : ℝ) (hxne : x ≠ xbar)
    (hx : x ∈ Set.Ioo a b) :
    ∃ c ∈ Set.Ioo a b, |c - xbar| < |x - xbar| ∧
      (f' x * (x - xbar) - f x + f xbar) / (x - xbar) ^ 2 = f'' c / 2 := by
  set gg : ℝ → ℝ := fun x => f' x * (x - xbar) - f x + f xbar with hgg
  have hgd : ∀ y ∈ Set.Ioo a b, HasDerivAt gg (f'' y * (y - xbar)) y := by
    intro y hy
    refine ((((hf' y hy).fun_mul ((hasDerivAt_id' y).sub_const xbar)).fun_sub
      (hf y hy)).add_const (f xbar)).congr_deriv ?_
    ring
  have hG : ∀ y : ℝ, HasDerivAt (fun y => (y - xbar) ^ 2) (2 * (y - xbar)) y := by
    intro y
    refine (((hasDerivAt_id' y).sub_const xbar).fun_pow 2).congr_deriv ?_
    norm_num
  have hgx : gg xbar = 0 := by simp [hgg]
  have hx0 : (x - xbar) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hxne)
  show ∃ c ∈ Set.Ioo a b, |c - xbar| < |x - xbar| ∧ gg x / (x - xbar) ^ 2 = f'' c / 2
  rcases lt_or_gt_of_ne hxne with hlt | hgt
  · have hsub : Set.Icc x xbar ⊆ Set.Ioo a b := by
      intro y hy
      exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hxbar.2⟩
    obtain ⟨c, hc, hcE⟩ := exists_ratio_hasDerivAt_eq_ratio_slope gg
      (fun y => f'' y * (y - xbar)) hlt
      (fun y hy => (hgd y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy => hgd y (hsub (Set.Ioo_subset_Icc_self hy)))
      (fun y => (y - xbar) ^ 2) (fun y => 2 * (y - xbar))
      (fun y _ => (hG y).continuousAt.continuousWithinAt)
      (fun y _ => hG y)
    refine ⟨c, hsub (Set.Ioo_subset_Icc_self hc), ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hc.2]), abs_of_neg (by linarith)]
      linarith [hc.1]
    · have hc0 : c - xbar ≠ 0 := (by linarith [hc.2] : c - xbar < 0).ne
      rw [div_eq_iff hx0]
      simp only [hgx] at hcE
      have H : (c - xbar) * ((x - xbar) ^ 2 * f'' c - 2 * gg x) = 0 := by
        linear_combination -hcE
      have H2 := (mul_eq_zero.1 H).resolve_left hc0
      linarith
  · have hsub : Set.Icc xbar x ⊆ Set.Ioo a b := by
      intro y hy
      exact ⟨lt_of_lt_of_le hxbar.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
    obtain ⟨c, hc, hcE⟩ := exists_ratio_hasDerivAt_eq_ratio_slope gg
      (fun y => f'' y * (y - xbar)) hgt
      (fun y hy => (hgd y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy => hgd y (hsub (Set.Ioo_subset_Icc_self hy)))
      (fun y => (y - xbar) ^ 2) (fun y => 2 * (y - xbar))
      (fun y _ => (hG y).continuousAt.continuousWithinAt)
      (fun y _ => hG y)
    refine ⟨c, hsub (Set.Ioo_subset_Icc_self hc), ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hc.1]), abs_of_pos (by linarith)]
      linarith [hc.2]
    · have hc0 : c - xbar ≠ 0 := (by linarith [hc.1] : 0 < c - xbar).ne'
      rw [div_eq_iff hx0]
      simp only [hgx] at hcE
      have H : (c - xbar) * ((x - xbar) ^ 2 * f'' c - 2 * gg x) = 0 := by
        linear_combination hcE
      have H2 := (mul_eq_zero.1 H).resolve_left hc0
      linarith

theorem W2m_MetodosNumericos_newton_g_limit (f f' f'' : ℝ → ℝ) (a b xbar : ℝ)
    (hxbar : xbar ∈ Set.Ioo a b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x)
    (hf'' : ContinuousOn f'' (Set.Ioo a b)) :
    Tendsto (fun x => (f' x * (x - xbar) - f x + f xbar) / (x - xbar) ^ 2)
      (𝓝[≠] xbar) (𝓝 (f'' xbar / 2)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hcont : ContinuousAt f'' xbar := hf''.continuousAt (Ioo_mem_nhds hxbar.1 hxbar.2)
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.continuousAt_iff.1 hcont ε hε
  refine ⟨min δ1 (min (xbar - a) (b - xbar)),
    lt_min hδ1 (lt_min (by linarith [hxbar.1]) (by linarith [hxbar.2])), ?_⟩
  intro x hx hdist
  beta_reduce
  have hxne : x ≠ xbar := hx
  rw [Real.dist_eq] at hdist
  have h1 : |x - xbar| < δ1 := lt_of_lt_of_le hdist (min_le_left _ _)
  have h2 : |x - xbar| < xbar - a :=
    lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : |x - xbar| < b - xbar :=
    lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_right _ _))
  have hxmem : x ∈ Set.Ioo a b := by
    constructor
    · have := neg_abs_le (x - xbar); linarith
    · have := le_abs_self (x - xbar); linarith
  obtain ⟨c, -, hc1, hc2⟩ := W2m_MetodosNumericos_newton_mvt f f' f'' a b xbar hxbar hf hf' x
    hxne hxmem
  rw [hc2, Real.dist_eq]
  have hcd : dist c xbar < δ1 := by rw [Real.dist_eq]; linarith
  have H := hδ1' hcd
  rw [Real.dist_eq] at H
  rw [show f'' c / 2 - f'' xbar / 2 = (f'' c - f'' xbar) / 2 by ring, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem W2m_MetodosNumericos_newton_quadratic_order (f f' f'' : ℝ → ℝ) (a b xbar x0 : ℝ)
    (hxbar : xbar ∈ Set.Ioo a b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x)
    (hf'' : ContinuousOn f'' (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, f' x ≠ 0)
    (hroot : f xbar = 0)
    (hmem : ∀ n : ℕ, newtonSeq f f' x0 n ∈ Set.Ioo a b)
    (hsimple : ∀ n : ℕ, newtonSeq f f' x0 n ≠ xbar)
    (hconv : Tendsto (newtonSeq f f' x0) atTop (𝓝 xbar)) :
    Tendsto (fun n : ℕ =>
        |newtonSeq f f' x0 (n + 1) - xbar| / |newtonSeq f f' x0 n - xbar| ^ 2)
      atTop (𝓝 (|f'' xbar| / (2 * |f' xbar|))) := by
  have hL := W2m_MetodosNumericos_newton_g_limit f f' f'' a b xbar hxbar hf hf' hf''
  have hf'c : ContinuousAt f' xbar := (hf' xbar hxbar).continuousAt
  have hf'x : f' xbar ≠ 0 := hne xbar hxbar
  have hL2 : Tendsto (fun x => |(f' x * (x - xbar) - f x + f xbar) / (x - xbar) ^ 2| / |f' x|)
      (𝓝[≠] xbar) (𝓝 (|f'' xbar / 2| / |f' xbar|)) :=
    hL.abs.div (hf'c.abs.tendsto.mono_left nhdsWithin_le_nhds) (abs_ne_zero.2 hf'x)
  have hseq : Tendsto (newtonSeq f f' x0) atTop (𝓝[≠] xbar) :=
    tendsto_nhdsWithin_iff.2 ⟨hconv, Filter.Eventually.of_forall hsimple⟩
  have H := hL2.comp hseq
  rw [show |f'' xbar| / (2 * |f' xbar|) = |f'' xbar / 2| / |f' xbar| by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_div]]
  refine H.congr (fun n => ?_)
  have hn := hmem n
  have hfn : f' (newtonSeq f f' x0 n) ≠ 0 := hne _ hn
  have hxn : newtonSeq f f' x0 n - xbar ≠ 0 := sub_ne_zero.2 (hsimple n)
  show |(f' (newtonSeq f f' x0 n) * (newtonSeq f f' x0 n - xbar) - f (newtonSeq f f' x0 n)
      + f xbar) / (newtonSeq f f' x0 n - xbar) ^ 2| / |f' (newtonSeq f f' x0 n)|
    = |newtonSeq f f' x0 n - f (newtonSeq f f' x0 n) / f' (newtonSeq f f' x0 n) - xbar|
      / |newtonSeq f f' x0 n - xbar| ^ 2
  rw [hroot, add_zero]
  generalize newtonSeq f f' x0 n = y at hfn hxn ⊢
  rw [abs_div, ← abs_pow (y - xbar) 2]
  rw [show y - f y / f' y - xbar = (f' y * (y - xbar) - f y) / f' y by
    first | (field_simp; ring1) | field_simp]
  rw [abs_div, div_right_comm]

theorem W2m_MetodosNumericos_newton_local_convergence (f f' f'' : ℝ → ℝ) (a b xbar : ℝ)
    (hxbar : xbar ∈ Set.Ioo a b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x)
    (hf'' : ContinuousOn f'' (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, f' x ≠ 0)
    (hroot : f xbar = 0) :
    ∃ h > 0, Set.Icc (xbar - h) (xbar + h) ⊆ Set.Ioo a b ∧
      ∀ x0 ∈ Set.Icc (xbar - h) (xbar + h),
        Tendsto (newtonSeq f f' x0) atTop (𝓝 xbar) := by
  have ha := hxbar.1
  have hb := hxbar.2
  obtain ⟨δ0, hδ0, hδa, hδb⟩ : ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < xbar - a ∧ δ0 < b - xbar :=
    ⟨min (xbar - a) (b - xbar) / 2, by positivity,
      by linarith [min_le_left (xbar - a) (b - xbar)],
      by linarith [min_le_right (xbar - a) (b - xbar)]⟩
  have hS : Set.Icc (xbar - δ0) (xbar + δ0) ⊆ Set.Ioo a b := by
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := xbar - δ0) (b := xbar + δ0)).exists_bound_of_continuousOn
    (hf''.mono hS)
  have hf'cont : ContinuousOn f' (Set.Icc (xbar - δ0) (xbar + δ0)) :=
    fun x hx => (hf' x (hS hx)).continuousAt.continuousWithinAt
  obtain ⟨p, hpS, hpmin⟩ := (isCompact_Icc (a := xbar - δ0) (b := xbar + δ0)).exists_isMinOn
    (Set.nonempty_Icc.2 (by linarith)) hf'cont.abs
  have hm : 0 < |f' p| := abs_pos.2 (hne p (hS hpS))
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK xbar ⟨by linarith, by linarith⟩)
  obtain ⟨h, hh0, hhδ, hhm⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ δ0 ∧ h ≤ |f' p| / (K + 1) :=
    ⟨min δ0 (|f' p| / (K + 1)), lt_min hδ0 (by positivity), min_le_left _ _, min_le_right _ _⟩
  refine ⟨h, hh0, fun y hy => hS ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
  intro x0 hx0
  have hstep : ∀ x ∈ Set.Icc (xbar - h) (xbar + h),
      |x - f x / f' x - xbar| ≤ |x - xbar| / 2 := by
    intro x hx
    have hxS : x ∈ Set.Icc (xbar - δ0) (xbar + δ0) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxab := hS hxS
    have hfx : f' x ≠ 0 := hne x hxab
    have hmx : |f' p| ≤ |f' x| := isMinOn_iff.1 hpmin x hxS
    have habs : |x - xbar| ≤ h := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    by_cases hxe : x = xbar
    · subst hxe
      rw [hroot]
      simp
    · obtain ⟨c, -, hc1, hc2⟩ := W2m_MetodosNumericos_newton_mvt f f' f'' a b xbar hxbar hf hf'
        x hxe hxab
      rw [hroot, add_zero] at hc2
      have hcS : c ∈ Set.Icc (xbar - δ0) (xbar + δ0) := by
        have := abs_lt.1 (lt_of_lt_of_le hc1 (le_trans habs hhδ))
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      have hKc : |f'' c| ≤ K := by
        have := hK c hcS
        rwa [Real.norm_eq_abs] at this
      have hx0 : x - xbar ≠ 0 := sub_ne_zero.2 hxe
      have eN : x - f x / f' x - xbar = (x - xbar) ^ 2 * (f'' c / 2) / f' x := by
        rw [← hc2]
        first | (field_simp; ring1) | field_simp
      have hfxpos : 0 < |f' x| := lt_of_lt_of_le hm hmx
      rw [eN, abs_div, abs_mul, abs_div, abs_pow, abs_of_pos (two_pos : (0 : ℝ) < 2),
        div_le_iff₀ hfxpos]
      have h1 : |x - xbar| * (K + 1) ≤ |f' x| := by
        have := le_trans habs hhm
        rw [le_div_iff₀ (by positivity)] at this
        linarith
      have he := abs_nonneg (x - xbar)
      nlinarith [mul_le_mul_of_nonneg_left hKc (sq_nonneg |x - xbar|),
        mul_le_mul_of_nonneg_left h1 he]
  have hind : ∀ n, newtonSeq f f' x0 n ∈ Set.Icc (xbar - h) (xbar + h) ∧
      |newtonSeq f f' x0 n - xbar| ≤ (1 / 2) ^ n * |x0 - xbar| := by
    intro n
    induction n with
    | zero => exact ⟨hx0, by simp [newtonSeq]⟩
    | succ n ih =>
      have H := hstep _ ih.1
      have e : newtonSeq f f' x0 (n + 1) = newtonSeq f f' x0 n
          - f (newtonSeq f f' x0 n) / f' (newtonSeq f f' x0 n) := rfl
      rw [e]
      have h1 : |newtonSeq f f' x0 n - xbar| ≤ h :=
        abs_le.2 ⟨by linarith [ih.1.1], by linarith [ih.1.2]⟩
      constructor
      · have h2 : |newtonSeq f f' x0 n - f (newtonSeq f f' x0 n) / f' (newtonSeq f f' x0 n)
            - xbar| ≤ h := by
          linarith [abs_nonneg (newtonSeq f f' x0 n - xbar)]
        have h3 := abs_le.1 h2
        constructor <;> linarith [h3.1, h3.2]
      · calc _ ≤ |newtonSeq f f' x0 n - xbar| / 2 := H
          _ ≤ (1 / 2) ^ n * |x0 - xbar| / 2 := by linarith [ih.2]
          _ = (1 / 2) ^ (n + 1) * |x0 - xbar| := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * |x0 - xbar|) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const |x0 - xbar|
    rwa [zero_mul] at this
  exact squeeze_zero (g := fun n : ℕ => (1 / 2 : ℝ) ^ n * |x0 - xbar|)
    (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact (hind n).2) hlim

theorem W2m_MetodosNumericos_trapezoid_simple_error (f : ℝ → ℝ) (x0 h : ℝ) (hh : 0 < h)
    (hf : ContDiffOn ℝ 2 f (Set.Icc x0 (x0 + h))) :
    ∃ mu ∈ Set.Ioo x0 (x0 + h),
      ∫ t in x0..(x0 + h), f t =
        h / 2 * (f x0 + f (x0 + h))
          - h ^ 3 * iteratedDerivWithin 2 f (Set.Icc x0 (x0 + h)) mu / 12 := by
  have hlt : x0 < x0 + h := by linarith
  have hU : UniqueDiffOn ℝ (Set.Icc x0 (x0 + h)) := uniqueDiffOn_Icc hlt
  have hfc : ContinuousOn f (Set.Icc x0 (x0 + h)) := hf.continuousOn
  have hD1c : ContDiffOn ℝ 1 (derivWithin f (Set.Icc x0 (x0 + h))) (Set.Icc x0 (x0 + h)) :=
    hf.derivWithin hU (by norm_num)
  have hD1cont := hD1c.continuousOn
  have hnhds : ∀ y ∈ Set.Ioo x0 (x0 + h), Set.Icc x0 (x0 + h) ∈ 𝓝 y :=
    fun y hy => Icc_mem_nhds hy.1 hy.2
  have hfd : ∀ y ∈ Set.Ioo x0 (x0 + h),
      HasDerivAt f (derivWithin f (Set.Icc x0 (x0 + h)) y) y := by
    intro y hy
    have hdw : DifferentiableWithinAt ℝ f (Set.Icc x0 (x0 + h)) y :=
      (hf.differentiableOn (by norm_num)) y (Set.Ioo_subset_Icc_self hy)
    have hd : DifferentiableAt ℝ f y := hdw.differentiableAt (hnhds y hy)
    rw [derivWithin_of_mem_nhds (hnhds y hy)]
    exact hd.hasDerivAt
  have hD1d : ∀ y ∈ Set.Ioo x0 (x0 + h), HasDerivAt (derivWithin f (Set.Icc x0 (x0 + h)))
      (iteratedDerivWithin 2 f (Set.Icc x0 (x0 + h)) y) y := by
    intro y hy
    have hdw : DifferentiableWithinAt ℝ (derivWithin f (Set.Icc x0 (x0 + h)))
        (Set.Icc x0 (x0 + h)) y :=
      (hD1c.differentiableOn (by norm_num)) y (Set.Ioo_subset_Icc_self hy)
    have hd := hdw.differentiableAt (hnhds y hy)
    have e : iteratedDerivWithin 2 f (Set.Icc x0 (x0 + h)) y
        = derivWithin (derivWithin f (Set.Icc x0 (x0 + h))) (Set.Icc x0 (x0 + h)) y := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one]
    rw [e, derivWithin_of_mem_nhds (hnhds y hy)]
    exact hd.hasDerivAt
  have hint : MeasureTheory.IntegrableOn f (Set.uIcc x0 (x0 + h)) := by
    rw [Set.uIcc_of_le hlt.le]
    exact hfc.integrableOn_compact isCompact_Icc
  have hIc : ContinuousOn (fun y => ∫ t in x0..y, f t) (Set.Icc x0 (x0 + h)) := by
    have H := intervalIntegral.continuousOn_primitive_interval hint
    rwa [Set.uIcc_of_le hlt.le] at H
  have hId : ∀ y ∈ Set.Ioo x0 (x0 + h), HasDerivAt (fun y => ∫ t in x0..y, f t) (f y) y := by
    intro y hy
    have hsub : Set.uIcc x0 y ⊆ Set.Icc x0 (x0 + h) := by
      rw [Set.uIcc_of_le hy.1.le]
      exact Set.Icc_subset_Icc le_rfl hy.2.le
    exact intervalIntegral.integral_hasDerivAt_right ((hfc.mono hsub).intervalIntegrable)
      ((hfc.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo y hy)
      (hfc.continuousAt (hnhds y hy))
  set D1 := derivWithin f (Set.Icc x0 (x0 + h)) with hD1
  set D2 := iteratedDerivWithin 2 f (Set.Icc x0 (x0 + h)) with hD2
  set Eh := (∫ t in x0..(x0 + h), f t) - h / 2 * (f x0 + f (x0 + h)) with hEh
  have hh' : h ≠ 0 := hh.ne'
  -- first auxiliary function
  have hφc : ContinuousOn (fun y => (∫ t in x0..y, f t) - (y - x0) / 2 * (f x0 + f y)
      - ((y - x0) / h) ^ 3 * Eh) (Set.Icc x0 (x0 + h)) := by
    refine ContinuousOn.sub (ContinuousOn.sub hIc ?_) (by fun_prop)
    exact (by fun_prop : ContinuousOn (fun y : ℝ => (y - x0) / 2) _).mul
      (continuousOn_const.add hfc)
  have hφd : ∀ y ∈ Set.Ioo x0 (x0 + h), HasDerivAt (fun y => (∫ t in x0..y, f t)
      - (y - x0) / 2 * (f x0 + f y) - ((y - x0) / h) ^ 3 * Eh)
      (f y - (1 / 2 * (f x0 + f y) + (y - x0) / 2 * D1 y)
        - 3 * ((y - x0) / h) ^ 2 * (1 / h) * Eh) y := by
    intro y hy
    have h1 := (((hasDerivAt_id' y).sub_const x0).div_const 2).fun_mul
      ((hfd y hy).const_add (f x0))
    have h2 := ((((hasDerivAt_id' y).sub_const x0).div_const h).fun_pow 3).mul_const Eh
    refine (((hId y hy).fun_sub h1).fun_sub h2).congr_deriv ?_
    first | ring1 | (norm_num; ring1) | norm_num | (simp; ring1)
  have hφ0 : (fun y => (∫ t in x0..y, f t) - (y - x0) / 2 * (f x0 + f y)
      - ((y - x0) / h) ^ 3 * Eh) x0 = (fun y => (∫ t in x0..y, f t)
      - (y - x0) / 2 * (f x0 + f y) - ((y - x0) / h) ^ 3 * Eh) (x0 + h) := by
    simp only [intervalIntegral.integral_same, sub_self, add_sub_cancel_left, div_self hh']
    rw [hEh]
    ring
  obtain ⟨y1, hy1, hy1'⟩ := exists_hasDerivAt_eq_zero hlt hφc hφ0 hφd
  -- second auxiliary function
  have hψc : ContinuousOn (fun y => (f y - f x0) / 2 - (y - x0) * D1 y / 2
      - 3 * (y - x0) ^ 2 / h ^ 3 * Eh) (Set.Icc x0 y1) := by
    have hsub : Set.Icc x0 y1 ⊆ Set.Icc x0 (x0 + h) := Set.Icc_subset_Icc le_rfl hy1.2.le
    have c1 := hfc.mono hsub
    have c2 := hD1cont.mono hsub
    refine ContinuousOn.sub (ContinuousOn.sub ?_ ?_) (by fun_prop)
    · exact (c1.sub continuousOn_const).div_const 2
    · exact ((continuousOn_id.sub continuousOn_const).mul c2).div_const 2
  have hψd : ∀ y ∈ Set.Ioo x0 y1, HasDerivAt (fun y => (f y - f x0) / 2 - (y - x0) * D1 y / 2
      - 3 * (y - x0) ^ 2 / h ^ 3 * Eh)
      (-((y - x0) * (D2 y / 2 + 6 * Eh / h ^ 3))) y := by
    intro y hy
    have hy' : y ∈ Set.Ioo x0 (x0 + h) := ⟨hy.1, lt_trans hy.2 hy1.2⟩
    have h1 := ((hfd y hy').sub_const (f x0)).div_const 2
    have h2 := (((hasDerivAt_id' y).sub_const x0).fun_mul (hD1d y hy')).div_const 2
    have h3 := ((((hasDerivAt_id' y).sub_const x0).fun_pow 2).const_mul 3).div_const (h ^ 3)
      |>.mul_const Eh
    refine ((h1.fun_sub h2).fun_sub h3).congr_deriv ?_
    first | ring1 | (norm_num; ring1) | (norm_num; field_simp; ring1) | norm_num
  have hψ0 : (fun y => (f y - f x0) / 2 - (y - x0) * D1 y / 2
      - 3 * (y - x0) ^ 2 / h ^ 3 * Eh) x0 = (fun y => (f y - f x0) / 2 - (y - x0) * D1 y / 2
      - 3 * (y - x0) ^ 2 / h ^ 3 * Eh) y1 := by
    have H := hy1'
    simp only
    have e : (f y1 - f x0) / 2 - (y1 - x0) * D1 y1 / 2 - 3 * (y1 - x0) ^ 2 / h ^ 3 * Eh
        = f y1 - (1 / 2 * (f x0 + f y1) + (y1 - x0) / 2 * D1 y1)
          - 3 * ((y1 - x0) / h) ^ 2 * (1 / h) * Eh := by
      first | (field_simp; ring1) | ring1
    rw [e, H]
    ring
  obtain ⟨y2, hy2, hy2'⟩ := exists_hasDerivAt_eq_zero hy1.1 hψc hψ0 hψd
  have hy2pos : 0 < y2 - x0 := by linarith [hy2.1]
  have key : D2 y2 / 2 + 6 * Eh / h ^ 3 = 0 := by
    have := neg_eq_zero.1 hy2'
    exact (mul_eq_zero.1 this).resolve_left hy2pos.ne'
  refine ⟨y2, ⟨hy2.1, lt_trans hy2.2 hy1.2⟩, ?_⟩
  have hEh' : Eh = -(h ^ 3 * D2 y2 / 12) := by
    have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh'
    have h6 : 6 * Eh / h ^ 3 = -(D2 y2 / 2) := by linarith
    rw [div_eq_iff hh3] at h6
    linear_combination h6 / 6
  have : (∫ t in x0..(x0 + h), f t) = Eh + h / 2 * (f x0 + f (x0 + h)) := by
    rw [hEh]; ring
  rw [this, hEh']
  ring

theorem W2m_MetodosNumericos_iter2_eq (f : ℝ → ℝ) (s : Set ℝ) (y : ℝ) (hs : s ∈ 𝓝 y) :
    iteratedDerivWithin 2 f s y = deriv (deriv f) y := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one,
    derivWithin_of_mem_nhds hs]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_mem_nhds_iff.2 hs] with z hz
  exact derivWithin_of_mem_nhds hz

theorem W2m_MetodosNumericos_trapezoid_composite_error (f : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hab : a < b) (hn : 0 < n)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b)) :
    ∃ mu ∈ Set.Ioo a b,
      ∫ t in a..b, f t =
        trapezoidRule f a b n
          - (b - a) * ((b - a) / n) ^ 2 * iteratedDerivWithin 2 f (Set.Icc a b) mu / 12 := by
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = (b - a) / n := ⟨_, rfl⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0' : (n : ℝ) ≠ 0 := hnR.ne'
  have hh : 0 < h := by rw [hh_def]; exact div_pos (by linarith) hnR
  have hbh : a + n * h = b := by
    rw [hh_def]; first | (field_simp; ring1) | field_simp
  have hsub : ∀ i < n, Set.Icc (a + i * h) (a + i * h + h) ⊆ Set.Icc a b := by
    intro i hi y hy
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_right hi' hh.le
    have hm0 := mul_nonneg hi0 hh.le
    constructor
    · nlinarith [hy.1]
    · nlinarith [hy.2]
  have hloc : ∀ i < n, ∃ mu ∈ Set.Ioo (a + i * h) (a + i * h + h),
      ∫ t in (a + i * h)..(a + i * h + h), f t =
        h / 2 * (f (a + i * h) + f (a + i * h + h))
          - h ^ 3 * iteratedDerivWithin 2 f (Set.Icc a b) mu / 12 := by
    intro i hi
    obtain ⟨mu, hmu, heq⟩ := W2m_MetodosNumericos_trapezoid_simple_error f (a + i * h) h hh
      (hf.mono (hsub i hi))
    refine ⟨mu, hmu, ?_⟩
    have hmab : mu ∈ Set.Icc a b := hsub i hi (Set.Ioo_subset_Icc_self hmu)
    have hmab' : a < mu ∧ mu < b := by
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
      have hm := mul_le_mul_of_nonneg_right hi' hh.le
      have hm0 := mul_nonneg hi0 hh.le
      constructor
      · nlinarith [hmu.1]
      · nlinarith [hmu.2]
    rw [heq, W2m_MetodosNumericos_iter2_eq f _ _ (Icc_mem_nhds hmu.1 hmu.2),
      W2m_MetodosNumericos_iter2_eq f _ _ (Icc_mem_nhds hmab'.1 hmab'.2)]
  choose! μ hμ hμeq using hloc
  have hμab : ∀ i < n, μ i ∈ Set.Ioo a b := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    have := hμ i hi
    have hm := mul_le_mul_of_nonneg_right hi' hh.le
    have hm0 := mul_nonneg hi0 hh.le
    constructor
    · nlinarith [this.1]
    · nlinarith [this.2]
  have hsucc : ∀ i : ℕ, a + ((i + 1 : ℕ) : ℝ) * h = a + i * h + h := by
    intro i; push_cast; ring
  have hsum : ∑ i ∈ Finset.range n, ∫ t in (a + (i : ℕ) * h)..(a + ((i + 1 : ℕ) : ℝ) * h), f t
      = ∫ t in a..b, f t := by
    have hint : ∀ k < n, IntervalIntegrable f MeasureTheory.volume (a + (k : ℝ) * h)
        (a + ((k + 1 : ℕ) : ℝ) * h) := by
      intro k hk
      apply ContinuousOn.intervalIntegrable
      apply hf.continuousOn.mono
      rw [Set.uIcc_of_le (by rw [hsucc]; linarith)]
      rw [hsucc]
      exact hsub k hk
    have H := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (f := f) (a := fun i : ℕ => a + (i : ℝ) * h) (n := n) hint
    beta_reduce at H
    rw [Nat.cast_zero, zero_mul, add_zero, hbh] at H
    exact H
  set D2 := iteratedDerivWithin 2 f (Set.Icc a b) with hD2
  have hD2c : ContinuousOn D2 (Set.Icc a b) :=
    hf.continuousOn_iteratedDerivWithin (by norm_num) (uniqueDiffOn_Icc hab)
  have hne : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.2 hn⟩
  obtain ⟨imin, himin, hmin⟩ := Finset.exists_min_image (Finset.range n) (fun i => D2 (μ i)) hne
  obtain ⟨imax, himax, hmax⟩ := Finset.exists_max_image (Finset.range n) (fun i => D2 (μ i)) hne
  have havg1 : D2 (μ imin) ≤ (∑ i ∈ Finset.range n, D2 (μ i)) / n := by
    rw [le_div_iff₀ hnR]
    have := Finset.card_nsmul_le_sum (Finset.range n) (fun i => D2 (μ i)) (D2 (μ imin)) hmin
    rw [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have havg2 : (∑ i ∈ Finset.range n, D2 (μ i)) / n ≤ D2 (μ imax) := by
    rw [div_le_iff₀ hnR]
    have := Finset.sum_le_card_nsmul (Finset.range n) (fun i => D2 (μ i)) (D2 (μ imax)) hmax
    rw [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hseg : Set.uIcc (μ imin) (μ imax) ⊆ Set.Ioo a b :=
    Set.ordConnected_Ioo.uIcc_subset (hμab imin (Finset.mem_range.1 himin))
      (hμab imax (Finset.mem_range.1 himax))
  obtain ⟨μ0, hμ0, hμ0eq⟩ := intermediate_value_uIcc
    (hD2c.mono (hseg.trans Set.Ioo_subset_Icc_self)) (Set.mem_uIcc.2 (Or.inl ⟨havg1, havg2⟩))
  refine ⟨μ0, hseg hμ0, ?_⟩
  rw [← hsum]
  have hterm : ∀ i ∈ Finset.range n,
      ∫ t in (a + (i : ℕ) * h)..(a + ((i + 1 : ℕ) : ℝ) * h), f t
        = h / 2 * (f (a + i * h) + f (a + ((i + 1 : ℕ) : ℝ) * h)) - h ^ 3 * D2 (μ i) / 12 := by
    intro i hi
    rw [hsucc]
    exact hμeq i (Finset.mem_range.1 hi)
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have htrap : h / 2 * ∑ i ∈ Finset.range n, (f (a + i * h) + f (a + ((i + 1 : ℕ) : ℝ) * h))
      = trapezoidRule f a b n := by
    simp only [trapezoidRule]
    rw [← hh_def, Finset.sum_add_distrib]
    have h1 : ∑ i ∈ Finset.range n, f (a + (i : ℕ) * h)
        = f a + ∑ i ∈ Finset.Ico 1 n, f (a + (i : ℕ) * h) := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
      simp
    have h2 : ∑ i ∈ Finset.range n, f (a + ((i + 1 : ℕ) : ℝ) * h)
        = ∑ i ∈ Finset.Ico 1 n, f (a + (i : ℕ) * h) + f b := by
      have e := Finset.sum_range_succ' (fun i : ℕ => f (a + (i : ℝ) * h)) n
      have e2 := Finset.sum_range_succ (fun i : ℕ => f (a + (i : ℝ) * h)) n
      beta_reduce at e e2
      rw [Nat.cast_zero, zero_mul, add_zero] at e
      rw [← hbh]
      linarith [h1]
    rw [h1, h2]
    ring
  have hμ0' : D2 μ0 = (∑ i ∈ Finset.range n, D2 (μ i)) / n := hμ0eq
  rw [htrap, hμ0']
  have hba : b - a = n * h := by rw [← hbh]; ring
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  rw [hba]
  first | (field_simp; ring1) | field_simp | ring1

theorem solution (f f' f'' : ℝ → ℝ) (a b xbar : ℝ)
    (hxbar : xbar ∈ Set.Ioo a b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x)
    (hf'' : ContinuousOn f'' (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, f' x ≠ 0)
    (hroot : f xbar = 0) :
    ∃ h > 0, Set.Icc (xbar - h) (xbar + h) ⊆ Set.Ioo a b ∧
      ∀ x0 ∈ Set.Icc (xbar - h) (xbar + h),
        Tendsto (newtonSeq f f' x0) atTop (𝓝 xbar) := by
  apply W2m_MetodosNumericos_newton_local_convergence <;> assumption
