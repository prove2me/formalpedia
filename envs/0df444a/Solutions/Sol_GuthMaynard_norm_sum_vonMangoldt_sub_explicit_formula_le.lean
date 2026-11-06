-- Prove2me | solution 1 for GuthMaynard.norm_sum_vonMangoldt_sub_explicit_formula_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:33:24.783193+00:00
-- url     : https://prove2.me/submissions/151aa6ac-7598-43d0-9fe0-db83a1c392e6

import Mathlib
import Theorems.Thm_GuthMaynard_davenport_truncated_explicit_formula
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count

open Finset

namespace GuthMaynard.CitedZeros


lemma ceil_eq_floor_add_one_of_ne {x : ℝ} (hx : 0 ≤ x) (h : ¬ ((⌊x⌋₊:ℕ):ℝ) = x) :
    ⌈x⌉₊ = ⌊x⌋₊ + 1 := by
  rw [Nat.ceil_eq_iff (by omega)]
  simp only [Nat.add_sub_cancel]
  exact ⟨lt_of_le_of_ne (Nat.floor_le hx) h, (Nat.lt_floor_add_one x).le.trans (by push_cast; rfl)⟩

lemma sum_Icc_vonMangoldt_eq {x u : ℝ} (hx : 0 < x) (hxu : x ≤ u) :
    ∑ n ∈ Icc ⌈x⌉₊ ⌊u⌋₊, ArithmeticFunction.vonMangoldt n =
      Chebyshev.psi u - Chebyshev.psi x +
        (if ((⌊x⌋₊:ℕ):ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ else 0) := by
  have h1 : ⌈x⌉₊ ≤ ⌊u⌋₊ + 1 :=
    (Nat.ceil_le_floor_add_one x).trans (by have := Nat.floor_le_floor (R := ℝ) hxu; omega)
  have hsplit := Finset.sum_Ico_consecutive (fun n => ArithmeticFunction.vonMangoldt n)
    (Nat.zero_le ⌈x⌉₊) h1
  have hIcc : ∀ a b : ℕ, Icc a b = Ico a (b + 1) := fun a b => by
    ext n; simp
  rw [Chebyshev.psi_eq_sum_Icc u, Chebyshev.psi_eq_sum_Icc x]
  simp only [hIcc]
  rw [← hsplit]
  split_ifs with h
  · have hc : ⌈x⌉₊ = ⌊x⌋₊ := by
      rw [← h]; simp
    rw [hc, Finset.sum_Ico_succ_top (Nat.zero_le _)]
    ring
  · rw [ceil_eq_floor_add_one_of_ne hx.le h]
    ring



lemma half_le_log {x : ℝ} (hx : 2 ≤ x) : 1 / 2 ≤ Real.log x := by
  have := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) hx
  norm_num at *; linarith

lemma log_le_mul_log {x v : ℝ} (n : ℕ) (_hx : 2 ≤ x) (hv : 0 < v) (hvx : v ≤ x ^ n) :
    Real.log v ≤ n * Real.log x := by
  rw [← Real.log_pow]; exact Real.log_le_log hv hvx

lemma davenport_term_le {C x T v w : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) (hTx : T ≤ x)
    (hxv : x ≤ v) (hv : v ≤ 2 * x) (hw : 0 ≤ w) :
    C * (v * Real.log (v * T) ^ 2 / T + Real.log v * min 1 w) ≤
      |C| * (44 * (x * Real.log x ^ 3 / T)) := by
  set ℓ := Real.log x with hℓdef
  have hℓ : 1 / 2 ≤ ℓ := half_le_log hx
  have hTpos : 0 < T := by linarith
  have hvpos : 0 < v := by linarith
  have hL0 : 0 ≤ Real.log (v * T) := Real.log_nonneg (by nlinarith)
  have hL : Real.log (v * T) ≤ 3 * ℓ := by
    have h1 : v * T ≤ (2 * x) * x := mul_le_mul hv hTx hTpos.le (by linarith)
    have := log_le_mul_log 3 hx (by positivity) (show v * T ≤ x ^ 3 by
      nlinarith [mul_nonneg (sub_nonneg.2 hx) (mul_self_nonneg x)])
    simpa using this
  have hl0 : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  have hl : Real.log v ≤ 2 * ℓ := by
    have := log_le_mul_log 2 hx hvpos (show v ≤ x ^ 2 by nlinarith)
    simpa using this
  have hm0 : 0 ≤ min 1 w := le_min zero_le_one hw
  have hm1 : min 1 w ≤ 1 := min_le_left _ _
  set q := x / T with hq
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hTpos]; linarith
  have hvT : v / T ≤ 2 * q := by rw [hq, mul_div_assoc']; exact div_le_div_of_nonneg_right hv hTpos.le
  have hA0 : 0 ≤ v * Real.log (v * T) ^ 2 / T + Real.log v * min 1 w := by positivity
  have hA : v * Real.log (v * T) ^ 2 / T + Real.log v * min 1 w ≤ 44 * (q * ℓ ^ 3) := by
    have e1 : v * Real.log (v * T) ^ 2 / T = (v / T) * Real.log (v * T) ^ 2 := by ring
    have h2 : Real.log (v * T) ^ 2 ≤ 9 * ℓ ^ 2 := by nlinarith
    have h3 : (v / T) * Real.log (v * T) ^ 2 ≤ (2 * q) * (9 * ℓ ^ 2) :=
      mul_le_mul hvT h2 (by positivity) (by positivity)
    have h4 : Real.log v * min 1 w ≤ 2 * ℓ := by nlinarith
    have h5 : ℓ ^ 2 ≤ 2 * ℓ ^ 3 := by nlinarith
    have h6 : ℓ ≤ 4 * ℓ ^ 3 := by
      have hl2 : 1 ≤ 4 * ℓ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hl2 (show 0 ≤ ℓ by linarith)]
    have h7 : ℓ ^ 3 ≤ q * ℓ ^ 3 := by nlinarith [pow_pos (show 0 < ℓ by linarith) 3]
    have h8 : q * ℓ ^ 2 ≤ 2 * (q * ℓ ^ 3) := by nlinarith
    nlinarith
  have e : x * ℓ ^ 3 / T = q * ℓ ^ 3 := by rw [hq]; ring
  rw [e]
  calc C * _ ≤ |C| * _ := mul_le_mul_of_nonneg_right (le_abs_self C) hA0
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (abs_nonneg C)

lemma abs_log_one_sub_le {v : ℝ} (hv : 2 ≤ v) : |Real.log (1 - v ^ (-2 : ℝ))| ≤ 1 := by
  have e : v ^ (-2 : ℝ) = (v ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by linarith)]; norm_cast
  rw [e]
  have h4 : 4 ≤ v ^ 2 := by nlinarith
  have ht0 : 0 < (v ^ 2)⁻¹ := by positivity
  have ht : (v ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; norm_num; linarith
  rw [abs_le]
  constructor
  · have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - (v ^ 2)⁻¹ by linarith)
    have h' : (1 - (v ^ 2)⁻¹)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  · have := Real.log_nonpos (show 0 ≤ 1 - (v ^ 2)⁻¹ by linarith) (by linarith)
    linarith

/-- the half-weight boundary term -/
noncomputable def bdry (v : ℝ) : ℝ :=
  if ((⌊v⌋₊ : ℕ) : ℝ) = v then ArithmeticFunction.vonMangoldt ⌊v⌋₊ / 2 else 0

lemma bdry_nonneg (v : ℝ) : 0 ≤ bdry v := by
  unfold bdry; split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by norm_num)
  · exact le_rfl

lemma bdry_le {v : ℝ} (hv : 1 ≤ v) : bdry v ≤ Real.log v / 2 := by
  unfold bdry; split_ifs
  · have h1 : (1 : ℝ) ≤ ⌊v⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro h; rw [Nat.floor_eq_zero] at h; linarith)
    have := (ArithmeticFunction.vonMangoldt_le_log (n := ⌊v⌋₊)).trans
      (Real.log_le_log (by linarith) (Nat.floor_le (by linarith)))
    linarith
  · exact div_nonneg (Real.log_nonneg hv) (by norm_num)



/-- the zero set of the Davenport formula -/
def zsetT (T : ℝ) : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T}

lemma zsetT_finite (T : ℝ) : (zsetT T).Finite :=
  (Zeta23.zetaSeam.finite_window (-T) T).subset fun _ ⟨h1, h2, h3, h4⟩ =>
    ⟨⟨h1, h2, h3⟩, (abs_lt.1 h4).1, (abs_lt.1 h4).2.le⟩

lemma zsetN_eq (T : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T} =
      ↑((zsetT_finite T).toFinset.filter (fun ρ => ‖ρ‖ ≤ T)) := by
  ext ρ
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, zsetT]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3, lt_of_lt_of_le (Complex.abs_im_lt_norm.2 h2.ne') h4⟩, h4⟩
  · rintro ⟨⟨h1, h2, h3, _⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩

lemma window_finite (a b : ℝ) : (Zeta23.zerosIn a b).Finite := Zeta23.zetaSeam.finite_window a b

lemma Ncount_eq (a b : ℝ) :
    Zeta23.Ncount a b = ∑ ρ ∈ (window_finite a b).toFinset, Zeta23.zeroMult ρ :=
  finsum_mem_eq_finite_toFinset_sum _ _

lemma far_subset (T : ℝ) :
    (zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T) ⊆
      (window_finite (T - 1) T).toFinset ∪ (window_finite (-T) (-T + 1)).toFinset := by
  intro ρ hρ
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, zsetT, Set.mem_ofPred_eq] at hρ
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hρ
  have hn := Complex.norm_le_abs_re_add_abs_im ρ
  rw [abs_of_pos h2] at hn
  have hgt : T - 1 < |ρ.im| := by linarith [not_le.1 h5]
  rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
  simp only [Zeta23.zerosIn, Set.mem_ofPred_eq, Zeta23.IsNontrivialZero]
  obtain ⟨h4a, h4b⟩ := abs_lt.1 h4
  rcases le_or_gt 0 ρ.im with him | him
  · rw [abs_of_nonneg him] at hgt
    exact Or.inl ⟨⟨h1, h2, h3⟩, hgt, h4b.le⟩
  · rw [abs_of_neg him] at hgt
    exact Or.inr ⟨⟨h1, h2, h3⟩, h4a, by linarith⟩

lemma far_count_le (T : ℝ) :
    ∑ ρ ∈ (zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T), analyticOrderNatAt riemannZeta ρ ≤
      Zeta23.Ncount (T - 1) T + Zeta23.Ncount (-T) (-T + 1) := by
  classical
  rw [Ncount_eq, Ncount_eq]
  have h1 := Finset.sum_le_sum_of_subset (f := Zeta23.zeroMult) (far_subset T)
  have h2 := Finset.sum_union_inter (f := Zeta23.zeroMult)
    (s₁ := (window_finite (T - 1) T).toFinset) (s₂ := (window_finite (-T) (-T + 1)).toFinset)
  exact h1.trans (by omega)

lemma far_count_le_real {A₀ T x : ℝ} (hA : ∀ t : ℝ, (Zeta23.Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hA0 : 0 ≤ A₀) (hT : 2 ≤ T) (hTx : T ≤ x) :
    (∑ ρ ∈ (zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
      (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ 6 * A₀ * Real.log x := by
  have h := far_count_le T
  have h' : (∑ ρ ∈ (zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
      (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      (Zeta23.Ncount (T - 1) T : ℝ) + Zeta23.Ncount (-T) (-T + 1) := by
    exact_mod_cast h
  have e1 := hA (T - 1)
  have e2 := hA (-T)
  rw [show T - 1 + 1 = T by ring] at e1
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ T - 1)] at e1
  rw [abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ T)] at e2
  have l1 : Real.log (T - 1 + 3) ≤ Real.log (T + 3) := Real.log_le_log (by linarith) (by linarith)
  have l2 : Real.log (T + 3) ≤ 3 * Real.log x := by
    rw [show (3:ℝ) * Real.log x = Real.log (x ^ 3) by rw [Real.log_pow]; norm_num]
    refine Real.log_le_log (by linarith) ?_
    nlinarith [mul_nonneg (sub_nonneg.2 (show (2:ℝ) ≤ x by linarith)) (mul_self_nonneg x)]
  have m1 := mul_le_mul_of_nonneg_left (l1.trans l2) hA0
  have m2 := mul_le_mul_of_nonneg_left l2 hA0
  linarith

lemma far_norm_le {m : ℂ → ℕ} (D : Finset ℂ) {x u T : ℝ} (hx : 1 ≤ x) (hxu : x ≤ u) (hu : u ≤ 2 * x)
    (hT : 0 < T) (hD : ∀ ρ ∈ D, ρ.re < 1 ∧ T < ‖ρ‖) :
    ‖∑ ρ ∈ D, (m ρ : ℂ) * (((u : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ≤
      3 * x / T * ∑ ρ ∈ D, (m ρ : ℝ) := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  obtain ⟨h1, h2⟩ := hD ρ hρ
  have hρ0 : 0 < ‖ρ‖ := hT.trans h2
  rw [norm_mul, norm_div, Complex.norm_natCast]
  have hu' : ‖(u : ℂ) ^ ρ‖ ≤ u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ u) h1.le
  have hx' : ‖(x : ℂ) ^ ρ‖ ≤ x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simpa using Real.rpow_le_rpow_of_exponent_le hx h1.le
  have hn : ‖(u : ℂ) ^ ρ - (x : ℂ) ^ ρ‖ ≤ 3 * x := (norm_sub_le _ _).trans (by linarith)
  have : ‖(u : ℂ) ^ ρ - (x : ℂ) ^ ρ‖ / ‖ρ‖ ≤ 3 * x / T :=
    div_le_div₀ (by linarith) hn hT h2.le
  have hm : (0:ℝ) ≤ m ρ := Nat.cast_nonneg _
  nlinarith


/-- Davenport's expression at `v` (with the half-weight boundary term written as `bdry v`). -/
noncomputable def dav (T v : ℝ) : ℂ :=
  (((Chebyshev.psi v - bdry v - v : ℝ)) : ℂ) +
    (∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T},
      (analyticOrderNatAt riemannZeta ρ : ℂ) * (v : ℂ) ^ ρ / ρ) +
    ((Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - v ^ (-2 : ℝ)) : ℝ) : ℂ)

lemma dav_le {C : ℝ} (hC : ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
      ‖(((Chebyshev.psi x -
            (if ((⌊x⌋₊ : ℕ) : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2 else 0) - x : ℝ)) : ℂ) +
          (∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T},
            (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) +
          ((Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)‖ ≤
        C * (x * Real.log (x * T) ^ 2 / T +
          Real.log x * min 1 (x / (T * sInf {d : ℝ | ∃ n : ℕ, IsPrimePow n ∧ (n : ℝ) ≠ x ∧
            d = |x - n|}))))
    {x T v : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) (hTx : T ≤ x) (hxv : x ≤ v) (hv : v ≤ 2 * x) :
    ‖dav T v‖ ≤ |C| * (44 * (x * Real.log x ^ 3 / T)) := by
  refine (hC v T (by linarith) hT).trans (davenport_term_le hx hT hTx hxv hv ?_)
  refine div_nonneg (by linarith) (mul_nonneg (by linarith) (Real.sInf_nonneg ?_))
  rintro d ⟨n, -, -, rfl⟩
  exact abs_nonneg _

lemma main_identity {x y T : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    (∑ n ∈ Icc ⌈x⌉₊ ⌊x + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y +
        ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T},
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((((x + y : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ) =
      dav T (x + y) - dav T x +
        ((bdry (x + y) + bdry x - 1 / 2 * Real.log (1 - (x + y) ^ (-2 : ℝ)) +
            1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ) -
        ∑ ρ ∈ (zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((((x + y : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ) := by
  have h2 : (if ((⌊x⌋₊ : ℕ) : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ else 0) =
      2 * bdry x := by
    unfold bdry; split_ifs <;> ring
  have hS : (∑ n ∈ Icc ⌈x⌉₊ ⌊x + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) =
      ((Chebyshev.psi (x + y) - Chebyshev.psi x + 2 * bdry x : ℝ) : ℂ) := by
    rw [← h2, ← sum_Icc_vonMangoldt_eq hx (by linarith)]
    push_cast; rfl
  have eT : ∀ v : ℝ, ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T},
      (analyticOrderNatAt riemannZeta ρ : ℂ) * (v : ℂ) ^ ρ / ρ =
      ∑ ρ ∈ (zsetT_finite T).toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) * (v : ℂ) ^ ρ / ρ :=
    fun v => finsum_mem_eq_finite_toFinset_sum _ (zsetT_finite T)
  have hsplit :
      ∑ ρ ∈ (zsetT_finite T).toFinset.filter (fun ρ => ‖ρ‖ ≤ T),
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((((x + y : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ) +
        ∑ ρ ∈ (zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((((x + y : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ) =
      ∑ ρ ∈ (zsetT_finite T).toFinset,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (((x + y : ℝ) : ℂ)) ^ ρ / ρ -
        ∑ ρ ∈ (zsetT_finite T).toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
    rw [Finset.sum_filter_add_sum_filter_not, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  unfold dav
  rw [hS, zsetN_eq T, finsum_mem_coe_finset, eT, eT]
  linear_combination (norm := (push_cast; ring)) hsplit

theorem explicit_formula_dev :
    ∃ C : ℝ, ∀ x T y : ℝ, 2 ≤ T → T ≤ x → 0 ≤ y → y ≤ x →
      ‖(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y +
        ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T},
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (((x + y : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ≤
        C * x * Real.log x ^ 3 / T := by
  obtain ⟨C, hC⟩ := GuthMaynard.davenport_truncated_explicit_formula
  obtain ⟨A₀, hA1, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨88 * |C| + 16 + 72 * A₀, ?_⟩
  intro x T y hT hTx hy hyx
  have hx : 2 ≤ x := hT.trans hTx
  have hu' : ((x : ℂ) + (y : ℂ)) = ((x + y : ℝ) : ℂ) := by push_cast; ring
  rw [hu', main_identity (by linarith) hy]
  set ℓ := Real.log x with hℓdef
  have hℓ : 1 / 2 ≤ ℓ := half_le_log hx
  have hTpos : 0 < T := by linarith
  set P := x * ℓ ^ 3 / T with hP
  have hq1 : 1 ≤ x / T := by rw [le_div_iff₀ hTpos]; linarith
  have hPq : P = x / T * ℓ ^ 3 := by rw [hP]; ring
  have hP1 : ℓ ^ 3 ≤ P := by rw [hPq]; nlinarith [pow_pos (show 0 < ℓ by linarith) 3]
  -- the two Davenport terms
  have hdu := dav_le hC hx hT hTx (v := x + y) (by linarith) (by linarith)
  have hdx := dav_le hC hx hT hTx (v := x) le_rfl (by linarith)
  rw [← hℓdef, ← hP] at hdu hdx
  -- the real boundary terms
  have hr : ‖((bdry (x + y) + bdry x - 1 / 2 * Real.log (1 - (x + y) ^ (-2 : ℝ)) +
            1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)‖ ≤ 16 * P := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have b1 := bdry_le (v := x + y) (by linarith)
    have b2 := bdry_le (v := x) (by linarith)
    have b1' := bdry_nonneg (x + y)
    have b2' := bdry_nonneg x
    have l1 := abs_log_one_sub_le (v := x + y) (by linarith)
    have l2 := abs_log_one_sub_le hx
    have lu : Real.log (x + y) ≤ 2 * ℓ := by
      have := log_le_mul_log 2 hx (by linarith) (show x + y ≤ x ^ 2 by nlinarith)
      simpa using this
    have h6 : ℓ ≤ 4 * ℓ ^ 3 := by
      have hl2 : 1 ≤ 4 * ℓ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hl2 (show 0 ≤ ℓ by linarith)]
    have h7 : 1 ≤ 8 * ℓ ^ 3 := by nlinarith
    rw [abs_le] at l1 l2 ⊢
    constructor <;> nlinarith
  -- the far zeros
  have hfar := far_norm_le (m := analyticOrderNatAt riemannZeta)
    ((zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T)) (x := x) (u := x + y) (T := T)
    (by linarith) (by linarith) (by linarith) hTpos (by
      intro ρ hρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, zsetT, Set.mem_ofPred_eq] at hρ
      exact ⟨hρ.1.2.2.1, not_le.1 hρ.2⟩)
  have hcount := far_count_le_real hA (by linarith) hT hTx
  have hfar' : ‖∑ ρ ∈ (zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((((x + y : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ≤
      72 * A₀ * P := by
    refine hfar.trans ?_
    have e : 3 * x / T = 3 * (x / T) := by ring
    rw [e]
    have h1 : 3 * (x / T) * (∑ ρ ∈ (zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
        (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ 3 * (x / T) * (6 * A₀ * ℓ) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    have h6 : ℓ ≤ 4 * ℓ ^ 3 := by
      have hl2 : 1 ≤ 4 * ℓ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hl2 (show 0 ≤ ℓ by linarith)]
    have h2 : 3 * (x / T) * (6 * A₀ * ℓ) ≤ 3 * (x / T) * (6 * A₀ * (4 * ℓ ^ 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 (by linarith)) (by positivity)
    rw [hPq]; nlinarith
  have hgoal : (88 * |C| + 16 + 72 * A₀) * x * ℓ ^ 3 / T = (88 * |C| + 16 + 72 * A₀) * P := by
    rw [hP]; ring
  rw [hgoal]
  calc _ ≤ ‖dav T (x + y)‖ + ‖dav T x‖ + ‖((bdry (x + y) + bdry x -
            1 / 2 * Real.log (1 - (x + y) ^ (-2 : ℝ)) +
            1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)‖ +
        ‖∑ ρ ∈ (zsetT_finite T).toFinset.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((((x + y : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        exact norm_sub_le _ _
    _ ≤ |C| * (44 * P) + |C| * (44 * P) + 16 * P + 72 * A₀ * P := by gcongr
    _ = (88 * |C| + 16 + 72 * A₀) * P := by ring

end GuthMaynard.CitedZeros


theorem solution :
    ∃ C : ℝ, ∀ x T y : ℝ, 2 ≤ T → T ≤ x → 0 ≤ y → y ≤ x →
      ‖(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y +
        ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T},
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (((x + y : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ≤
        C * x * Real.log x ^ 3 / T :=
  GuthMaynard.CitedZeros.explicit_formula_dev
