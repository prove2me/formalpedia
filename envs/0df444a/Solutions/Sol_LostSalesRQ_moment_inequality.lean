-- Prove2me | solution 1 for LostSalesRQ.moment_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T19:17:55.96605+00:00
-- url     : https://prove2.me/submissions/a47b1ced-a403-4db1-95b3-cfe755aa3713

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.Order.Field

namespace LostSalesRQ
open Finset

lemma pm_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisMass μ j := by
  unfold poisMass; positivity

lemma pm_succ (μ : ℝ) (j : ℕ) :
    poisMass μ (j + 1) * ((j : ℝ) + 1) = μ * poisMass μ j := by
  unfold poisMass
  rw [Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma pc_succ (μ : ℝ) (j : ℕ) : poisCdf μ (j + 1) = poisCdf μ j + poisMass μ (j + 1) := by
  unfold poisCdf; rw [Finset.sum_range_succ]

lemma pc_zero (μ : ℝ) : poisCdf μ 0 = poisMass μ 0 := by simp [poisCdf]

lemma pm_le_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : poisMass μ j ≤ poisCdf μ j := by
  unfold poisCdf
  exact Finset.single_le_sum (fun i _ => (pm_pos hμ i).le) (Finset.self_mem_range_succ j)

lemma pc_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisCdf μ j :=
  lt_of_lt_of_le (pm_pos hμ j) (pm_le_pc hμ j)

lemma sum_i_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i = μ * (poisCdf μ j - poisMass μ j) := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination h

lemma sum_ii_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i
      = μ ^ 2 * (poisCdf μ j - poisMass μ j) - μ * (j : ℝ) * poisMass μ j := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination ((n : ℝ) + μ) * h

lemma lf_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < lossFraction μ j := by
  unfold lossFraction; exact div_pos (pm_pos hμ j) (pc_pos hμ j)

lemma lf_le_one {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : lossFraction μ j ≤ 1 := by
  unfold lossFraction; rw [div_le_one (pc_pos hμ j)]; exact pm_le_pc hμ j

lemma moh_mul_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    meanOnHand μ j * poisCdf μ j = ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
  have hF := pc_pos hμ j
  have h1 := sum_i_pm μ j
  have h0 : ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i
      = (j : ℝ) * poisCdf μ j - ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i := by
    unfold poisCdf
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h0, h1]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma moh_nonneg {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 ≤ meanOnHand μ j := by
  have hF := pc_pos hμ j
  have h := moh_mul_pc hμ j
  have hs : 0 ≤ ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    apply Finset.sum_nonneg
    intro i hi
    have hij : (i : ℝ) ≤ j := by
      have := Finset.mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    exact mul_nonneg (by linarith) (pm_pos hμ i).le
  by_contra hneg
  push_neg at hneg
  have : meanOnHand μ j * poisCdf μ j < 0 := mul_neg_of_neg_of_pos hneg hF
  linarith

lemma lf_succ {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    lossFraction μ (j + 1) = μ * lossFraction μ j / (μ + meanOnHand μ j + 1) := by
  have hF := pc_pos hμ j
  have hp := pm_pos hμ j
  have h := pm_succ μ j
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hHdef : meanOnHand μ j = (j : ℝ) - μ + μ * lossFraction μ j := rfl
  have hpe : poisMass μ j = lossFraction μ j * poisCdf μ j := by
    unfold lossFraction; field_simp
  have he := lf_pos hμ j
  rw [hHdef]
  set e := lossFraction μ j with he_def
  set F := poisCdf μ j with hF_def
  have hp' : poisMass μ (j + 1) = μ * e * F / ((j : ℝ) + 1) := by
    rw [eq_div_iff hj.ne', h, hpe]; ring
  show poisMass μ (j + 1) / poisCdf μ (j + 1) = _
  rw [pc_succ, hp']
  have h1 : 0 < F + μ * e * F / ((j : ℝ) + 1) := by positivity
  have h2 : 0 < μ + ((j : ℝ) - μ + μ * e) + 1 := by nlinarith
  rw [div_eq_div_iff h1.ne' h2.ne']
  field_simp
  ring

lemma ohv_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    onHandVariance μ j = μ * (1 - lossFraction μ j * (meanOnHand μ j + 1)) := by
  have hF := pc_pos hμ j
  have hFne : poisCdf μ j ≠ 0 := hF.ne'
  set H := meanOnHand μ j with hHdef
  -- reflect the sum
  have hrefl : onHandVariance μ j
      = ∑ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j) := by
    unfold onHandVariance
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : j + 1 - 1 - i = j - i := by omega
    have h2 : j - (j - i) = i := by omega
    rw [h1, h2]
    push_cast [hij]
    ring
  rw [hrefl]
  have hexp : ∀ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j)
      = ((((j : ℝ) - H) ^ 2) * poisMass μ i - (2 * ((j : ℝ) - H) - 1) * ((i : ℝ) * poisMass μ i)
          + (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i) / poisCdf μ j := by
    intro i _; field_simp; ring
  rw [Finset.sum_congr rfl hexp, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_i_pm, sum_ii_pm]
  have hFdef : ∑ i ∈ range (j + 1), poisMass μ i = poisCdf μ j := rfl
  rw [hFdef]
  rw [hHdef]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma en_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : erlangNormalizer μ j = 1 / lossFraction μ j := by
  unfold erlangNormalizer lossFraction
  rw [one_div_div]

end LostSalesRQ

namespace LostSalesRQ
open Finset

lemma hd_pm0 (μ : ℝ) : HasDerivAt (fun t => poisMass t 0) (-poisMass μ 0) μ := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-μ) * (-1)) μ :=
    (hasDerivAt_neg' μ).exp
  have hfun : (fun t => poisMass t 0) = fun t : ℝ => Real.exp (-t) := by
    funext t; unfold poisMass; simp
  rw [hfun]
  refine h1.congr_deriv ?_
  unfold poisMass; simp

lemma hd_pm (μ : ℝ) (i : ℕ) :
    HasDerivAt (fun t => poisMass t (i + 1)) (poisMass μ i - poisMass μ (i + 1)) μ := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-μ) * (-1)) μ :=
    (hasDerivAt_neg' μ).exp
  have h2 : HasDerivAt (fun t : ℝ => t ^ (i + 1)) (((i + 1 : ℕ) : ℝ) * μ ^ i) μ := by
    simpa using hasDerivAt_pow (i + 1) μ
  have h3 := (h1.fun_mul h2).div_const ((Nat.factorial (i + 1) : ℕ) : ℝ)
  have hfun : (fun t => poisMass t (i + 1))
      = fun t => Real.exp (-t) * t ^ (i + 1) / ((Nat.factorial (i + 1) : ℕ) : ℝ) := by
    funext t; rfl
  rw [hfun]
  refine h3.congr_deriv ?_
  unfold poisMass
  rw [Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial i : ℝ) ≠ 0 := by positivity
  have hi : (i : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma hd_pc (μ : ℝ) (j : ℕ) : HasDerivAt (fun t => poisCdf t j) (-poisMass μ j) μ := by
  induction j with
  | zero =>
    have : (fun t => poisCdf t 0) = fun t => poisMass t 0 := by funext t; exact pc_zero t
    rw [this]; exact hd_pm0 μ
  | succ n ih =>
    have : (fun t => poisCdf t (n + 1)) = fun t => poisCdf t n + poisMass t (n + 1) := by
      funext t; exact pc_succ t n
    rw [this]
    exact (ih.add (hd_pm μ n)).congr_deriv (by ring)

lemma hd_lf {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    HasDerivAt (fun t => lossFraction t (k + 1))
      (lossFraction μ (k + 1) * meanOnHand μ (k + 1) / μ) μ := by
  have hp := hd_pm μ k
  have hF := hd_pc μ (k + 1)
  have hFpos := pc_pos hμ (k + 1)
  have h := hp.fun_div hF hFpos.ne'
  have hfun : (fun t => lossFraction t (k + 1))
      = fun t => poisMass t (k + 1) / poisCdf t (k + 1) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  have hs := pm_succ μ k
  have hpk : poisMass μ k = poisMass μ (k + 1) * ((k : ℝ) + 1) / μ := by
    rw [hs]; field_simp
  unfold meanOnHand lossFraction
  rw [hpk]
  push_cast
  have hF0 : poisCdf μ (k + 1) ≠ 0 := hFpos.ne'
  have hμ0 : μ ≠ 0 := hμ.ne'
  field_simp
  ring

end LostSalesRQ

namespace LostSalesRQ

noncomputable def thD (μ x θ : ℝ) : ℝ := (1 - θ) * (θ / x - (x - 1) / μ)

noncomputable def ZdE (μ x θ : ℝ) : ℝ :=
  2 * thD μ x θ / 7 - 2 * ((x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ)) *
    (((2 * x * (-θ) - (-θ) - (θ + μ * thD μ x θ)) * (x ^ 2 + μ * θ)
      - (x ^ 2 - x - μ * θ) * (2 * x * (-θ) + (θ + μ * thD μ x θ))) / (x ^ 2 + μ * θ) ^ 2)

lemma ZdE_neg (μ x θ : ℝ) (hμ : 0 < μ) (hx : 1 ≤ x) (hθ0 : 0 < θ)
    (hA3 : μ * θ ≤ (x - 1) * x) (hdom : x * (x - 1) ≤ μ * (1 - θ))
    (hZ : 2 * θ / 7 = ((x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ)) ^ 2) : ZdE μ x θ < 0 := by
  have hx0 : 0 < x := by linarith
  have hμθ : 0 < μ * θ := mul_pos hμ hθ0
  have hDn : 0 < x ^ 2 + μ * θ := by positivity
  have hN : 0 ≤ x ^ 2 - x - μ * θ := by nlinarith
  have hid : x * ZdE μ x θ =
      -(2 * θ * (1 - θ) * ((x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ)) * (1 + μ * θ / x ^ 2)) /
          (7 * (μ * θ / x ^ 2))
        - 2 * ((x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ)) ^ 2 *
            (1 + (x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ))
        + 4 * θ * ((x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ)) / (1 + μ * θ / x ^ 2) := by
    unfold ZdE thD
    field_simp
    ring
  set κ := (x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ) with hκdef
  set ρ := μ * θ / x ^ 2 with hρdef
  have hκ0 : 0 ≤ κ := div_nonneg hN hDn.le
  have hκpos : 0 < κ := by
    rcases hκ0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hZ; nlinarith
  have hNpos : 0 < x ^ 2 - x - μ * θ := by
    have := mul_pos hκpos hDn
    have hk : κ * (x ^ 2 + μ * θ) = x ^ 2 - x - μ * θ := by
      rw [hκdef]; field_simp
    linarith
  have hθk : θ = 7 * κ ^ 2 / 2 := by linarith
  -- domain bound 2θ < 1 - κ
  have hDx : 0 < x ^ 2 + μ * θ - x := by nlinarith
  have h1 : 2 * θ * (x ^ 2 + μ * θ - x) ≤ (x ^ 2 + μ * θ - x) - (x ^ 2 - x - μ * θ) := by
    nlinarith [mul_le_mul_of_nonneg_left hdom hθ0.le]
  have h2 : 2 * θ ≤ 1 - (x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ - x) := by
    have : (x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ - x) ≤ 1 - 2 * θ := by
      rw [div_le_iff₀ hDx]; linarith
    linarith
  have h3 : κ < (x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ - x) := by
    rw [hκdef]
    exact div_lt_div_of_pos_left hNpos hDx (by linarith)
  have hdomk : 2 * θ < 1 - κ := by linarith
  have hκb : κ < 6 / 19 := by nlinarith
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρdef, div_lt_one (by positivity)]; nlinarith
  clear_value κ ρ
  have hP0 : 0 < 4 / 7 * ρ * (1 + ρ) := by positivity
  have hPk : 0 < 4 * (9730 * ρ ^ 2 - 4727 * ρ + 705) / 48013 := by
    nlinarith [sq_nonneg (ρ - 4727 / 19460)]
  have hP : 0 < κ * (2 / 7 - κ ^ 2) * (1 + ρ) ^ 2 + 4 / 7 * ρ * (1 + ρ) * (1 + κ) - 4 * κ * ρ := by
    have hide : κ * (2 / 7 - κ ^ 2) * (1 + ρ) ^ 2 + 4 / 7 * ρ * (1 + ρ) * (1 + κ) - 4 * κ * ρ
        = (1 - κ / (6 / 19)) * (4 / 7 * ρ * (1 + ρ))
          + (κ / (6 / 19)) * (4 * (9730 * ρ ^ 2 - 4727 * ρ + 705) / 48013)
          + (1 + ρ) ^ 2 * κ * ((6 / 19) ^ 2 - κ ^ 2) := by ring
    rw [hide]
    have ha : 0 < 1 - κ / (6 / 19) := by
      have : κ / (6 / 19) < 1 := by rw [div_lt_one (by norm_num)]; exact hκb
      linarith
    have hb : 0 ≤ κ / (6 / 19) := by positivity
    have hc : 0 ≤ (1 + ρ) ^ 2 * κ * ((6 / 19) ^ 2 - κ ^ 2) := by
      apply mul_nonneg (by positivity)
      nlinarith
    nlinarith [mul_pos ha hP0, mul_nonneg hb hPk.le]
  have hneg : -(2 * θ * (1 - θ) * κ * (1 + ρ)) / (7 * ρ) - 2 * κ ^ 2 * (1 + κ)
      + 4 * θ * κ / (1 + ρ) < 0 := by
    have hρ1' : 0 < 1 + ρ := by linarith
    have hfac : -(2 * θ * (1 - θ) * κ * (1 + ρ)) / (7 * ρ) - 2 * κ ^ 2 * (1 + κ)
        + 4 * θ * κ / (1 + ρ)
        = -(7 * κ ^ 2 / (2 * ρ * (1 + ρ))) *
            (κ * (2 / 7 - κ ^ 2) * (1 + ρ) ^ 2 + 4 / 7 * ρ * (1 + ρ) * (1 + κ) - 4 * κ * ρ) := by
      rw [hθk]
      field_simp
      ring
    rw [hfac]
    have : 0 < 7 * κ ^ 2 / (2 * ρ * (1 + ρ)) := by positivity
    rw [neg_mul]
    exact neg_neg_of_pos (mul_pos this hP)
  have hxZ : x * ZdE μ x θ < 0 := by rw [hid]; exact hneg
  by_contra hcon
  push_neg at hcon
  have : 0 ≤ x * ZdE μ x θ := mul_nonneg hx0.le hcon
  linarith

end LostSalesRQ

namespace LostSalesRQ

noncomputable def xF (k : ℕ) (t : ℝ) : ℝ := meanOnHand t (k + 1) + 1
noncomputable def θF (k : ℕ) (t : ℝ) : ℝ := 1 - lossFraction t (k + 1) * (meanOnHand t (k + 1) + 1)
noncomputable def ZF (k : ℕ) (t : ℝ) : ℝ :=
  2 * θF k t / 7 - ((xF k t ^ 2 - xF k t - t * θF k t) / (xF k t ^ 2 + t * θF k t)) ^ 2

lemma hd_moh {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    HasDerivAt (fun t => meanOnHand t (k + 1)) (-(θF k μ)) μ := by
  have he := hd_lf hμ k
  have h := ((hasDerivAt_const μ ((k + 1 : ℕ) : ℝ)).sub (hasDerivAt_id' μ)).add
    ((hasDerivAt_id' μ).fun_mul he)
  have hfun : (fun t => meanOnHand t (k + 1))
      = fun t => ((k + 1 : ℕ) : ℝ) - t + t * lossFraction t (k + 1) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  unfold θF
  have hμ0 : μ ≠ 0 := hμ.ne'
  field_simp
  ring

lemma hd_x {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : HasDerivAt (xF k) (-(θF k μ)) μ := by
  have h := (hd_moh hμ k).add_const 1
  exact h

lemma xF_ge_one {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : 1 ≤ xF k μ := by
  unfold xF; linarith [moh_nonneg hμ (k + 1)]

lemma hd_θ {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    HasDerivAt (θF k) (thD μ (xF k μ) (θF k μ)) μ := by
  have he := hd_lf hμ k
  have hx := hd_x hμ k
  have h := (hasDerivAt_const μ (1 : ℝ)).sub (he.fun_mul hx)
  have hfun : θF k = fun t => 1 - lossFraction t (k + 1) * xF k t := by
    funext t; rfl
  rw [hfun]
  refine h.congr_deriv ?_
  have hx1 := xF_ge_one hμ k
  have hx0 : xF k μ ≠ 0 := by linarith
  have hμ0 : μ ≠ 0 := hμ.ne'
  unfold thD θF
  unfold xF at hx0 ⊢
  field_simp
  ring

lemma θF_nonneg {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : 0 ≤ θF k μ := by
  have hv := ohv_eq hμ (k + 1)
  have hv0 : 0 ≤ onHandVariance μ (k + 1) := by
    unfold onHandVariance
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (sq_nonneg _) (div_nonneg (pm_pos hμ _).le (pc_pos hμ _).le)
  unfold θF
  by_contra h
  push_neg at h
  have : μ * (1 - lossFraction μ (k + 1) * (meanOnHand μ (k + 1) + 1)) < 0 := mul_neg_of_pos_of_neg hμ h
  linarith

lemma hd_Z {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    HasDerivAt (ZF k) (ZdE μ (xF k μ) (θF k μ)) μ := by
  have hx := hd_x hμ k
  have hθ := hd_θ hμ k
  have hx1 := xF_ge_one hμ k
  have hθ0 := θF_nonneg hμ k
  have hpos : 0 < xF k μ ^ 2 + μ * θF k μ := by positivity
  have hN := ((hx.fun_pow 2).sub hx).sub ((hasDerivAt_id' μ).fun_mul hθ)
  have hD := (hx.fun_pow 2).add ((hasDerivAt_id' μ).fun_mul hθ)
  have hq := hN.fun_div hD hpos.ne'
  have hq2 := hq.fun_pow 2
  have hZ := ((hθ.const_mul 2).div_const 7).sub hq2
  have hfun : ZF k = fun t => 2 * θF k t / 7 -
      ((xF k t ^ 2 - xF k t - t * θF k t) / (xF k t ^ 2 + t * θF k t)) ^ 2 := by
    funext t; rfl
  rw [hfun]
  refine hZ.congr_deriv ?_
  unfold ZdE
  simp only [Pi.add_apply, Pi.sub_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, one_mul]

end LostSalesRQ

namespace LostSalesRQ
open Filter Topology

lemma crossing (f : ℝ → ℝ) (a : ℝ)
    (hd : ∀ t, a ≤ t → ∃ d, HasDerivAt f d t ∧ (f t = 0 → d < 0))
    (hlarge : ∀ M, ∃ t, M ≤ t ∧ 0 < f t) : ∀ t, a ≤ t → 0 < f t := by
  intro t0 ht0
  by_contra hneg
  push_neg at hneg
  obtain ⟨t1, ht1, hf1⟩ := hlarge (t0 + 1)
  have hcont : ∀ t, a ≤ t → ContinuousAt f t := fun t ht => by
    obtain ⟨d, hdt, _⟩ := hd t ht; exact hdt.continuousAt
  have hcontOn : ContinuousOn f (Set.Icc t0 t1) := fun t ht =>
    (hcont t (le_trans ht0 ht.1)).continuousWithinAt
  set S := Set.Icc t0 t1 ∩ f ⁻¹' Set.Iic 0 with hS
  have hSc : IsClosed S := hcontOn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t0, ⟨le_refl _, by linarith⟩, hneg⟩
  have hSb : BddAbove S := ⟨t1, fun t ht => ht.1.2⟩
  have hsS : sSup S ∈ S := hSc.csSup_mem hSne hSb
  set s := sSup S with hsdef
  have hfs : f s ≤ 0 := hsS.2
  have hst1 : s < t1 := by
    rcases lt_or_eq_of_le hsS.1.2 with h | h
    · exact h
    · exfalso; rw [h] at hfs; linarith
  have hpos : ∀ t, s < t → t ≤ t1 → 0 < f t := by
    intro t hst htt1
    by_contra hc
    push_neg at hc
    have hmem : t ∈ S := ⟨⟨by linarith [hsS.1.1], htt1⟩, hc⟩
    have := le_csSup hSb hmem
    linarith
  have has : a ≤ s := le_trans ht0 hsS.1.1
  have hfs0 : f s = 0 := by
    by_contra hne
    have hlt : f s < 0 := lt_of_le_of_ne hfs hne
    have hev : ∀ᶠ y in 𝓝 s, f y < 0 := (hcont s has).eventually (Iio_mem_nhds hlt)
    have hev2 : ∀ᶠ y in 𝓝[>] s, f y < 0 ∧ y ∈ Set.Ioo s t1 :=
      (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hst1)
    obtain ⟨y, hy1, hy2⟩ := hev2.exists
    linarith [hpos y hy2.1 hy2.2.le]
  obtain ⟨d, hdd, hdneg⟩ := hd s has
  have hd0 := hdneg hfs0
  have hslope := hasDerivAt_iff_tendsto_slope.mp hdd
  have hev : ∀ᶠ y in 𝓝[≠] s, slope f s y < 0 := hslope.eventually (Iio_mem_nhds hd0)
  have hev' : ∀ᶠ y in 𝓝[>] s, slope f s y < 0 :=
    hev.filter_mono (nhdsWithin_mono s fun y hy => Set.mem_compl_singleton_iff.mpr (ne_of_gt hy))
  obtain ⟨y, hy1, hy2⟩ := (hev'.and (Ioo_mem_nhdsGT hst1)).exists
  rw [slope_def_field, hfs0] at hy1
  have hys : 0 < y - s := by linarith [hy2.1]
  have hfy : f y - 0 < 0 := by
    by_contra hc
    push_neg at hc
    have := div_nonneg hc hys.le
    linarith
  linarith [hpos y hy2.1 hy2.2.le]

end LostSalesRQ

namespace LostSalesRQ
open Filter Topology

noncomputable def Dp : ℕ → ℝ → ℝ
  | 0, _ => 0
  | (n + 1), q => ((n : ℝ) + 1) * n * (n - 1) * (n - 2) + ((n : ℝ) + 1) * q * Dp n q

lemma Dp_succ (n : ℕ) (q : ℝ) :
    Dp (n + 1) q = ((n : ℝ) + 1) * n * (n - 1) * (n - 2) + ((n : ℝ) + 1) * q * Dp n q := rfl

lemma Dp_cont (n : ℕ) : Continuous (Dp n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    show Continuous (fun q => ((n : ℝ) + 1) * n * (n - 1) * (n - 2) + ((n : ℝ) + 1) * q * Dp n q)
    fun_prop

noncomputable def Apoly (j q D : ℝ) : ℝ :=
  1 + j * q + j * (j - 1) * q ^ 2 + j * (j - 1) * (j - 2) * q ^ 3 + q ^ 4 * D

noncomputable def Pth (j q D : ℝ) : ℝ := D^2*q^6 + 2*D*j^3*q^5 - 6*D*j^2*q^5 + 2*D*j^2*q^4 + 4*D*j*q^5 - 2*D*j*q^4 + 2*D*j*q^3 - D*j*q^2 + D*q^2 + D*q + j^6*q^4 - 6*j^5*q^4 + 2*j^5*q^3 + 13*j^4*q^4 - 8*j^4*q^3 + 3*j^4*q^2 - j^4*q - 12*j^3*q^4 + 10*j^3*q^3 - 8*j^3*q^2 + 6*j^3*q + 4*j^2*q^4 - 4*j^2*q^3 + 5*j^2*q^2 - 7*j^2*q + 2*j*q + j
noncomputable def PN (j q D : ℝ) : ℝ := D^2*j^2*q^6 + D^2*j*q^6 - 2*D^2*j*q^5 - 2*D^2*q^5 + D^2*q^4 + 2*D*j^5*q^5 - 4*D*j^4*q^5 - 2*D*j^4*q^4 - 2*D*j^3*q^5 + 8*D*j^3*q^4 + 4*D*j^2*q^5 + 2*D*j^2*q^4 - 4*D*j^2*q^3 - 8*D*j*q^4 + 8*D*j*q^3 - 4*D*j*q^2 + D*j*q - 2*D*q - D + j^8*q^4 - 5*j^7*q^4 + 7*j^6*q^4 + 4*j^6*q^3 + j^5*q^4 - 12*j^5*q^3 + j^5*q^2 - 8*j^4*q^4 + 4*j^4*q^3 + 6*j^4*q^2 - 2*j^4*q + j^4 + 4*j^3*q^4 + 12*j^3*q^3 - 19*j^3*q^2 + 12*j^3*q - 6*j^3 - 8*j^2*q^3 + 12*j^2*q^2 - 10*j^2*q + 11*j^2 - 4*j
noncomputable def PD (j q D : ℝ) : ℝ := D*j^2*q^4 + 2*D*j*q^4 - 2*D*j*q^3 + D*q^4 - D*q^3 + D*q^2 + j^5*q^3 - j^4*q^3 - j^4*q^2 - 3*j^3*q^3 + 6*j^3*q^2 + j^2*q^3 - 2*j^2*q^2 + 2*j*q^3 - 3*j*q^2 + 4*j*q + 1

lemma en_succ {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    erlangNormalizer μ (n + 1) = 1 + ((n : ℝ) + 1) / μ * erlangNormalizer μ n := by
  have hp := pm_pos hμ n
  have hp1 := pm_pos hμ (n + 1)
  have h := pm_succ μ n
  have hp1' : poisMass μ (n + 1) = μ * poisMass μ n / ((n : ℝ) + 1) := by
    field_simp; linarith
  unfold erlangNormalizer
  rw [pc_succ, hp1']
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma en_expand {q : ℝ} (hq : 0 < q) (n : ℕ) :
    erlangNormalizer (1 / q) n = Apoly n q (Dp n q) := by
  induction n with
  | zero =>
    unfold erlangNormalizer Apoly Dp
    rw [pc_zero, div_self (pm_pos (by positivity) 0).ne']
    simp
  | succ n ih =>
    rw [en_succ (by positivity) n, ih, Dp_succ]
    unfold Apoly
    push_cast
    field_simp
    ring

lemma I1 (j q D : ℝ) (hq : q ≠ 0) (hA : Apoly j q D ≠ 0) :
    1 - (1 / Apoly j q D) * ((j - 1 / q + 1 / q * (1 / Apoly j q D)) + 1)
      = q ^ 2 * Pth j q D / Apoly j q D ^ 2 := by
  unfold Pth
  generalize hAg : Apoly j q D = A at hA ⊢
  field_simp
  rw [← hAg]
  unfold Apoly
  ring

lemma I2 (j q D : ℝ) (hq : q ≠ 0) (hA : Apoly j q D ≠ 0) :
    ((j - 1 / q + 1 / q * (1 / Apoly j q D)) + 1) ^ 2 - ((j - 1 / q + 1 / q * (1 / Apoly j q D)) + 1)
      - 1 / q * (1 - (1 / Apoly j q D) * ((j - 1 / q + 1 / q * (1 / Apoly j q D)) + 1))
      = q ^ 2 * PN j q D / Apoly j q D ^ 2 := by
  unfold PN
  generalize hAg : Apoly j q D = A at hA ⊢
  field_simp
  rw [← hAg]
  unfold Apoly
  ring

lemma I3 (j q D : ℝ) (hq : q ≠ 0) (hA : Apoly j q D ≠ 0) :
    ((j - 1 / q + 1 / q * (1 / Apoly j q D)) + 1) ^ 2
      + 1 / q * (1 - (1 / Apoly j q D) * ((j - 1 / q + 1 / q * (1 / Apoly j q D)) + 1))
      = PD j q D / Apoly j q D := by
  unfold PD
  generalize hAg : Apoly j q D = A at hA ⊢
  field_simp
  rw [← hAg]
  unfold Apoly
  ring

end LostSalesRQ

namespace LostSalesRQ
open Filter Topology

noncomputable def Gf (k : ℕ) (q : ℝ) : ℝ :=
  2 * Pth ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) / (7 * Apoly ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) ^ 2)
    - q ^ 2 * PN ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) ^ 2 /
        (Apoly ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) ^ 2 * PD ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) ^ 2)

lemma en_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < erlangNormalizer μ j := by
  unfold erlangNormalizer; exact div_pos (pc_pos hμ j) (pm_pos hμ j)

lemma ZF_eq {q : ℝ} (hq : 0 < q) (k : ℕ) : ZF k (1 / q) = q ^ 2 * Gf k q := by
  have hμ : (0 : ℝ) < 1 / q := by positivity
  have hA := en_expand hq (k + 1)
  have hApos : 0 < Apoly ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) := by
    rw [← hA]; exact en_pos hμ (k + 1)
  have hlf : lossFraction (1 / q) (k + 1) = 1 / Apoly ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) := by
    rw [← hA, en_eq hμ, one_div_one_div]
  have hq0 : q ≠ 0 := hq.ne'
  have hA0 := hApos.ne'
  have hDpos : 0 < xF k (1 / q) ^ 2 + 1 / q * θF k (1 / q) := by
    have := xF_ge_one hμ k
    have := θF_nonneg hμ k
    positivity
  have hmoh : meanOnHand (1 / q) (k + 1)
      = ((k + 1 : ℕ) : ℝ) - 1 / q + 1 / q * lossFraction (1 / q) (k + 1) := rfl
  have hPD : 0 < PD ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) := by
    have h3 := I3 ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) hq0 hA0
    unfold xF θF at hDpos
    rw [hmoh, hlf, h3] at hDpos
    exact (div_pos_iff_of_pos_right hApos).mp hDpos
  unfold ZF xF θF Gf
  rw [hmoh, hlf, I2 _ _ _ hq0 hA0, I3 _ _ _ hq0 hA0, I1 _ _ _ hq0 hA0]
  have hPD0 := hPD.ne'
  field_simp

lemma Gf_cont (k : ℕ) : ContinuousAt (Gf k) 0 := by
  have hD := Dp_cont (k + 1)
  have c1 : Continuous fun q => Pth ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) := by
    unfold Pth; fun_prop
  have c2 : Continuous fun q => Apoly ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) := by
    unfold Apoly; fun_prop
  have c3 : Continuous fun q => PN ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) := by
    unfold PN; fun_prop
  have c4 : Continuous fun q => PD ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) := by
    unfold PD; fun_prop
  have hA0 : Apoly ((k + 1 : ℕ) : ℝ) 0 (Dp (k + 1) 0) ≠ 0 := by unfold Apoly; simp
  have hP0 : PD ((k + 1 : ℕ) : ℝ) 0 (Dp (k + 1) 0) ≠ 0 := by unfold PD; simp
  have e1 : ContinuousAt (fun q => 2 * Pth ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q)
      / (7 * Apoly ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) ^ 2)) 0 :=
    ((continuous_const.mul c1).continuousAt).div
      ((continuous_const.mul (c2.pow 2)).continuousAt) (by simpa using hA0)
  have e2 : ContinuousAt (fun q => q ^ 2 * PN ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) ^ 2 /
      (Apoly ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) ^ 2 * PD ((k + 1 : ℕ) : ℝ) q (Dp (k + 1) q) ^ 2)) 0 :=
    (((continuous_id.pow 2).mul (c3.pow 2)).continuousAt).div
      (((c2.pow 2).mul (c4.pow 2)).continuousAt) (mul_ne_zero (pow_ne_zero 2 hA0) (pow_ne_zero 2 hP0))
  exact e1.sub e2

lemma Gf_zero (k : ℕ) : Gf k 0 = 2 * ((k + 1 : ℕ) : ℝ) / 7 := by
  unfold Gf Pth Apoly PN PD
  simp

lemma ZF_large (k : ℕ) : ∀ M, ∃ t, M ≤ t ∧ 0 < ZF k t := by
  have hG0 : 0 < Gf k 0 := by rw [Gf_zero]; positivity
  have hev : ∀ᶠ q in 𝓝 (0 : ℝ), 0 < Gf k q := (Gf_cont k).eventually (lt_mem_nhds hG0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  intro M
  set t := max M (2 / δ) + 1 with ht
  have ht2 : 2 / δ + 1 ≤ t := by rw [ht]; linarith [le_max_right M (2 / δ)]
  have htpos : 0 < t := by have : 0 < 2 / δ := by positivity
                           linarith
  refine ⟨t, by rw [ht]; linarith [le_max_left M (2 / δ)], ?_⟩
  have hq : 0 < 1 / t := by positivity
  have hqδ : dist (1 / t) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hq, div_lt_iff₀ htpos]
    have : 2 < δ * t := by
      have h1 : δ * (2 / δ + 1) ≤ δ * t := by
        exact mul_le_mul_of_nonneg_left ht2 hδ.le
      have h2 : δ * (2 / δ + 1) = 2 + δ := by field_simp
      linarith
    linarith
  have hG := hball hqδ
  have hZ := ZF_eq hq k
  rw [one_div_one_div] at hZ
  rw [hZ]
  positivity

end LostSalesRQ

namespace LostSalesRQ
open Filter Topology

lemma R_ineq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    μ ≤ (meanOnHand μ j + 1) * (meanOnHand μ j + μ * lossFraction μ j) := by
  induction j with
  | zero =>
    have h0 : lossFraction μ 0 = 1 := by
      unfold lossFraction; rw [pc_zero]; exact div_self (pm_pos hμ 0).ne'
    have hH0 : meanOnHand μ 0 = 0 := by unfold meanOnHand; rw [h0]; simp
    rw [hH0, h0]; linarith
  | succ n ih =>
    have he := lf_pos hμ n
    have hH := moh_nonneg hμ n
    have hrec := lf_succ hμ n
    have hHdef : meanOnHand μ n = (n : ℝ) - μ + μ * lossFraction μ n := rfl
    have hH' : meanOnHand μ (n + 1) = ((n : ℝ) + 1) - μ + μ * lossFraction μ (n + 1) := by
      unfold meanOnHand; push_cast; ring
    rw [hH', hrec]
    set e := lossFraction μ n with he_def
    set H := meanOnHand μ n with hH_def
    have heH : μ * e = H - n + μ := by linarith [hHdef]
    have hD : 0 < μ + H + 1 := by linarith
    have hsub : μ * (μ * e / (μ + H + 1)) = μ * (H - n + μ) / (μ + H + 1) := by
      rw [← heH]; ring
    rw [hsub, ← sub_nonneg]
    have key : ((n : ℝ) + 1 - μ + μ * (H - n + μ) / (μ + H + 1) + 1) *
        ((n : ℝ) + 1 - μ + μ * (H - n + μ) / (μ + H + 1) + μ * (H - n + μ) / (μ + H + 1)) - μ
        = ((n : ℝ) + 1) * ((H + 1) ^ 2 * ((n : ℝ) + 2 + μ) + (H + 1) * μ * (μ - n - 1) - μ ^ 2)
            / (μ + H + 1) ^ 2 := by
      field_simp; ring
    rw [key]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    have hR : 0 ≤ (H + 1) * (2 * H - n + μ) - μ := by
      have : (H + 1) * (H + μ * e) = (H + 1) * (2 * H - n + μ) := by rw [heH]; ring
      linarith [ih, this]
    have ha : 0 < H + 1 := by linarith
    by_cases hc : 0 ≤ (H + 1) * ((n : ℝ) + 2 - μ) + μ
    · nlinarith [mul_nonneg hμ.le hR, mul_nonneg ha.le hc]
    · push_neg at hc
      have hc' : 0 < (H + 1) * (μ - n - 2) - μ := by linarith
      have hm : 0 < μ - n - 2 := by
        by_contra hneg; push_neg at hneg
        nlinarith [mul_nonneg ha.le (by linarith : (0 : ℝ) ≤ -(μ - n - 2))]
      have h1 : 0 < μ * ((H + 1) * (μ - n - 2) - μ) := mul_pos hμ hc'
      have h2 : 0 < (H + 1) ^ 2 * ((n : ℝ) + 2 + μ) := by positivity
      have h3 : 0 < (H + 1) * μ := mul_pos ha hμ
      nlinarith [h1, h2, h3]


lemma evb_all (μ : ℝ) (hμ : 0 < μ) (j : ℕ) (hj : 1 ≤ j) :
    0 < onHandVariance μ j ∧ onHandVariance μ j ≤ meanOnHand μ j * (meanOnHand μ j + 1) := by
  constructor
  · have hF := pc_pos hμ j
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (j + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have hnn : ∀ l ∈ Finset.range (j + 1),
        0 ≤ ((l : ℝ) - meanOnHand μ j) ^ 2 * (poisMass μ (j - l) / poisCdf μ j) := by
      intro l _
      exact mul_nonneg (sq_nonneg _) (div_nonneg (pm_pos hμ _).le hF.le)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l hl _ => hnn l hl)
    rw [Finset.sum_pair (by norm_num)] at hle
    simp only [Nat.cast_zero, Nat.cast_one, Nat.sub_zero] at hle
    have hw0 : 0 < poisMass μ j / poisCdf μ j := div_pos (pm_pos hμ _) hF
    have hw1 : 0 < poisMass μ (j - 1) / poisCdf μ j := div_pos (pm_pos hμ _) hF
    set H := meanOnHand μ j
    have hpos : 0 < (0 - H) ^ 2 * (poisMass μ j / poisCdf μ j)
        + (1 - H) ^ 2 * (poisMass μ (j - 1) / poisCdf μ j) := by
      by_cases hH0 : H = 0
      · rw [hH0]; norm_num; exact hw1
      · have : 0 < (0 - H) ^ 2 := by
          have : (0 - H) ≠ 0 := by intro h; apply hH0; linarith
          positivity
        nlinarith [mul_pos this hw0, mul_nonneg (sq_nonneg (1 - H)) hw1.le]
    unfold onHandVariance
    linarith
  · have hR := R_ineq hμ j
    have hv := ohv_eq hμ j
    rw [hv]
    nlinarith [hR]

lemma ipf_all (μ : ℝ) (hμ : 0 < μ) (j : ℕ) :
    lossFraction μ j - lossFraction μ (j + 1) =
        lossFraction μ j * (meanOnHand μ j + 1) / (μ + meanOnHand μ j + 1) ∧
    0 < lossFraction μ j - lossFraction μ (j + 1) ∧
    intersectionPenalty μ j =
        erlangNormalizer μ j * (1 + onHandVariance μ j / (meanOnHand μ j + 1)) ∧
    baseStockCost μ (intersectionPenalty μ j) j =
        baseStockCost μ (intersectionPenalty μ j) (j + 1) ∧
    baseStockCost μ (intersectionPenalty μ j) j =
        meanOnHand μ j + 1 + onHandVariance μ j / (meanOnHand μ j + 1) ∧
    baseStockCost μ (intersectionPenalty μ j) j =
        (j : ℝ) + 1 - μ + μ / (meanOnHand μ j + 1) := by
  have he := lf_pos hμ j
  have hH := moh_nonneg hμ j
  have hrec := lf_succ hμ j
  have hv := ohv_eq hμ j
  have hA := en_eq hμ j
  have hHdef : meanOnHand μ j = (j : ℝ) - μ + μ * lossFraction μ j := rfl
  have hH1def : meanOnHand μ (j + 1) = ((j : ℝ) + 1) - μ + μ * lossFraction μ (j + 1) := by
    unfold meanOnHand; push_cast; ring
  have hI : intersectionPenalty μ j = (lossFraction μ j - lossFraction μ (j + 1))⁻¹ - μ := rfl
  have hL : ∀ a k, baseStockCost μ a k = meanOnHand μ k + a * lossFraction μ k :=
    fun _ _ => rfl
  simp only [hL]
  rw [hH1def]
  set e := lossFraction μ j with he_def
  set e' := lossFraction μ (j + 1) with he'_def
  set H := meanOnHand μ j with hH_def
  set v := onHandVariance μ j with hv_def
  set a := intersectionPenalty μ j with ha_def
  have hH1 : 0 < H + 1 := by linarith
  have hH1ne : H + 1 ≠ 0 := hH1.ne'
  have hD : 0 < μ + H + 1 := by linarith
  have hDne : μ + H + 1 ≠ 0 := hD.ne'
  have hene : e ≠ 0 := he.ne'
  have hδ : e - e' = e * (H + 1) / (μ + H + 1) := by
    rw [hrec]; field_simp; ring
  have hδpos : 0 < e - e' := by rw [hδ]; exact div_pos (mul_pos he hH1) hD
  have hprod : (a + μ) * (e - e') = 1 := by
    rw [hI]; simp only [sub_add_cancel]; exact inv_mul_cancel₀ hδpos.ne'
  have h3 : a = 1 / e * (1 + v / (H + 1)) := by
    rw [hI, hδ, hv]; field_simp; ring
  have h5 : H + a * e = H + 1 + v / (H + 1) := by
    rw [h3]; field_simp; ring
  refine ⟨hδ, hδpos, by rw [hA]; exact h3, ?_, h5, ?_⟩
  · linear_combination hHdef + hprod
  · rw [h5, hv]
    have hmid : H + 1 + μ * (1 - e * (H + 1)) / (H + 1) = H + 1 + μ / (H + 1) - μ * e := by
      field_simp; ring
    rw [hmid]
    linarith [hHdef]

lemma second_claim (μ x θ : ℝ) (hμ : 0 < μ) (hx : 1 ≤ x) (hθ0 : 0 < θ)
    (hA3 : μ * θ ≤ (x - 1) * x) (hdom : x * (x - 1) ≤ μ * (1 - θ))
    (hZ : ((x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ)) ^ 2 < 2 * θ / 7) :
    3 * (x ^ 2 - x - μ * θ) < x ^ 2 + μ * θ := by
  have hx0 : 0 < x := by linarith
  have hμθ : 0 < μ * θ := mul_pos hμ hθ0
  have hDn : 0 < x ^ 2 + μ * θ := by positivity
  have hN : 0 ≤ x ^ 2 - x - μ * θ := by nlinarith
  rcases hN.lt_or_eq with hNpos | hN0
  · set κ := (x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ) with hκdef
    have hκpos : 0 < κ := div_pos hNpos hDn
    have hDx : 0 < x ^ 2 + μ * θ - x := by nlinarith
    have h1 : 2 * θ * (x ^ 2 + μ * θ - x) ≤ (x ^ 2 + μ * θ - x) - (x ^ 2 - x - μ * θ) := by
      nlinarith [mul_le_mul_of_nonneg_left hdom hθ0.le]
    have h2 : 2 * θ ≤ 1 - (x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ - x) := by
      have : (x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ - x) ≤ 1 - 2 * θ := by
        rw [div_le_iff₀ hDx]; linarith
      linarith
    have h3 : κ < (x ^ 2 - x - μ * θ) / (x ^ 2 + μ * θ - x) := by
      rw [hκdef]
      exact div_lt_div_of_pos_left hNpos hDx (by linarith)
    have hdomk : 2 * θ < 1 - κ := by linarith
    have hk3 : κ < 1 / 3 := by nlinarith
    have : κ * (x ^ 2 + μ * θ) = x ^ 2 - x - μ * θ := by rw [hκdef]; field_simp
    nlinarith
  · rw [← hN0]; linarith

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ : ℝ) (j : ℕ) (hj : 1 ≤ j) (hμj : (j : ℝ) ≤ μ) :
    0 < 2 * (onHandVariance μ j / μ) / 7 -
        ((meanOnHand μ j - onHandVariance μ j / (meanOnHand μ j + 1)) /
          baseStockCost μ (intersectionPenalty μ j) j) ^ 2 ∧
    3 * (meanOnHand μ j - onHandVariance μ j / (meanOnHand μ j + 1)) <
      baseStockCost μ (intersectionPenalty μ j) j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hj1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hj
  have hμ : 0 < μ := by linarith
  -- facts at any t ≥ j
  have facts : ∀ t : ℝ, ((k + 1 : ℕ) : ℝ) ≤ t →
      0 < t ∧ 1 ≤ xF k t ∧ 0 < θF k t ∧ t * θF k t ≤ (xF k t - 1) * xF k t ∧
        xF k t * (xF k t - 1) ≤ t * (1 - θF k t) := by
    intro t ht
    have htpos : 0 < t := by linarith
    have hv := ohv_eq htpos (k + 1)
    have hev := evb_all t htpos (k + 1) (by omega)
    have hx := xF_ge_one htpos k
    have hθ : t * θF k t = onHandVariance t (k + 1) := by unfold θF; rw [hv]
    refine ⟨htpos, hx, ?_, ?_, ?_⟩
    · have : 0 < t * θF k t := by rw [hθ]; exact hev.1
      exact pos_of_mul_pos_right this htpos.le
    · rw [hθ]; unfold xF; have := hev.2; nlinarith
    · -- identity t - H(H+1) - v = (H+1)(t - j)
      have hHdef : meanOnHand t (k + 1) = ((k + 1 : ℕ) : ℝ) - t + t * lossFraction t (k + 1) := rfl
      have hid : t * (1 - θF k t) - xF k t * (xF k t - 1)
          = xF k t * (t - ((k + 1 : ℕ) : ℝ)) := by
        unfold θF xF; rw [hHdef]; ring
      have : 0 ≤ xF k t * (t - ((k + 1 : ℕ) : ℝ)) := mul_nonneg (by linarith) (by linarith)
      linarith
  have hZpos : ∀ t, ((k + 1 : ℕ) : ℝ) ≤ t → 0 < ZF k t := by
    apply crossing (ZF k) (((k + 1 : ℕ) : ℝ))
    · intro t ht
      obtain ⟨htpos, hx, hθ0, hA3, hdom⟩ := facts t ht
      refine ⟨ZdE t (xF k t) (θF k t), hd_Z htpos k, ?_⟩
      intro hz
      apply ZdE_neg t (xF k t) (θF k t) htpos hx hθ0 hA3 hdom
      unfold ZF at hz
      linarith
    · exact ZF_large k
  obtain ⟨_, hx, hθ0, hA3, hdom⟩ := facts μ hμj
  have hZ := hZpos μ hμj
  have hipf := (ipf_all μ hμ (k + 1)).2.2.2.2.1
  have hv := ohv_eq hμ (k + 1)
  have hvθ : onHandVariance μ (k + 1) = μ * θF k μ := by unfold θF; rw [hv]
  have hHx : meanOnHand μ (k + 1) = xF k μ - 1 := by unfold xF; ring
  have hx0 : 0 < xF k μ := by linarith
  have hconv : (meanOnHand μ (k + 1) - onHandVariance μ (k + 1) / (meanOnHand μ (k + 1) + 1)) /
        baseStockCost μ (intersectionPenalty μ (k + 1)) (k + 1)
      = (xF k μ ^ 2 - xF k μ - μ * θF k μ) / (xF k μ ^ 2 + μ * θF k μ) := by
    rw [hipf, hvθ, hHx]
    have : xF k μ - 1 + 1 = xF k μ := by ring
    rw [this]
    have hD : 0 < xF k μ ^ 2 + μ * θF k μ := by have := hθ0.le; positivity
    field_simp
  have hθdef : onHandVariance μ (k + 1) / μ = θF k μ := by
    rw [hvθ]; field_simp
  rw [hconv, hθdef]
  constructor
  · unfold ZF at hZ; linarith
  · have hsc := second_claim μ (xF k μ) (θF k μ) hμ hx hθ0 hA3 hdom (by unfold ZF at hZ; linarith)
    rw [hipf, hvθ, hHx]
    have : xF k μ - 1 + 1 = xF k μ := by ring
    rw [this]
    rw [show 3 * (xF k μ - 1 - μ * θF k μ / xF k μ) = 3 * (xF k μ ^ 2 - xF k μ - μ * θF k μ) / xF k μ by
      field_simp]
    rw [show xF k μ + μ * θF k μ / xF k μ = (xF k μ ^ 2 + μ * θF k μ) / xF k μ by field_simp]
    exact div_lt_div_of_pos_right hsc hx0
