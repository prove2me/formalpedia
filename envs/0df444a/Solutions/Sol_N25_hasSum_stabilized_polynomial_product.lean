-- Prove2me | solution 1 for N25.hasSum_stabilized_polynomial_product
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:51.526688+00:00
-- url     : https://prove2.me/submissions/0b950b0a-abbc-4687-ae40-c067e4b72d41

import Mathlib
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Filter Topology Polynomial

open scoped BigOperators

namespace N25

section Formal

variable {R : Type} [CommRing R]

private theorem pp_zero (P : ℕ → R[X]) : ((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) P 0 = 1 := Finset.prod_range_zero _

private theorem pp_succ (P : ℕ → R[X]) (N : ℕ) : ((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) P (N + 1) = ((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) P N * Polynomial.expand R (N + 1) (P N) :=
  Finset.prod_range_succ _ _

private theorem coe_pp (P : ℕ → R[X]) (N : ℕ) :
    ((((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) P N : R[X]) : PowerSeries R) = ∏ n ∈ Finset.range N, ((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (n : ℕ) => ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R))) P n := by
  show Polynomial.coeToPowerSeries.ringHom (∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))
    = _
  rw [map_prod]
  rfl

variable {P : ℕ → R[X]}

private theorem fac_sub_one (P : ℕ → R[X]) (n : ℕ) :
    ((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (n : ℕ) => ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R))) P n - 1 = ((Polynomial.expand R (n + 1) (P n - 1) : R[X]) : PowerSeries R) := by
  dsimp only
  rw [map_sub, map_one, Polynomial.coe_sub, Polynomial.coe_one]

private theorem coeff_fac_sub_one (hP : ∀ n, (P n).coeff 0 = 1) (n i : ℕ) (hi : i < n + 1) :
    PowerSeries.coeff i (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (n : ℕ) => ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R))) P n - 1) = 0 := by
  rw [fac_sub_one, Polynomial.coeff_coe, Polynomial.coeff_expand (Nat.succ_pos n)]
  split_ifs with hd
  · rw [Nat.eq_zero_of_dvd_of_lt hd hi, Nat.zero_div, Polynomial.coeff_sub,
      Polynomial.coeff_one_zero, hP n, sub_self]
  · rfl

private theorem order_fac_sub_one (hP : ∀ n, (P n).coeff 0 = 1) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (n : ℕ) => ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R))) P n - 1).order :=
  PowerSeries.nat_le_order _ _ fun i hi => coeff_fac_sub_one hP n i hi

private theorem coeff_mul_fac_of_le (hP : ∀ n, (P n).coeff 0 = 1) {m n : ℕ} (h : m ≤ n) (φ : PowerSeries R) :
    PowerSeries.coeff m (φ * ((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (n : ℕ) => ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R))) P n) = PowerSeries.coeff m φ := by
  have : φ * ((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (n : ℕ) => ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R))) P n = φ + φ * (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (n : ℕ) => ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R))) P n - 1) := by ring
  rw [this, map_add, PowerSeries.coeff_mul_of_lt_order, add_zero]
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le h) (order_fac_sub_one hP n)

private theorem coeff_prod_range_fac (hP : ∀ n, (P n).coeff 0 = 1) (m N : ℕ) (hN : m ≤ N) :
    PowerSeries.coeff m (∏ n ∈ Finset.range N, ((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (n : ℕ) => ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R))) P n) =
      PowerSeries.coeff m (∏ n ∈ Finset.range m, ((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (n : ℕ) => ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R))) P n) := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hmN ih => rw [Finset.prod_range_succ, coeff_mul_fac_of_le hP hmN, ih]

private theorem coeff_pp_stable (hP : ∀ n, (P n).coeff 0 = 1) {m N : ℕ} (h : m ≤ N) :
    (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) P N).coeff m = (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) P m).coeff m := by
  have := coeff_prod_range_fac hP m N h
  rwa [← coe_pp, ← coe_pp, Polynomial.coeff_coe, Polynomial.coeff_coe] at this

end Formal

section Analytic

variable {P : ℕ → ℂ[X]} {M : ℂ[X]}

private theorem Cst_nonneg (M : ℂ[X]) : 0 ≤ ((fun (M : ℂ[X]) => ∑ k ∈ M.support, ‖M.coeff k‖)) M := Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem coeff_Pabs (M : ℂ[X]) (k : ℕ) : (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).coeff k = ‖M.coeff k‖ := by
  classical
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Polynomial.mem_support_iff, ne_eq]
  split_ifs with h
  · rw [h, norm_zero]
  · rfl

private theorem coeff_Pabs_zero (hM : M.coeff 0 = 1) : (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).coeff 0 = 1 := by
  rw [coeff_Pabs, hM, norm_one]

private theorem coeff_Pabs_nonneg (M : ℂ[X]) (k : ℕ) : 0 ≤ (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).coeff k := by
  rw [coeff_Pabs]; exact norm_nonneg _

private theorem zero_mem_support {Q : ℂ[X]} (hQ : Q.coeff 0 = 1) : (0 : ℕ) ∈ Q.support :=
  Polynomial.mem_support_iff.mpr (by rw [hQ]; exact one_ne_zero)

private theorem eval_sub_one_eq {Q : ℂ[X]} (hQ : Q.coeff 0 = 1) (x : ℂ) :
    Q.eval x - 1 = ∑ k ∈ Q.support.erase 0, Q.coeff k * x ^ k := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, ← Finset.add_sum_erase _ _ (zero_mem_support hQ),
    hQ, pow_zero, one_mul, add_sub_cancel_left]

private theorem norm_eval_sub_one_le {Q : ℂ[X]} (hQ : Q.coeff 0 = 1) (hdom : ∀ k, ‖Q.coeff k‖ ≤ ‖M.coeff k‖)
    {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖Q.eval x - 1‖ ≤ ((fun (M : ℂ[X]) => ∑ k ∈ M.support, ‖M.coeff k‖)) M * ‖x‖ := by
  rw [eval_sub_one_eq hQ]
  refine (norm_sum_le _ _).trans ?_
  have hsub : Q.support.erase 0 ⊆ M.support := by
    intro k hk
    have hk' : Q.coeff k ≠ 0 := Polynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hk)
    refine Polynomial.mem_support_iff.mpr fun h0 => hk' ?_
    have := hdom k
    rw [h0, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
  calc ∑ k ∈ Q.support.erase 0, ‖Q.coeff k * x ^ k‖
      ≤ ∑ k ∈ Q.support.erase 0, ‖M.coeff k‖ * ‖x‖ := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [norm_mul, norm_pow]
        refine mul_le_mul (hdom k) ?_ (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hk)
        calc ‖x‖ ^ k ≤ ‖x‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hx hk1
          _ = ‖x‖ := pow_one _
    _ ≤ ∑ k ∈ M.support, ‖M.coeff k‖ * ‖x‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun k _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = ((fun (M : ℂ[X]) => ∑ k ∈ M.support, ‖M.coeff k‖)) M * ‖x‖ := by rw [Finset.sum_mul]

private theorem eval_Pabs (M : ℂ[X]) (r : ℝ) :
    (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval r = ∑ k ∈ M.support, ‖M.coeff k‖ * r ^ k := by
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]

private theorem eval_Pabs_sub_one_eq (hM : M.coeff 0 = 1) (r : ℝ) :
    (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval r - 1 = ∑ k ∈ M.support.erase 0, ‖M.coeff k‖ * r ^ k := by
  rw [eval_Pabs, ← Finset.add_sum_erase _ _ (zero_mem_support hM), hM, norm_one, pow_zero,
    one_mul, add_sub_cancel_left]

private theorem one_le_eval_Pabs (hM : M.coeff 0 = 1) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval r := by
  have h := eval_Pabs_sub_one_eq hM r
  have h0 : 0 ≤ ∑ k ∈ M.support.erase 0, ‖M.coeff k‖ * r ^ k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr _)
  linarith

private theorem eval_Pabs_sub_one_le (hM : M.coeff 0 = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval r - 1 ≤ ((fun (M : ℂ[X]) => ∑ k ∈ M.support, ‖M.coeff k‖)) M * r := by
  rw [eval_Pabs_sub_one_eq hM]
  calc ∑ k ∈ M.support.erase 0, ‖M.coeff k‖ * r ^ k
      ≤ ∑ k ∈ M.support.erase 0, ‖M.coeff k‖ * r := by
        refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hk)
        calc r ^ k ≤ r ^ 1 := pow_le_pow_of_le_one hr hr1 hk1
          _ = r := pow_one _
    _ ≤ ∑ k ∈ M.support, ‖M.coeff k‖ * r :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun k _ _ => mul_nonneg (norm_nonneg _) hr
    _ = ((fun (M : ℂ[X]) => ∑ k ∈ M.support, ‖M.coeff k‖)) M * r := by rw [Finset.sum_mul]

private theorem norm_coeff_mul_le {f g : ℂ[X]} {F G : ℝ[X]} (hf : ∀ k, ‖f.coeff k‖ ≤ F.coeff k)
    (hg : ∀ k, ‖g.coeff k‖ ≤ G.coeff k) (k : ℕ) : ‖(f * g).coeff k‖ ≤ (F * G).coeff k := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) ((norm_nonneg _).trans (hf _))

private theorem norm_coeff_expand_le {f : ℂ[X]} {F : ℝ[X]} (hf : ∀ k, ‖f.coeff k‖ ≤ F.coeff k)
    {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ‖(Polynomial.expand ℂ m f).coeff k‖ ≤ (Polynomial.expand ℝ m F).coeff k := by
  rw [Polynomial.coeff_expand hm, Polynomial.coeff_expand hm]
  split_ifs
  · exact hf _
  · rw [norm_zero]

private theorem norm_coeff_pp_le (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖) (N k : ℕ) :
    ‖(((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) P N).coeff k‖ ≤ (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) (((fun (M : ℂ[X]) (_ : ℕ) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M) N).coeff k := by
  induction N generalizing k with
  | zero =>
    rw [pp_zero, pp_zero, Polynomial.coeff_one, Polynomial.coeff_one]
    split_ifs
    · rw [norm_one]
    · rw [norm_zero]
  | succ N ih =>
    rw [pp_succ, pp_succ]
    exact norm_coeff_mul_le ih
      (norm_coeff_expand_le (fun j => (hdom N j).trans (coeff_Pabs M j).symm.le) (Nat.succ_pos N)) k

private theorem coeff_pp_Mfam_nonneg (M : ℂ[X]) (N k : ℕ) : 0 ≤ (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) (((fun (M : ℂ[X]) (_ : ℕ) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M) N).coeff k := by
  induction N generalizing k with
  | zero =>
    rw [pp_zero, Polynomial.coeff_one]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  | succ N ih =>
    rw [pp_succ, Polynomial.coeff_mul]
    refine Finset.sum_nonneg fun x _ => mul_nonneg (ih _) ?_
    rw [Polynomial.coeff_expand (Nat.succ_pos N)]
    split_ifs
    · exact coeff_Pabs_nonneg M _
    · exact le_rfl

private theorem coeff_le_coeff_mul {F G : ℝ[X]} (hF : ∀ k, 0 ≤ F.coeff k) (hG : ∀ k, 0 ≤ G.coeff k)
    (hG0 : G.coeff 0 = 1) (k : ℕ) : F.coeff k ≤ (F * G).coeff k := by
  rw [Polynomial.coeff_mul]
  have hmem : (k, 0) ∈ Finset.HasAntidiagonal.antidiagonal k := by simp
  refine le_trans ?_ (Finset.single_le_sum (fun x _ => mul_nonneg (hF _) (hG _)) hmem)
  show F.coeff k ≤ F.coeff k * G.coeff 0
  rw [hG0, mul_one]

private theorem coeff_expand_Pabs_nonneg (M : ℂ[X]) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    0 ≤ (Polynomial.expand ℝ m (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M)).coeff k := by
  rw [Polynomial.coeff_expand hm]
  split_ifs
  · exact coeff_Pabs_nonneg M _
  · exact le_rfl

private theorem coeff_expand_Pabs_zero (hM : M.coeff 0 = 1) {m : ℕ} (hm : 0 < m) :
    (Polynomial.expand ℝ m (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M)).coeff 0 = 1 := by
  rw [Polynomial.coeff_expand hm, if_pos (dvd_zero m), Nat.zero_div, coeff_Pabs_zero hM]

private theorem coeff_pp_Mfam_mono (hM : M.coeff 0 = 1) {N N' : ℕ} (h : N ≤ N') (k : ℕ) :
    (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) (((fun (M : ℂ[X]) (_ : ℕ) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M) N).coeff k ≤ (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) (((fun (M : ℂ[X]) (_ : ℕ) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M) N').coeff k := by
  induction N', h using Nat.le_induction with
  | base => exact le_rfl
  | succ N' hN ih =>
    rw [pp_succ]
    exact ih.trans (coeff_le_coeff_mul (coeff_pp_Mfam_nonneg M N')
      (coeff_expand_Pabs_nonneg M (Nat.succ_pos N')) (coeff_expand_Pabs_zero hM (Nat.succ_pos N')) k)

private theorem Mfam_coeff_zero (hM : M.coeff 0 = 1) : ∀ n, (((fun (M : ℂ[X]) (_ : ℕ) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M n).coeff 0 = 1 :=
  fun _ => coeff_Pabs_zero hM

private theorem norm_coeff_pp_le_dom (hM : M.coeff 0 = 1) (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖)
    (N k : ℕ) : ‖(((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) P N).coeff k‖ ≤ ((fun (M : ℂ[X]) (k : ℕ) => (∏ n ∈ Finset.range k, Polynomial.expand ℝ (n + 1) (∑ j ∈ M.support, Polynomial.monomial j ‖M.coeff j‖)).coeff k)) M k := by
  refine (norm_coeff_pp_le hdom N k).trans ?_
  dsimp only
  rcases le_total N k with h | h
  · exact coeff_pp_Mfam_mono hM h k
  · exact (coeff_pp_stable (Mfam_coeff_zero hM) h).le

private theorem sum_coeff_le_eval {Q : ℝ[X]} (hQ : ∀ k, 0 ≤ Q.coeff k) {r : ℝ} (hr : 0 ≤ r)
    (s : Finset ℕ) : ∑ k ∈ s, Q.coeff k * r ^ k ≤ Q.eval r := by
  classical
  have h1 : ∑ k ∈ s, Q.coeff k * r ^ k
      = ∑ k ∈ s.filter (fun k => k ∈ Q.support), Q.coeff k * r ^ k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · rfl
    · rw [Polynomial.notMem_support_iff.mp h, zero_mul]
  have h2 : s.filter (fun k => k ∈ Q.support) ⊆ Q.support := fun k hk => (Finset.mem_filter.mp hk).2
  rw [h1, Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_le_sum_of_subset_of_nonneg h2 fun k _ _ => mul_nonneg (hQ k) (pow_nonneg hr k)

private theorem eval_pp {R : Type} [CommRing R] (Q : ℕ → R[X]) (N : ℕ) (r : R) :
    (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) Q N).eval r = ∏ n ∈ Finset.range N, (Q n).eval (r ^ (n + 1)) := by
  rw [Polynomial.eval_prod]
  simp only [Polynomial.expand_eval]

private theorem summable_pow_succ {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : Summable fun n : ℕ => r ^ (n + 1) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr hr1)

private theorem prod_eval_Pabs_le (hM : M.coeff 0 = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∏ n ∈ Finset.range N, (((fun (M : ℂ[X]) (_ : ℕ) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M n).eval (r ^ (n + 1)) ≤ ((fun (M : ℂ[X]) (r : ℝ) => Real.exp ((∑ k ∈ M.support, ‖M.coeff k‖) * ∑' n : ℕ, r ^ (n + 1)))) M r := by
  dsimp only
  have hfac : ∀ n : ℕ, (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval (r ^ (n + 1)) = 1 + ((((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval (r ^ (n + 1)) - 1) :=
    fun n => by ring
  have hnn : ∀ n : ℕ, 0 ≤ (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval (r ^ (n + 1)) - 1 :=
    fun n => sub_nonneg.mpr (one_le_eval_Pabs hM (pow_nonneg hr _))
  calc ∏ n ∈ Finset.range N, (((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval (r ^ (n + 1))
      = ∏ n ∈ Finset.range N, (1 + ((((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval (r ^ (n + 1)) - 1)) :=
        Finset.prod_congr rfl fun n _ => hfac n
    _ ≤ Real.exp (∑ n ∈ Finset.range N, ((((fun (M : ℂ[X]) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M).eval (r ^ (n + 1)) - 1)) :=
        Real.prod_one_add_le_exp_sum _ hnn
    _ ≤ Real.exp (∑ n ∈ Finset.range N, ((fun (M : ℂ[X]) => ∑ k ∈ M.support, ‖M.coeff k‖)) M * r ^ (n + 1)) := by
        refine Real.exp_le_exp.mpr (Finset.sum_le_sum fun n _ => ?_)
        exact eval_Pabs_sub_one_le hM (pow_nonneg hr _) (pow_le_one₀ hr hr1.le)
    _ ≤ ((fun (M : ℂ[X]) (r : ℝ) => Real.exp ((∑ k ∈ M.support, ‖M.coeff k‖) * ∑' n : ℕ, r ^ (n + 1)))) M r := by
        refine Real.exp_le_exp.mpr ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (Cst_nonneg M)
        exact (summable_pow_succ hr hr1).sum_le_tsum _ fun n _ => pow_nonneg hr _

private theorem summable_dom (hM : M.coeff 0 = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ => ((fun (M : ℂ[X]) (k : ℕ) => (∏ n ∈ Finset.range k, Polynomial.expand ℝ (n + 1) (∑ j ∈ M.support, Polynomial.monomial j ‖M.coeff j‖)).coeff k)) M k * r ^ k := by
  refine summable_of_sum_range_le (c := ((fun (M : ℂ[X]) (r : ℝ) => Real.exp ((∑ k ∈ M.support, ‖M.coeff k‖) * ∑' n : ℕ, r ^ (n + 1)))) M r)
    (fun k => mul_nonneg (coeff_pp_Mfam_nonneg M k k) (pow_nonneg hr k)) fun N => ?_
  calc ∑ k ∈ Finset.range N, ((fun (M : ℂ[X]) (k : ℕ) => (∏ n ∈ Finset.range k, Polynomial.expand ℝ (n + 1) (∑ j ∈ M.support, Polynomial.monomial j ‖M.coeff j‖)).coeff k)) M k * r ^ k
      ≤ ∑ k ∈ Finset.range N, (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) (((fun (M : ℂ[X]) (_ : ℕ) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M) N).coeff k * r ^ k := by
        refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr k)
        exact coeff_pp_Mfam_mono hM (Finset.mem_range.mp hk).le k
    _ ≤ (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) (((fun (M : ℂ[X]) (_ : ℕ) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M) N).eval r := sum_coeff_le_eval (coeff_pp_Mfam_nonneg M N) hr _
    _ = ∏ n ∈ Finset.range N, (((fun (M : ℂ[X]) (_ : ℕ) => ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖)) M n).eval (r ^ (n + 1)) := eval_pp _ _ _
    _ ≤ ((fun (M : ℂ[X]) (r : ℝ) => Real.exp ((∑ k ∈ M.support, ‖M.coeff k‖) * ∑' n : ℕ, r ^ (n + 1)))) M r := prod_eval_Pabs_le hM hr hr1 N

private theorem summable_norm_eval_sub_one (hP : ∀ n, (P n).coeff 0 = 1)
    (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖(P n).eval (q ^ (n + 1)) - 1‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)).mul_left
      (((fun (M : ℂ[X]) => ∑ k ∈ M.support, ‖M.coeff k‖)) M))
  have h := norm_eval_sub_one_le (hP n) (hdom n) (x := q ^ (n + 1))
    (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hq.le)
  rwa [norm_pow] at h

private theorem multipliable_eval (hP : ∀ n, (P n).coeff 0 = 1)
    (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖) {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => (P n).eval (q ^ (n + 1)) :=
  (multipliable_one_add_of_summable (summable_norm_eval_sub_one hP hdom hq)).congr
    fun _ => add_sub_cancel 1 _

private theorem tsum_coeff_pp_mul_pow (P : ℕ → ℂ[X]) (N : ℕ) (q : ℂ) :
    ∑' m : ℕ, (((fun {R : Type} [CommRing R] (P : ℕ → R[X]) (N : ℕ) => ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))) P N).coeff m * q ^ m = ∏ n ∈ Finset.range N, (P n).eval (q ^ (n + 1)) := by
  rw [← eval_pp, Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact tsum_eq_sum fun m hm => by rw [Polynomial.notMem_support_iff.mp hm, zero_mul]

end Analytic

/-- A coefficientwise bounded Euler product equals its stabilized coefficient series inside the unit disk. -/
theorem _root_.solution
    (P : ℕ → ℂ[X]) (M : ℂ[X])
    (hP : ∀ n, (P n).coeff 0 = 1)
    (hM : M.coeff 0 = 1)
    (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖)
    (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum
      (fun m : ℕ =>
        (∏ n ∈ Finset.range m, Polynomial.expand ℂ (n + 1) (P n)).coeff m * q ^ m)
      (∏' n : ℕ, (P n).eval (q ^ (n + 1))) := by
  let pp : ℕ → ℂ[X] := fun N => ∏ n ∈ Finset.range N, Polynomial.expand ℂ (n + 1) (P n)
  let dom : ℕ → ℝ := fun k =>
    (∏ n ∈ Finset.range k, Polynomial.expand ℝ (n + 1)
      (∑ j ∈ M.support, Polynomial.monomial j ‖M.coeff j‖)).coeff k
  have hsum : Summable fun m : ℕ => dom m * ‖q‖ ^ m := summable_dom hM (norm_nonneg q) hq
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N m : ℕ) => (pp N).coeff m * q ^ m)
    (g := fun m : ℕ => (pp m).coeff m * q ^ m) hsum ?_ ?_
  rotate_left
  · intro m
    refine tendsto_const_nhds.congr' (Filter.eventuallyEq_of_mem (Filter.Ici_mem_atTop m)
      fun N hN => ?_)
    change (pp m).coeff m * q ^ m = (pp N).coeff m * q ^ m
    rw [coeff_pp_stable hP (show m ≤ N from hN)]
  · refine Eventually.of_forall fun N m => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (norm_coeff_pp_le_dom hM hdom N m) (pow_nonneg (norm_nonneg _) _)
  dsimp only [pp] at hT
  simp_rw [tsum_coeff_pp_mul_pow] at hT
  have heq : (∑' m : ℕ, (pp m).coeff m * q ^ m) = ∏' n : ℕ, (P n).eval (q ^ (n + 1)) :=
    tendsto_nhds_unique hT (multipliable_eval hP hdom hq).tendsto_prod_tprod_nat
  have hs : Summable fun m : ℕ => (pp m).coeff m * q ^ m :=
    Summable.of_norm_bounded hsum fun m => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (norm_coeff_pp_le_dom hM hdom m m) (pow_nonneg (norm_nonneg _) _)
  rw [← heq]
  exact hs.hasSum

end N25
