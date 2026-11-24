-- Prove2me | solution 1 for HermitekLEAN.summable_norm_sq_Phi_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:26.661006+00:00
-- url     : https://prove2.me/submissions/f866ee7c-97b4-45ca-ab2b-5540c76b5e9b

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_phi_explicit
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private lemma summable_nat_pow_mul_pow_div_factorial_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)) := by
  let f : ℕ → ℝ := fun n => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)
  rw [← @summable_nat_add_iff ℝ _ _ _ _ m]
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ))) ?_ ?_ ?_
  · intro n
    positivity
  · intro n
    have hdesc_nat : (n + 1) ^ m ≤ (n + m).descFactorial m := by
      simpa only [Nat.add_comm, Nat.add_assoc, add_tsub_cancel_left, Nat.add_left_comm] using
        (Nat.pow_sub_le_descFactorial (n + m) m)
    have hpow_real :
        ((n + m + 1 : ℝ) ^ m) ≤
          (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by
      have hdesc : ((n + 1 : ℝ) ^ m) ≤ (((n + m).descFactorial m : ℕ) : ℝ) := by
        exact_mod_cast hdesc_nat
      calc
        ((n + m + 1 : ℝ) ^ m) ≤ (((m + 1 : ℝ) * (n + 1)) ^ m) := by
          gcongr
          nlinarith only []
        _ = (m + 1 : ℝ) ^ m * (n + 1 : ℝ) ^ m := by rw [mul_pow]
        _ ≤ (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by gcongr
    have hfact :
        (Nat.factorial n : ℝ) * (((n + m).descFactorial m : ℕ) : ℝ) =
          (Nat.factorial (n + m) : ℝ) := by
      have hfact_nat : (n.factorial * (n + m).descFactorial m) = (n + m).factorial := by
        simpa only [Nat.add_comm, add_tsub_cancel_left, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.factorial_mul_descFactorial (show m ≤ n + m by omega))
      exact_mod_cast hfact_nat
    have hcalc :
        (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ)
          = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := by
      rw [pow_add, ← hfact]
      have hnfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hndesc_nat : (n + m).descFactorial m ≠ 0 :=
        Nat.ne_of_gt (Nat.descFactorial_pos.mpr (show m ≤ n + m by omega))
      have hndesc : (((n + m).descFactorial m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hndesc_nat
      field_simp [hnfact, hndesc]
    calc
      f (n + m)
          = ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) / (Nat.factorial (n + m) : ℝ) := by simp [f]
      _ ≤ (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ) := by
              have hpowx :
                  ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                    ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                      x ^ (n + m) := mul_le_mul_of_nonneg_right hpow_real (pow_nonneg hx _)
              have hfacpos : 0 < (Nat.factorial (n + m) : ℝ) := by positivity
              rw [div_le_iff₀ hfacpos]
              calc
                ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                    ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                      x ^ (n + m) := hpowx
                _ =
                    ((((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) *
                        x ^ (n + m)) / (Nat.factorial (n + m) : ℝ)) *
                      (Nat.factorial (n + m) : ℝ) := by
                        have hfacne : (Nat.factorial (n + m) : ℝ) ≠ 0 := by positivity
                        field_simp [hfacne]
      _ = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := hcalc
  · simpa only [mul_comm, mul_left_comm, pow_add, mul_assoc] using
      (Real.summable_pow_div_factorial x).mul_left ((m + 1 : ℝ) ^ m * x ^ m)
private lemma factorial_ratio_le_pow_succ {n k j : ℕ} (hjn : j ≤ n) (hjk : j ≤ k) :
    (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) ≤ (n + 1 : ℝ) ^ k := by
  have hnat : n.descFactorial j ≤ (n + 1) ^ k := by
    calc
      n.descFactorial j ≤ n ^ j := Nat.descFactorial_le_pow _ _
      _ ≤ (n + 1) ^ j := Nat.pow_le_pow_left n.le_succ _
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos _) hjk
  have hdiv_nat : n.descFactorial j = n.factorial / (n - j).factorial := by
    rw [Nat.descFactorial_eq_div hjn]
  have hdiv : (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) = n.descFactorial j := by
    rw [hdiv_nat, Nat.cast_div (Nat.factorial_dvd_factorial (Nat.sub_le n j))]
    positivity
  rw [hdiv]
  exact_mod_cast hnat
private lemma choose_partial_sum_le_pow_two (k n : ℕ) :
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ)) ≤ (2 : ℝ) ^ k := by
  calc
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ))
      ≤ Finset.sum (Finset.range (k + 1)) (fun j => (Nat.choose k j : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · simp_all only [range_subset_range, add_le_add_iff_right, min_le_iff, Std.le_refl,
              true_or]
          · simp_all only [mem_range, Order.lt_add_one_iff, le_inf_iff, true_and, not_le,
              Nat.cast_nonneg, implies_true]
    _ = (2 : ℝ) ^ k := by exact_mod_cast Nat.sum_range_choose k
private lemma phi_norm_le_majorant {k n : ℕ} {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖Phi k n z‖ ≤ ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
      Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
  let S := Finset.range (min k n + 1)
  let term : ℕ → ℂ := fun j =>
    (-1 : ℂ) ^ j * ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
      z ^ (n - j) * star z ^ (k - j)
  let common : ℝ := ((n + 1 : ℝ) ^ k) * R ^ k * R ^ n
  rw [phi_explicit]
  have hsum_norm : ‖Finset.sum S term‖ ≤ Finset.sum S (fun j => ‖term j‖) := norm_sum_le _ _
  have hterm_bound : ∀ j ∈ S, ‖term j‖ ≤ (Nat.choose k j : ℝ) * common := by
    intro j hj
    have hjk : j ≤ k := by
      simp [S] at hj
      omega
    have hjn : j ≤ n := by
      simp [S] at hj
      omega
    have hratio := factorial_ratio_le_pow_succ hjn hjk
    have hz1 : ‖z‖ ^ (n - j) ≤ R ^ n := by
      calc
        ‖z‖ ^ (n - j) ≤ R ^ (n - j) := by exact pow_le_pow_left₀ (norm_nonneg _) hz _
        _ ≤ R ^ n := by exact pow_le_pow_right₀ hR (Nat.sub_le _ _)
    have hz2 : ‖z‖ ^ (k - j) ≤ R ^ k := by
      calc
        ‖z‖ ^ (k - j) ≤ R ^ (k - j) := by exact pow_le_pow_left₀ (norm_nonneg _) hz _
        _ ≤ R ^ k := by exact pow_le_pow_right₀ hR (Nat.sub_le _ _)
    calc
      ‖term j‖
        = (Nat.choose k j : ℝ) * ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
            ‖z‖ ^ (n - j) * ‖z‖ ^ (k - j) := by
            dsimp [term]
            simp [norm_pow]
      _ ≤ (Nat.choose k j : ℝ) * ((n + 1 : ℝ) ^ k) * R ^ n * R ^ k := by gcongr
      _ = (Nat.choose k j : ℝ) * common := by
            dsimp [common]
            ac_rfl
  have hsum_bound :
      Finset.sum S (fun j => ‖term j‖) ≤ Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) :=
    Finset.sum_le_sum (fun j hj => hterm_bound j hj)
  have hsum_factor :
      Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) =
        (Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common := by rw [Finset.sum_mul]
  have hfront_nonneg :
      0 ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ := norm_nonneg _
  have hfront :
      ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) := by
    rw [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      one_div]
  calc
    ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) * Finset.sum S term‖
      ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
          Finset.sum S (fun j => ‖term j‖) := by
            exact le_trans (norm_mul_le _ _) <|
              mul_le_mul_of_nonneg_left hsum_norm (norm_nonneg _)
    _ ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
          Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) :=
            mul_le_mul_of_nonneg_left hsum_bound hfront_nonneg
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by rw [hfront]
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          ((Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common) := by rw [hsum_factor]
    _ ≤ ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          (((2 : ℝ) ^ k) * common) := by
            gcongr
            exact choose_partial_sum_le_pow_two k n
    _ = ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
            dsimp [common]
            rw [div_eq_mul_inv]
            ring
private lemma summable_sq_Phi_eval (k : ℕ) (z : ℂ) :
    Summable (fun n => ‖Phi k n z‖ ^ 2) := by
  let R : ℝ := max 1 ‖z‖
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hzR : ‖z‖ ≤ R := by
    dsimp [R]
    exact le_max_right _ _
  let C : ℝ := (((2 : ℝ) ^ k) ^ 2 * (R ^ k) ^ 2) / (Nat.factorial k : ℝ)
  have hbase0 :
      Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (2 * k)) * (R ^ 2) ^ n / (Nat.factorial n : ℝ)) := by
    apply summable_nat_pow_mul_pow_div_factorial_nonneg
    positivity
  have hbase :
      Summable (fun n : ℕ => (((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
    refine hbase0.congr ?_
    intro n
    rw [← pow_mul, ← pow_mul]
    simp [pow_mul, Nat.mul_comm]
  have hmajorant :
      Summable (fun n : ℕ => C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)))
          := hbase.mul_left C
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hmajorant
  intro n
  have hphi := phi_norm_le_majorant (k := k) (n := n) (R := R) hR hzR
  have hrhs_nonneg :
      0 ≤ ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
        Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by positivity
  have hphi_sq :
      ‖Phi k n z‖ ^ 2 ≤
        (((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hphi 2
  have hsqrt_ne : Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by positivity
  calc
    ‖Phi k n z‖ ^ 2
      ≤ (((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) ^ 2 := hphi_sq
    _ = C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
      dsimp [C]
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (by positivity)]
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution (k : ℕ) (z : ℂ) :
    Summable (fun n : ℕ => ‖Phi k n z‖ ^ 2) :=
  summable_sq_Phi_eval k z
end HermitekLEAN
