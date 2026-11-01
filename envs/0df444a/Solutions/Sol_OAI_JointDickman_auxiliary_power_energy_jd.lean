-- Prove2me | solution 1 for OAI.JointDickman.auxiliary_power_energy_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:24:11.08851+00:00
-- url     : https://prove2.me/submissions/245241ab-b4fb-426d-b550-eff81b7611c5

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_ramare_product_sparse_integral_jd

section
-- module Solutions.OAIQ083_JD.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquareKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential majorant for Dirichlet-polynomial mean squares

This is the elementary kernel behind the mean-value estimate used at the
start of corrected MRT, Appendix A, Proposition A.3.  Its Fourier transform
has quadratic decay, so the ensuing row sum loses no logarithm.
-/

namespace TwoPointCorrelations

open Complex MeasureTheory Set

lemma mrtMeanSquareKernel_right {T : ℝ} (ω : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonneg ht,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_left {T : ℝ} (ω : ℝ) {t : ℝ} (ht : t ≤ 0) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonpos ht, neg_neg,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_integrable {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    Integrable (mrtMeanSquareKernel T ω) := by
  have hr : IntegrableOn (mrtMeanSquareKernel T ω) (Ioi 0) := by
    apply (integrableOn_exp_mul_complex_Ioi
      (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0).congr_fun
        (fun t ht => ?_) measurableSet_Ioi
    simpa using (mrtMeanSquareKernel_right ω ht.le).symm
  have hl : IntegrableOn (mrtMeanSquareKernel T ω) (Iic 0) := by
    apply (integrableOn_exp_mul_complex_Iic
      (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using one_div_pos.mpr hT) 0).congr_fun
        (fun t ht => ?_) measurableSet_Iic
    exact (mrtMeanSquareKernel_left ω ht).symm
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

/-- Exact quadratic-decay Fourier transform, without an asymptotic constant. -/
theorem integral_mrtMeanSquareKernel {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    (∫ t : ℝ, mrtMeanSquareKernel T ω t) =
      ((2 * T / (1 + T ^ 2 * ω ^ 2) : ℝ) : ℂ) := by
  have hi := mrtMeanSquareKernel_integrable hT ω
  have hr : (∫ t in Ioi (0 : ℝ), mrtMeanSquareKernel T ω t) =
      -1 / (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), Complex.exp
          ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simpa using mrtMeanSquareKernel_right ω ht.le
      _ = _ := by
        simpa using integral_exp_mul_complex_Ioi
          (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0
  have hl : (∫ t in Iic (0 : ℝ), mrtMeanSquareKernel T ω t) =
      1 / (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Iic (0 : ℝ), Complex.exp
          ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        exact mrtMeanSquareKernel_left ω ht
      _ = _ := by
        simpa using integral_exp_mul_complex_Iic
          (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using one_div_pos.mpr hT) 0
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic, hl, hr]
  have hTp : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hp : (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : (1 / T : ℝ) = 0 := by simpa using this
    exact (one_div_pos.mpr hT).ne' he
  have hm : (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : -(1 / T : ℝ) = 0 := by simpa using this
    exact (neg_lt_zero.mpr (one_div_pos.mpr hT)).ne he
  have hp1 : (1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hm1 : (-1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hd : (1 + T ^ 2 * ω ^ 2 : ℝ) ≠ 0 := by positivity
  have hdc : (1 + (T : ℂ) ^ 2 * (ω : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring_nf
  field_simp [hp1, hm1, hdc]
  ring_nf
  simp only [Complex.I_sq]
  ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquareRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable quadratic-gap bounds for the MRT Dirichlet mean-value estimate. -/

namespace TwoPointCorrelations

open Finset
open scoped BigOperators

lemma mrt_log_gap {x y N : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyN : y ≤ N) :
    (y - x) / N ≤ Real.log y - Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  have hN : 0 < N := hy.trans_le hyN
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne', inv_div] at hlog
  calc
    (y - x) / N ≤ (y - x) / y :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hy hyN
    _ = 1 - x / y := by field_simp
    _ ≤ _ := hlog

lemma mrt_quadratic_gap_sum {R : ℝ} (hR : 0 < R) (N : ℕ) :
    (∑ k ∈ Ioc 0 N, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ 2 * R + 1 := by
  let K := Nat.ceil R
  let M := max K N
  have hK : 0 < K := Nat.ceil_pos.mpr hR
  have hRK : R ≤ (K : ℝ) := Nat.le_ceil R
  have hKR : (K : ℝ) < R + 1 := Nat.ceil_lt_add_one hR.le
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hKM : K ≤ M := le_max_left _ _
  have hsplit : Ioc 0 M = Ioc 0 K ∪ Ioc K M := by
    ext k
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 K) (Ioc K M) := by
    rw [disjoint_left]
    simp only [mem_Ioc]
    omega
  have hnear : (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Ioc 0 K, (1 : ℝ) := by
        apply sum_le_sum
        intro k _
        exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((k : ℝ) / R)])
      _ = _ := by simp
  have hfar : (∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹) ≤ R := by
    calc
      _ ≤ ∑ k ∈ Ioc K M, R ^ 2 * ((k : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (hK.trans (mem_Ioc.mp hk).1)
        calc
          _ ≤ (((k : ℝ) / R) ^ 2)⁻¹ := by
            apply inv_anti₀ (sq_pos_of_pos (div_pos hk0 hR))
            linarith
          _ = _ := by field_simp
      _ = R ^ 2 * ∑ k ∈ Ioc K M, ((k : ℝ) ^ 2)⁻¹ := (mul_sum _ _ _).symm
      _ ≤ R ^ 2 * ((K : ℝ)⁻¹ - (M : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (α := ℝ) hK.ne' hKM)
          (sq_nonneg R)
      _ ≤ R ^ 2 * (K : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg M))
      _ ≤ R := by
        rw [← div_eq_mul_inv, div_le_iff₀ hK0]
        nlinarith
  calc
    _ ≤ ∑ k ∈ Ioc 0 M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [mem_Ioc] at hk ⊢
        exact ⟨hk.1, hk.2.trans (le_max_right _ _)⟩
      · intro k _ _
        positivity
    _ = (∑ k ∈ Ioc 0 K, (1 + ((k : ℝ) / R) ^ 2)⁻¹) +
        ∑ k ∈ Ioc K M, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by rw [hsplit, sum_union hd]
    _ ≤ (K : ℝ) + R := add_le_add hnear hfar
    _ ≤ 2 * R + 1 := by linarith

lemma mrt_nat_distance_sum (φ : ℕ → ℝ) (hφ : ∀ k, 0 ≤ φ k)
    {m N : ℕ} (hm : m ∈ Ioc 0 N) :
    (∑ n ∈ Ioc 0 N, φ (Nat.dist n m)) ≤
      φ 0 + 2 * ∑ k ∈ Ioc 0 N, φ k := by
  have hm' := mem_Ioc.mp hm
  have hsplit : Ioc 0 N = Ioc 0 m ∪ Ioc m N := by
    ext n
    simp only [mem_Ioc, mem_union]
    omega
  have hd : Disjoint (Ioc 0 m) (Ioc m N) := by
    rw [disjoint_left]
    simp only [mem_Ioc]
    omega
  have hleft : (∑ n ∈ Ioc 0 m, φ (Nat.dist n m)) = ∑ k ∈ range m, φ k := by
    apply sum_bij (fun n _ => m - n)
    · intro n hn
      have hn' := mem_Ioc.mp hn
      simp only [mem_range]
      omega
    · intro n hn n' hn' he
      have h1 := mem_Ioc.mp hn
      have h2 := mem_Ioc.mp hn'
      omega
    · intro k hk
      have hk' := mem_range.mp hk
      refine ⟨m - k, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rw [Nat.dist_eq_sub_of_le (mem_Ioc.mp hn).2]
  have hright : (∑ n ∈ Ioc m N, φ (Nat.dist n m)) = ∑ k ∈ Ioc 0 (N - m), φ k := by
    apply sum_bij (fun n _ => n - m)
    · intro n hn
      have hn' := mem_Ioc.mp hn
      simp only [mem_Ioc]
      omega
    · intro n hn n' hn' he
      have h1 := mem_Ioc.mp hn
      have h2 := mem_Ioc.mp hn'
      omega
    · intro k hk
      have hk' := mem_Ioc.mp hk
      refine ⟨m + k, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro n hn
      rw [Nat.dist_eq_sub_of_le_right (mem_Ioc.mp hn).1.le]
  have hrange : range m = insert 0 (Ioc 0 (m - 1)) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  have hzero : 0 ∉ Ioc 0 (m - 1) := by simp
  conv_lhs => rw [hsplit, sum_union hd, hleft, hright, hrange, sum_insert hzero]
  have hL : (∑ k ∈ Ioc 0 (m - 1), φ k) ≤ ∑ k ∈ Ioc 0 N, φ k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hk' := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨hk'.1, by omega⟩
    · intro k _ _
      exact hφ k
  have hR : (∑ k ∈ Ioc 0 (N - m), φ k) ≤ ∑ k ∈ Ioc 0 N, φ k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hk' := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨hk'.1, by omega⟩
    · intro k _ _
      exact hφ k
  linarith

lemma mrt_log_nat_gap {m n N : ℕ} (hm : m ∈ Ioc 0 N) (hn : n ∈ Ioc 0 N) :
    (Nat.dist m n : ℝ) / (N : ℝ) ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have hm' := mem_Ioc.mp hm
  have hn' := mem_Ioc.mp hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm'.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
  rcases le_total m n with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm0 (by exact_mod_cast h)))]
    exact mrt_log_gap hm0 (by exact_mod_cast h) (by exact_mod_cast hn'.2)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast h)))]
    exact mrt_log_gap hn0 (by exact_mod_cast h) (by exact_mod_cast hm'.2)

/-- The actual logarithmic-frequency kernel has row sum `O(T+N)`. -/
theorem mrt_logarithmic_kernel_row {T : ℝ} (hT : 0 < T) {N m : ℕ}
    (hm : m ∈ Ioc 0 N) :
    (∑ n ∈ Ioc 0 N,
      2 * T / (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2)) ≤
      8 * (T + (N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (mem_Ioc.mp hm).1.trans_le (mem_Ioc.mp hm).2
  let R := (N : ℝ) / T
  have hR : 0 < R := div_pos hN hT
  have hterm (n : ℕ) (hn : n ∈ Ioc 0 N) :
      2 * T / (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2) ≤
      2 * T * (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ := by
    have hgap := mrt_log_nat_gap hn hm
    rw [abs_sub_comm] at hgap
    have hsq : ((Nat.dist n m : ℝ) / (N : ℝ)) ^ 2 ≤
        (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (by positivity) hgap 2
    have he : ((Nat.dist n m : ℝ) / R) ^ 2 =
        T ^ 2 * ((Nat.dist n m : ℝ) / (N : ℝ)) ^ 2 := by
      dsimp only [R]
      field_simp
    rw [he, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply inv_anti₀ (by positivity)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (sq_nonneg T))
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, 2 * T * (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ :=
      sum_le_sum hterm
    _ = 2 * T * ∑ n ∈ Ioc 0 N, (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹ :=
      (mul_sum _ _ _).symm
    _ ≤ 2 * T * (1 + 2 * (2 * R + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hd := mrt_nat_distance_sum (fun k => (1 + ((k : ℝ) / R) ^ 2)⁻¹)
        (fun _ => by positivity) hm
      have hd' : (∑ n ∈ Ioc 0 N, (1 + ((Nat.dist n m : ℝ) / R) ^ 2)⁻¹) ≤
          1 + 2 * ∑ k ∈ Ioc 0 N, (1 + ((k : ℝ) / R) ^ 2)⁻¹ := by
        simpa only [Nat.cast_zero, zero_div, zero_pow (by decide : 2 ≠ 0), add_zero,
          inv_one] using hd
      exact hd'.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (mrt_quadratic_gap_sum hR N)
          (by norm_num : (0 : ℝ) ≤ 2)))
    _ ≤ 8 * (T + (N : ℝ)) := by
      dsimp only [R]
      have hc : T * ((N : ℝ) / T) = N := mul_div_cancel₀ _ hT.ne'
      nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Dirichlet-polynomial mean squares, using the integrable
exponential majorant and its exact quadratic-decay Fourier transform. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset Set
open scoped BigOperators ComplexConjugate

lemma mrt_phase_pair (x y : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) *
        conj (Complex.exp ((y : ℂ) * Complex.I)) =
      Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, ofReal_sub]
  ring

lemma mrt_weighted_square_expansion {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (T t : ℝ) :
    ((Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S,
        (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t := by
  rw [ofReal_mul, ofReal_pow, ← Complex.mul_conj']
  simp only [mrtExponentialPolynomial, map_sum, sum_mul, mul_sum]
  rw [sum_comm (s := S) (t := S)]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [map_mul]
  have hp := mrt_phase_pair (freq i * t) (freq j * t)
  have he : (((freq i - freq j) * t : ℝ) : ℂ) * Complex.I =
      ((freq i * t - freq j * t : ℝ) : ℂ) * Complex.I := by congr 1; push_cast <;> ring
  dsimp only [mrtMeanSquareKernel]
  rw [he, ← hp]
  ring

lemma mrt_weighted_square_integrable {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
  have hi : Integrable (fun t : ℝ => ∑ i ∈ S, ∑ j ∈ S,
      (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
  have he : (fun t : ℝ => ∑ i ∈ S, ∑ j ∈ S,
      (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t) =
      fun t => ((Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    exact (mrt_weighted_square_expansion S a freq T t).symm
  rw [he] at hi
  simpa only [RCLike.re_to_complex, ofReal_re] using hi.re

/-- Exact finite mean-square formula.  This identity is valid for arbitrary
real frequencies; separation is needed only for the subsequent bound. -/
theorem mrt_weighted_mean_square {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)).re *
        (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
  have he : (∫ t : ℝ, ((Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)) *
        ((2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2) : ℝ) : ℂ) := by
    simp_rw [mrt_weighted_square_expansion]
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply sum_congr rfl
        intro j _
        rw [integral_const_mul, integral_mrtMeanSquareKernel hT]
      · intro j _
        exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
    · intro i _
      apply integrable_finsetSum
      intro j _
      exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
  rw [integral_complex_ofReal] at he
  have hr := congrArg Complex.re he
  simpa only [ofReal_re, Complex.re_sum, mul_re, ofReal_im, mul_zero, sub_zero] using hr

/-- The exact integral is bounded by the positive kernel quadratic form. -/
lemma mrt_weighted_mean_square_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖a i‖ * ‖a j‖ *
        (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
  rw [mrt_weighted_mean_square S a freq hT]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simpa only [norm_mul, norm_conj] using Complex.re_le_norm (a i * conj (a j))

/-- A symmetric positive kernel is bounded on the squared norm by its
largest row sum.  The numerical row estimate is proved separately. -/
lemma mrt_symmetric_row_bound {ι : Type*} (S : Finset ι) (K : ι → ι → ℝ)
    (v : ι → ℝ) (C : ℝ) (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, v i * v j * K i j) ≤ C * ∑ i ∈ S, (v i) ^ 2 := by
  have he : (∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j) =
      ∑ i ∈ S, (v i) ^ 2 * ∑ j ∈ S, K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S) (f := fun i j => (v j) ^ 2 / 2 * K i j)]
    simp only [← mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hk : (∑ j ∈ S, K j i) = ∑ j ∈ S, K i j :=
      sum_congr rfl fun j hj => hsymm j hj i hi
    rw [hk]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hK i hi j hj)
      nlinarith [sq_nonneg (v i - v j)]
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

theorem mrt_weighted_mean_square_of_rows {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T C : ℝ} (hT : 0 < T)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, 2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) ≤ C) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      C * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  apply (mrt_weighted_mean_square_le S a freq hT).trans
  apply mrt_symmetric_row_bound S _ (fun i => ‖a i‖) C
    (fun _ _ _ _ => by positivity) _ hrow
  intro i _ j _
  rw [show (freq i - freq j) ^ 2 = (freq j - freq i) ^ 2 by ring]

lemma mrtExponentialPolynomial_continuous {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) : Continuous (mrtExponentialPolynomial S a freq) := by
  unfold mrtExponentialPolynomial
  fun_prop

lemma mrt_unweighted_mean_square_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial S a freq t‖ ^ 2) ≤
      Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 := by
  have hf := (mrtExponentialPolynomial_continuous S a freq).norm.pow 2
  have hi := mrt_weighted_square_integrable S a freq hT
  have hc : Continuous (fun t : ℝ => Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
    exact (Real.continuous_exp.comp (continuous_abs.neg.div_const T)).mul hf
  have hb : -T ≤ T := by linarith
  calc
    _ ≤ ∫ t in -T..T, Real.exp 1 * (Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on hb (hf.intervalIntegrable (-T) T)
        ((continuous_const.mul hc).intervalIntegrable (-T) T)
      intro t ht
      have hat : |t| ≤ T := abs_le.mpr ht
      have hh : 0 ≤ 1 + -|t| / T := by
        have := (div_le_one hT).mpr hat
        rw [neg_div]
        linarith
      have he : 1 ≤ Real.exp 1 * Real.exp (-|t| / T) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp hh
      change ‖mrtExponentialPolynomial S a freq t‖ ^ 2 ≤
        Real.exp 1 * (Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2)
      nlinarith [sq_nonneg ‖mrtExponentialPolynomial S a freq t‖]
    _ = Real.exp 1 * ∫ t in -T..T, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a freq t‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le hb]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun t => by positivity)

/-- The standard Dirichlet-polynomial mean-value bound, with an absolute
constant and no logarithmic loss.  Arbitrary complex coefficients are allowed. -/
theorem mrt_dirichlet_mean_square (N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial (Finset.Ioc 0 N) a (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + (N : ℝ)) * ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 := by
  have hrow : ∀ m ∈ Finset.Ioc 0 N,
      (∑ n ∈ Finset.Ioc 0 N, 2 * T /
        (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2)) ≤
          8 * (T + (N : ℝ)) := by
    intro m hm
    convert mrt_logarithmic_kernel_row hT hm using 1
    all_goals try with_reducible_and_instances rfl
    apply sum_congr rfl
    intro n _
    congr 2
    ring
  calc
    _ ≤ Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial (Finset.Ioc 0 N) a (fun n => -Real.log (n : ℝ)) t‖ ^ 2 :=
      mrt_unweighted_mean_square_le _ _ _ hT
    _ ≤ Real.exp 1 * (8 * (T + (N : ℝ)) * ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mrt_weighted_mean_square_of_rows _ _ _ hT hrow)
        (Real.exp_pos _).le
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTDyadicMeanSquare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized dyadic Dirichlet-polynomial mean-value estimate used in
corrected MRT Appendix A.  The coefficient bound is completely arbitrary. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset
open scoped BigOperators

theorem mrt_dirichlet_mean_square_subset (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hrow : ∀ m ∈ S,
      (∑ n ∈ S, 2 * T /
        (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2)) ≤
          8 * (T + (N : ℝ)) := by
    intro m hm
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (-Real.log (m : ℝ) - -Real.log (n : ℝ)) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
      _ = ∑ n ∈ Ioc 0 N, 2 * T /
          (1 + T ^ 2 * (Real.log (m : ℝ) - Real.log (n : ℝ)) ^ 2) := by
        apply sum_congr rfl
        intro n _
        have he (a b : ℝ) : (-a - -b) ^ 2 = (a - b) ^ 2 := by ring
        simp only [he]
      _ ≤ _ := mrt_logarithmic_kernel_row hT (hS hm)
  calc
    _ ≤ Real.exp 1 * ∫ t : ℝ, Real.exp (-|t| / T) *
        ‖mrtExponentialPolynomial S a (fun n => -Real.log (n : ℝ)) t‖ ^ 2 :=
      mrt_unweighted_mean_square_le _ _ _ hT
    _ ≤ Real.exp 1 * (8 * (T + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mrt_weighted_mean_square_of_rows _ _ _ hT hrow)
        (Real.exp_pos _).le
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_ShortSumSampling
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_DivisibilityPrefix
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact change of variables `x=u*z` for a divisibility indicator,
including the floor endpoint `floor(X/u)`. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma positivePrefix_eq_Icc (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix F X = ∑ n ∈ Icc 1 X, F n := by
  simpa only [Nat.zero_add, positivePrefix] using (sum_Icc_shift F 0 X).symm

theorem divisibility_positivePrefix (F : ℕ → ℂ) (u X : ℕ) (hu : 0 < u) :
    positivePrefix (fun n => natDivisibilityIndicator u n * F n) X =
      positivePrefix (fun z => F (u * z)) (X / u) := by
  calc
    _ = ∑ n ∈ (Icc 1 X).filter (fun n => u ∣ n), F n := by
      rw [positivePrefix_eq_Icc, sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : u ∣ n <;> simp only [natDivisibilityIndicator, hn, ite_true, if_true, ite_false, if_false,
        one_mul, zero_mul]
    _ = ∑ z ∈ Icc 1 (X / u), F (u * z) := by
      symm
      apply sum_bij (fun z _ => u * z)
      · intro z hz
        obtain ⟨hz₁, hzX⟩ := mem_Icc.mp hz
        apply mem_filter.mpr
        refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hu hz₁, ?_⟩, dvd_mul_right u z⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hu).mp hzX
      · intro z _ w _ heq
        exact Nat.eq_of_mul_eq_mul_left hu heq
      · intro n hn
        obtain ⟨hnI, hdiv⟩ := mem_filter.mp hn
        obtain ⟨hn₁, hnX⟩ := mem_Icc.mp hnI
        refine ⟨n / u, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnX⟩, Nat.mul_div_cancel' hdiv⟩
        exact Nat.div_pos (Nat.le_of_dvd hn₁ hdiv) hu
      · intro z _
        rfl
    _ = _ := (positivePrefix_eq_Icc (fun z => F (u * z)) (X / u)).symm

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTRamareIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The corrected Ramaré identity from MRT v3, equation (3.2).
The denominator retains `1_{p ∤ m}`; repeated prime factors are allowed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma finitePrimeDivisorCount_eq_card (P : Finset ℕ) (n : ℕ) :
    finitePrimeDivisorCount P n = (P.filter (fun p => p ∣ n)).card := by
  simp [finitePrimeDivisorCount, sum_boole]

lemma finitePrimeDivisorCount_insert {P : Finset ℕ} {p : ℕ} (hp : p ∉ P) (n : ℕ) :
    finitePrimeDivisorCount (insert p P) n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount P n := by
  simp only [finitePrimeDivisorCount, sum_insert hp]

lemma finitePrimeDivisorCount_pos_of_mem {P : Finset ℕ} {p n : ℕ}
    (hp : p ∈ P) (hpn : p ∣ n) : 0 < finitePrimeDivisorCount P n := by
  rw [finitePrimeDivisorCount_eq_card, card_pos]
  exact ⟨p, mem_filter.mpr ⟨hp, hpn⟩⟩

/-- The correction term distinguishes a new prime from a repeated prime. -/
theorem mrt_prime_divisor_count_mul (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) (m : ℕ) :
    finitePrimeDivisorCount P (p * m) =
      (if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m := by
  have hc (n : ℕ) : finitePrimeDivisorCount P n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount (P.erase p) n := by
    conv_lhs => rw [← insert_erase hp]
    exact finitePrimeDivisorCount_insert (notMem_erase p P) n
  have he : finitePrimeDivisorCount (P.erase p) (p * m) =
      finitePrimeDivisorCount (P.erase p) m := by
    unfold finitePrimeDivisorCount
    apply sum_congr rfl
    intro q hq
    have hq' := mem_erase.mp hq
    have hqprime := hP q hq'.2
    have hqp : ¬q ∣ p := by
      intro hdiv
      exact hq'.1 ((Nat.prime_dvd_prime_iff_eq hqprime (hP p hp)).mp hdiv)
    simp only [hqprime.dvd_mul, hqp, false_or]
  rw [hc (p * m), hc m, he]
  simp only [dvd_mul_right, ite_true, if_true]
  split_ifs <;> omega

lemma mrt_ramare_common_denominator (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    (∑ p ∈ P, if p ∣ n then F n / (finitePrimeDivisorCount P n : ℂ) else 0) =
      if finitePrimeDivisorCount P n = 0 then 0 else F n := by
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, ← finitePrimeDivisorCount_eq_card]
  by_cases hn : finitePrimeDivisorCount P n = 0
  · simp [hn]
  · rw [ite_eq_right hn]
    have hn' : (finitePrimeDivisorCount P n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp

/-- Corrected pointwise factorization, with no squarefree assumption. -/
theorem mrt_ramare_identity (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (n : ℕ) :
    (if finitePrimeDivisorCount P n = 0 then 0 else F n) =
      ∑ p ∈ P, if p ∣ n then
        F (p * (n / p)) /
          (((if p ∣ n / p then 0 else 1) + finitePrimeDivisorCount P (n / p) : ℕ) : ℂ)
        else 0 := by
  rw [← mrt_ramare_common_denominator P F n]
  apply sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · simp only [hpn, ite_true, if_true]
    have he := Nat.mul_div_cancel' hpn
    have hc := mrt_prime_divisor_count_mul P hP hp (n / p)
    rw [he] at hc ⊢
    rw [hc]
  · simp only [hpn, ite_false, if_false]

lemma mrt_inverse_successor_difference {k : ℕ} (hk : 0 < k) :
    ‖(k : ℂ)⁻¹ - ((k + 1 : ℕ) : ℂ)⁻¹‖ ≤ 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1C : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have he : (k : ℂ)⁻¹ - ((k + 1 : ℕ) : ℂ)⁻¹ =
      ((1 / ((k : ℝ) * (k + 1)) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  apply (div_le_one (by positivity)).mpr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- Replacing the corrected denominator by `ω_P(m)+1` costs only the
prime-square terms.  This is the correction explicitly needed in MRT v3. -/
theorem mrt_ramare_denominator_error (P : Finset ℕ) {p m : ℕ}
    (hp : p ∈ P) (z : ℂ) :
    ‖z / (((if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m : ℕ) : ℂ) -
      z / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)‖ ≤
        if p ∣ m then ‖z‖ else 0 := by
  by_cases hpm : p ∣ m
  · simp only [hpm, ite_true, if_true, zero_add]
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, norm_mul]
    have hk := finitePrimeDivisorCount_pos_of_mem hp hpm
    exact (mul_le_mul_of_nonneg_left (mrt_inverse_successor_difference hk)
      (norm_nonneg z)).trans_eq (mul_one _)
  · simp only [hpm, ite_false, if_false, Nat.add_comm 1, sub_self, norm_zero, le_refl]

lemma mrt_count_multiples {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ m ∈ Icc 1 N, if p ∣ m then (1 : ℝ) else 0) = (N / p : ℕ) := by
  have he := divisibility_positivePrefix (fun _ => (1 : ℂ)) p N hp
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, mul_one,
    sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum, apply_ite, Complex.one_re, Complex.zero_re,
    Complex.natCast_re] using hr

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTPrimeSquareMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime-square error in the corrected Ramaré decomposition has a
small mean square.  The count is evaluated by pairing prime-square
divisibility tests; distinct primes give the product modulus exactly. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrtPrimeSquareCount_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ mrtPrimeSquareCount P n := by
  unfold mrtPrimeSquareCount
  exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

lemma mrt_prime_square_joint_count (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (∑ n ∈ Icc 1 N, (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
      (if q ^ 2 ∣ n then (1 : ℝ) else 0)) ≤
      (N : ℝ) * ((if p = q then 1 / (p : ℝ) ^ 2 else 0) +
        (1 / (p : ℝ) ^ 2) * (1 / (q : ℝ) ^ 2)) := by
  by_cases hpq : p = q
  · subst q
    have he (n : ℕ) : (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if p ^ 2 ∣ n then (1 : ℝ) else 0) =
        (if p ^ 2 ∣ n then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    rw [mrt_count_multiples (pow_pos hp.pos 2)]
    simp only [ite_true, if_true]
    calc
      _ ≤ (N : ℝ) / (p ^ 2 : ℕ) := Nat.cast_div_le
      _ = (N : ℝ) * (1 / (p : ℝ) ^ 2) := by push_cast <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (Nat.cast_nonneg N)
  · have hc : Nat.Coprime (p ^ 2) (q ^ 2) := ((Nat.coprime_primes hp hq).mpr hpq).pow 2 2
    have hd (n : ℕ) : p ^ 2 * q ^ 2 ∣ n ↔ p ^ 2 ∣ n ∧ q ^ 2 ∣ n := by
      constructor
      · intro h
        exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩
      · rintro ⟨h1, h2⟩
        exact hc.mul_dvd_of_dvd_of_dvd h1 h2
    have he (n : ℕ) : (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if q ^ 2 ∣ n then (1 : ℝ) else 0) =
        (if p ^ 2 * q ^ 2 ∣ n then (1 : ℝ) else 0) := by
      simp only [hd]
      split_ifs <;> simp_all
    simp_rw [he]
    rw [mrt_count_multiples (Nat.mul_pos (pow_pos hp.pos 2) (pow_pos hq.pos 2)),
      ite_eq_right hpq, zero_add]
    convert (Nat.cast_div_le (m := N) (n := p ^ 2 * q ^ 2) :
      ((N / (p ^ 2 * q ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / (p ^ 2 * q ^ 2 : ℕ)) using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring

/-- No logarithm or cardinality of the prime set occurs in the
divisibility-count second moment. -/
theorem mrt_prime_square_count_second_moment (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (mrtPrimeSquareCount P n) ^ 2) ≤
      (N : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have he (n : ℕ) : (mrtPrimeSquareCount P n) ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if q ^ 2 ∣ n then (1 : ℝ) else 0) := by
    unfold mrtPrimeSquareCount
    rw [pow_two, sum_mul]
    apply sum_congr rfl
    intro p _
    rw [mul_sum]
  simp_rw [he]
  rw [sum_comm (s := Icc 1 N) (t := P)]
  calc
    _ = ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Icc 1 N,
        (if p ^ 2 ∣ n then (1 : ℝ) else 0) *
        (if q ^ 2 ∣ n then (1 : ℝ) else 0) := by
      apply sum_congr rfl
      intro p _
      exact sum_comm
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, (N : ℝ) *
        ((if p = q then 1 / (p : ℝ) ^ 2 else 0) +
          (1 / (p : ℝ) ^ 2) * (1 / (q : ℝ) ^ 2)) := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro q hq
      exact mrt_prime_square_joint_count N p q (hP p hp) (hP q hq)
    _ = _ := by
      simp_rw [← mul_sum]
      congr 1
      simp only [sum_add_distrib]
      congr 1
      · apply sum_congr rfl
        intro p hp
        simp [hp]
      · calc
          _ = ∑ p ∈ P, (1 / (p : ℝ) ^ 2) * (∑ q ∈ P, 1 / (q : ℝ) ^ 2) := by
            apply sum_congr rfl
            intro p _
            exact (mul_sum _ _ _).symm
          _ = _ := by rw [← sum_mul, pow_two]

theorem mrt_prime_square_coefficient_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (2 * N), ‖b n‖ ≤ mrtPrimeSquareCount P n) :
    (∑ n ∈ Ioc N (2 * N), ‖b n / (n : ℂ)‖ ^ 2) ≤
      (2 / (N : ℝ)) * ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ n ∈ Ioc N (2 * N), ((mrtPrimeSquareCount P n) / (N : ℝ)) ^ 2 := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_natCast]
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div₀ (mrtPrimeSquareCount_nonneg P n) (hb n hn) hNr
        (by exact_mod_cast (mem_Ioc.mp hn).1.le)
    _ = (N : ℝ)⁻¹ ^ 2 * ∑ n ∈ Ioc N (2 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      simp_rw [div_eq_mul_inv, mul_pow]
      rw [← sum_mul, mul_comm]
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ∑ n ∈ Icc 1 (2 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      · exact fun _ _ _ => sq_nonneg _
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ((2 * N : ℕ) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_count_second_moment P hP (2 * N))
        (by positivity)
    _ = _ := by
      push_cast
      field_simp

/-- The mean-square cost of any prime-square-supported Ramaré error. -/
theorem mrt_prime_square_dyadic_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (2 * N), ‖b n‖ ≤ mrtPrimeSquareCount P n)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial b N t‖ ^ 2) ≤
      32 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := mrt_dirichlet_mean_square_subset (Ioc N (2 * N)) (N := 2 * N)
    (by intro n hn; exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,
      (mem_Ioc.mp hn).2⟩) (fun n => b n / (n : ℂ)) hT
  apply hm.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (2 * N : ℕ)) * ((2 / (N : ℝ)) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_coefficient_mass P hP b hN hb)
        (by positivity)
    _ = 16 * Real.exp 1 * (T / (N : ℝ) + 2) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
      push_cast
      field_simp <;> ring
    _ ≤ _ := by
      have hc : 0 ≤ (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 := by positivity
      nlinarith [mul_nonneg (Real.exp_pos 1).le hc,
        mul_nonneg (div_nonneg hT.le hNr.le) (mul_nonneg (Real.exp_pos 1).le hc)]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTPrimeProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The factorial multiplicity of a product of primes.  Sorting gives
an injective permutation code on each product fiber, including tuples
with repeated primes.  This is the arithmetic input for high moments
of prime Dirichlet polynomials. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_prime_tuples_perm {r : ℕ} (v w : Fin r → ℕ)
    (hv : ∀ i, (v i).Prime) (hw : ∀ i, (w i).Prime)
    (hprod : (∏ i, v i) = ∏ i, w i) : List.Perm (List.ofFn v) (List.ofFn w) := by
  have hpv := Nat.primeFactorsList_unique (List.prod_ofFn (f := v)) (by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hv i)
  have hpw := Nat.primeFactorsList_unique (List.prod_ofFn (f := w)) (by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hw i)
  rw [hprod] at hpv
  exact hpv.trans hpw.symm

lemma mrt_prime_tuples_sorted_eq {r : ℕ} (v w : Fin r → ℕ)
    (hv : ∀ i, (v i).Prime) (hw : ∀ i, (w i).Prime)
    (hprod : (∏ i, v i) = ∏ i, w i) :
    v ∘ Tuple.sort v = w ∘ Tuple.sort w := by
  have hp := ((Tuple.sort v).ofFn_comp_perm v).trans
    ((mrt_prime_tuples_perm v w hv hw hprod).trans ((Tuple.sort w).ofFn_comp_perm w).symm)
  exact List.ofFn_injective (hp.eq_of_pairwise'
    (Tuple.monotone_sort v).sortedLE_ofFn.pairwise
    (Tuple.monotone_sort w).sortedLE_ofFn.pairwise)

theorem mrt_prime_product_fiber_card {r : ℕ} (S : Finset (Fin r → ℕ))
    (hS : ∀ v ∈ S, ∀ i, (v i).Prime) (n : ℕ) :
    (S.filter (fun v => (∏ i, v i) = n)).card ≤ r.factorial := by
  let T := S.filter (fun v => (∏ i, v i) = n)
  have hcard : T.card ≤ (univ : Finset (Equiv.Perm (Fin r))).card := by
    apply card_le_card_of_injOn Tuple.sort (fun _ _ => mem_univ _)
    intro v hv w hw he
    have hv' := mem_filter.mp hv
    have hw' := mem_filter.mp hw
    have hs := mrt_prime_tuples_sorted_eq v w (hS v hv'.1) (hS w hw'.1)
      (hv'.2.trans hw'.2.symm)
    funext i
    have hi := congrFun hs ((Tuple.sort v).symm i)
    rw [← he] at hi
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi
  simpa only [card_univ, Fintype.card_perm, Fintype.card_fin] using hcard

lemma mrt_norm_sum_sq_le_card {α : Type*} (S : Finset α) (a : α → ℂ) :
    ‖∑ i ∈ S, a i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ S, ‖a i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖a i‖)

/-- Equal products of `r` primes contribute at most the factorial loss
to the square of a grouped Dirichlet coefficient. -/
theorem mrt_prime_product_coefficient_sq {r : ℕ} (S : Finset (Fin r → ℕ))
    (hS : ∀ v ∈ S, ∀ i, (v i).Prime) (a : (Fin r → ℕ) → ℂ) (n : ℕ) :
    ‖∑ v ∈ S.filter (fun v => (∏ i, v i) = n), a v‖ ^ 2 ≤
      (r.factorial : ℝ) * ∑ v ∈ S.filter (fun v => (∏ i, v i) = n), ‖a v‖ ^ 2 := by
  apply (mrt_norm_sum_sq_le_card _ a).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  exact_mod_cast mrt_prime_product_fiber_card S hS n

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTPrimeMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High even moments of a prime Dirichlet polynomial.  Expanding the
power produces ordered prime tuples; unique factorization bounds each
coefficient fiber by the factorial, and the ordinary mean-square theorem
then applies to a polynomial of length `N ^ r`. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped BigOperators Classical

lemma mrt_prime_tuple_range (P : Finset ℕ) (N r : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (v : Fin r → ℕ) (hv : v ∈ Fintype.piFinset fun _ : Fin r => P) :
    (∏ i, v i) ∈ Ioc 0 (N ^ r) := by
  have hm : ∀ i, v i ∈ P := Fintype.mem_piFinset.mp hv
  refine mem_Ioc.mpr ⟨prod_pos fun i _ => (hP _ (hm i)).pos, ?_⟩
  calc
    _ ≤ ∏ _i : Fin r, N := prod_le_prod' fun i _ => hN _ (hm i)
    _ = _ := by simp

theorem mrt_prime_power_coefficient_mass (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N) :
    (∑ n ∈ Ioc 0 (N ^ r), ‖mrtPrimePowerCoefficient P a r n‖ ^ 2) ≤
      (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
  let S := Fintype.piFinset fun _ : Fin r => P
  have hs : ∀ v ∈ S, ∀ i, (v i).Prime := by
    intro v hv i
    exact hP _ (Fintype.mem_piFinset.mp hv i)
  calc
    _ ≤ ∑ n ∈ Ioc 0 (N ^ r), (r.factorial : ℝ) *
        ∑ v ∈ S.filter (fun v => (∏ i, v i) = n), ‖∏ i, a (v i)‖ ^ 2 := by
      apply sum_le_sum
      intro n _
      exact mrt_prime_product_coefficient_sq S hs (fun v => ∏ i, a (v i)) n
    _ = (r.factorial : ℝ) * ∑ v ∈ S, ‖∏ i, a (v i)‖ ^ 2 := by
      rw [← mul_sum]
      congr 1
      exact sum_fiberwise_of_maps_to (fun v hv => mrt_prime_tuple_range P N r hP hN v hv) _
    _ = _ := by
      congr 1
      simp only [norm_prod, ← prod_pow]
      exact (sum_pow' P (fun p => ‖a p‖ ^ 2) r).symm

lemma mrt_prime_tuple_phase {r : ℕ} (v : Fin r → ℕ)
    (hv : ∀ i, 0 < v i) (t : ℝ) :
    (∏ i, Complex.exp (((-Real.log (v i : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((-Real.log ((∏ i, v i : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_sum]
  have hl : Real.log ((∏ i, v i : ℕ) : ℝ) = ∑ i, Real.log (v i : ℝ) := by
    push_cast
    exact Real.log_prod fun i _ => by exact_mod_cast (hv i).ne'
  rw [hl]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [← sum_mul, ← sum_mul, sum_neg_distrib]

theorem mrt_prime_polynomial_power (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N) (t : ℝ) :
    (mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t) ^ r =
      mrtExponentialPolynomial (Ioc 0 (N ^ r)) (mrtPrimePowerCoefficient P a r)
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtExponentialPolynomial
  rw [sum_pow']
  symm
  calc
    _ = ∑ n ∈ Ioc 0 (N ^ r), ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
        (fun v => (∏ i, v i) = n),
          (∏ i, a (v i)) * Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
      apply sum_congr rfl
      intro n _
      exact sum_mul _ _ _
    _ = ∑ v ∈ Fintype.piFinset fun _ : Fin r => P,
        (∏ i, a (v i)) *
          Complex.exp (((-Real.log ((∏ i, v i : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
      calc
        _ = ∑ n ∈ Ioc 0 (N ^ r), ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
            (fun v => (∏ i, v i) = n), (∏ i, a (v i)) *
              Complex.exp (((-Real.log ((∏ i, v i : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
          apply sum_congr rfl
          intro n _
          apply sum_congr rfl
          intro v hv
          rw [(mem_filter.mp hv).2]
        _ = _ := sum_fiberwise_of_maps_to
          (fun v hv => mrt_prime_tuple_range P N r hP hN v hv) _
    _ = _ := by
      apply sum_congr rfl
      intro v hv
      rw [prod_mul_distrib, mrt_prime_tuple_phase v
        (fun i => (hP _ (Fintype.mem_piFinset.mp hv i)).pos) t]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTRestrictedEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite energy bounds on arbitrary measurable frequency classes.
They retain the explicit coarse-bin count and permit the coefficient
bounds to vary from bin to bin. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_continuous_square_integrable {F : ℝ → ℂ} (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    IntegrableOn (fun t => ‖F t‖ ^ 2) E := by
  have hi : IntegrableOn (fun t => ‖F t‖ ^ 2) (Set.Ioc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      ((hF.norm.pow 2).intervalIntegrable _ _)
  exact hi.mono_set hE

lemma mrt_restricted_square_le_interval {F : ℝ → ℂ} (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖F t‖ ^ 2) ≤ ∫ t in -T..T, ‖F t‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact setIntegral_mono_set
    (mrt_continuous_square_integrable hF hT (Set.Subset.refl _))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall hE)

/-- Split a polynomial into a coarse approximation and its actual error
on a frequency class, bounding only the error by its full-interval energy. -/
theorem mrt_restricted_energy_split (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖F t‖ ^ 2) ≤
      2 * (∫ t in -T..T, ‖F t - G t‖ ^ 2) + 2 * (∫ t in E, ‖G t‖ ^ 2) := by
  have hiG := mrt_continuous_square_integrable hG hT hE
  have hiD : IntegrableOn (fun t => ‖F t - G t‖ ^ 2) E :=
    mrt_continuous_square_integrable (hF.sub hG) hT hE
  calc
    _ ≤ ∫ t in E, (2 * ‖F t - G t‖ ^ 2 + 2 * ‖G t‖ ^ 2) := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((hiD.const_mul 2).add (hiG.const_mul 2))
      intro t _
      change ‖F t‖ ^ 2 ≤ 2 * ‖F t - G t‖ ^ 2 + 2 * ‖G t‖ ^ 2
      have ht := norm_add_le (F t - G t) (G t)
      rw [sub_add_cancel] at ht
      nlinarith [sq_nonneg (‖F t - G t‖ - ‖G t‖), norm_nonneg (F t),
        norm_nonneg (F t - G t), norm_nonneg (G t)]
    _ = 2 * (∫ t in E, ‖F t - G t‖ ^ 2) + 2 * (∫ t in E, ‖G t‖ ^ 2) := by
      rw [integral_add (hiD.const_mul 2) (hiG.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (mrt_restricted_square_le_interval (hF.sub hG) hT hE) (by norm_num)) le_rfl

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBoundaryMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two boundary strips created by replacing prime-dependent
cofactor cutoffs with endpoints of a multiplicative prime bin. -/

namespace TwoPointCorrelations

open Finset MeasureTheory

lemma mrt_mem_boundary_iff (N n : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) :
    n ∈ mrtBoundarySet N δ ↔
      (N < n ∧ (n : ℝ) ≤ δ * N) ∨
        (2 * N < n ∧ (n : ℝ) ≤ δ * (2 * N : ℕ)) := by
  have hδ0 : 0 ≤ δ := by linarith
  simp only [mrtBoundarySet, mem_union, mem_Ioc,
    Nat.le_floor_iff (mul_nonneg hδ0 (Nat.cast_nonneg N)),
    Nat.le_floor_iff (mul_nonneg hδ0 (Nat.cast_nonneg (2 * N)))]

lemma mrt_boundary_strip_card (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) :
    ((Ioc N ⌊δ * (N : ℝ)⌋₊).card : ℝ) ≤ (δ - 1) * N := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl : (N : ℝ) ≤ δ * N := by nlinarith
  have hf : N ≤ ⌊δ * (N : ℝ)⌋₊ := Nat.le_floor hl
  rw [Nat.card_Ioc, Nat.cast_sub hf]
  have hu := Nat.floor_le (show 0 ≤ δ * (N : ℝ) by positivity)
  nlinarith

theorem mrt_boundary_card (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) :
    ((mrtBoundarySet N δ).card : ℝ) ≤ 3 * (δ - 1) * N := by
  have hc := card_union_le (Ioc N ⌊δ * (N : ℝ)⌋₊)
    (Ioc (2 * N) ⌊δ * (2 * N : ℕ)⌋₊)
  have hc' : ((mrtBoundarySet N δ).card : ℝ) ≤
      ((Ioc N ⌊δ * (N : ℝ)⌋₊).card : ℝ) +
        ((Ioc (2 * N) ⌊δ * (2 * N : ℕ)⌋₊).card : ℝ) := by
    exact_mod_cast hc
  have h1 := mrt_boundary_strip_card N hδ
  have h2 := mrt_boundary_strip_card (2 * N) hδ
  conv at h2 => rhs; rw [Nat.cast_mul, Nat.cast_ofNat]
  linarith

lemma mrt_boundary_range {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : δ ≤ 2)
    {n : ℕ} (hn : n ∈ mrtBoundarySet N δ) : N < n ∧ n ≤ 4 * N := by
  have hn' := mem_union.mp hn
  have hh : ∀ M : ℕ, ⌊δ * (M : ℝ)⌋₊ ≤ 2 * M := by
    intro M
    apply Nat.floor_le_of_le
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right hδ (show (0 : ℝ) ≤ M from Nat.cast_nonneg M)
  rcases hn' with hn' | hn'
  · have hd := mem_Ioc.mp hn'
    exact ⟨hd.1, (hd.2.trans (hh N)).trans (by omega)⟩
  · have hd := mem_Ioc.mp hn'
    have hu := hd.2.trans (hh (2 * N))
    exact ⟨by omega, by omega⟩

/-- Arbitrary bounded coefficients on the two bin-boundary strips have
mean-square cost proportional to their multiplicative width. -/
theorem mrt_boundary_mean_square (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hb : ∀ n ∈ mrtBoundarySet N δ, ‖b n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial (mrtBoundarySet N δ)
      (fun n => b n / (n : ℂ)) (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      96 * Real.exp 1 * (T / (N : ℝ) + 1) * (δ - 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrange : mrtBoundarySet N δ ⊆ Ioc 0 (4 * N) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mrt_boundary_range hN hδ2 hn
    exact mem_Ioc.mpr ⟨by omega, hn2⟩
  have hcoeff : (∑ n ∈ mrtBoundarySet N δ, ‖b n / (n : ℂ)‖ ^ 2) ≤
      3 * (δ - 1) / (N : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ mrtBoundarySet N δ, (1 / (N : ℝ)) ^ 2 := by
        apply sum_le_sum
        intro n hn
        rw [norm_div, Complex.norm_natCast]
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div₀ (by norm_num) (hb n hn) hNr
          (by exact_mod_cast (mrt_boundary_range hN hδ2 hn).1.le)
      _ = ((mrtBoundarySet N δ).card : ℝ) * (1 / (N : ℝ)) ^ 2 := by simp
      _ ≤ (3 * (δ - 1) * N) * (1 / (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (mrt_boundary_card N hδ) (by positivity)
      _ = _ := by field_simp
  apply (mrt_dirichlet_mean_square_subset (mrtBoundarySet N δ) hrange
    (fun n => b n / (n : ℂ)) hT).trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (4 * N : ℕ)) * (3 * (δ - 1) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = 24 * Real.exp 1 * (T / (N : ℝ) + 4) * (δ - 1) := by
      push_cast
      field_simp <;> ring
    _ ≤ _ := by
      have hd : 0 ≤ Real.exp 1 * (δ - 1) := mul_nonneg (Real.exp_pos _).le (by linarith)
      have ht := mul_nonneg (div_nonneg hT.le hNr.le) hd
      nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTRamareWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive coefficient weights in the uncorrected Ramaré polynomial.
They have total mass at most one, even at integers divisible by prime
squares.  This is the contraction needed for logarithmic-bin cutoffs. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrtRamareWeight_nonneg (P : Finset ℕ) (n p : ℕ) :
    0 ≤ mrtRamareWeight P n p := by
  unfold mrtRamareWeight
  split_ifs <;> positivity

lemma mrt_ramare_weight_le_count (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p n : ℕ} (hp : p ∈ P) (hpn : p ∣ n) :
    mrtRamareWeight P n p ≤ 1 / (finitePrimeDivisorCount P n : ℝ) := by
  have hcount := mrt_prime_divisor_count_mul P hP hp (n / p)
  rw [Nat.mul_div_cancel' hpn] at hcount
  have hc : finitePrimeDivisorCount P n ≤ finitePrimeDivisorCount P (n / p) + 1 := by
    rw [hcount]
    split_ifs <;> omega
  have hpos : (0 : ℝ) < finitePrimeDivisorCount P n := by
    exact_mod_cast finitePrimeDivisorCount_pos_of_mem hp hpn
  rw [mrtRamareWeight, ite_eq_left hpn]
  exact one_div_le_one_div_of_le hpos (by exact_mod_cast hc)

theorem mrt_ramare_weight_sum_le_one (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∑ p ∈ P, mrtRamareWeight P n p) ≤ 1 := by
  by_cases hc : finitePrimeDivisorCount P n = 0
  · have hz : ∀ p ∈ P, ¬p ∣ n := by
      intro p hp hpn
      have := finitePrimeDivisorCount_pos_of_mem hp hpn
      omega
    have hs : (∑ p ∈ P, mrtRamareWeight P n p) = 0 := by
      apply sum_eq_zero
      intro p hp
      simp only [mrtRamareWeight, ite_eq_right (hz p hp)]
    rw [hs]
    norm_num
  · calc
      _ ≤ ∑ p ∈ P, if p ∣ n then 1 / (finitePrimeDivisorCount P n : ℝ) else 0 := by
        apply sum_le_sum
        intro p hp
        by_cases hpn : p ∣ n
        · rw [ite_eq_left hpn]
          exact mrt_ramare_weight_le_count P hP hp hpn
        · simp only [mrtRamareWeight, ite_eq_right hpn, le_refl]
      _ = 1 := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, ← finitePrimeDivisorCount_eq_card]
        exact mul_one_div_cancel (by exact_mod_cast hc)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCoarseBins
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse cofactor windows for a multiplicative prime bin.  The weights
are the actual Ramaré weights, and moving all primes in a bin to its
lower endpoint changes coefficients only in two short boundary strips. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrtCoarseRamareWeight_nonneg (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ) :
    0 ≤ mrtCoarseRamareWeight P L N n := by
  apply sum_nonneg
  intro p _
  exact mul_nonneg (mrtRamareWeight_nonneg P n p) (by split_ifs <;> norm_num)

lemma mrt_coarse_weight_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (L : ℕ → ℝ) (N n : ℕ) : mrtCoarseRamareWeight P L N n ≤ 1 := by
  apply le_trans _ (mrt_ramare_weight_sum_le_one P hP n)
  apply sum_le_sum
  intro p _
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]
    exact mrtRamareWeight_nonneg P n p

lemma mrt_coarse_window_support {X δ a p m n : ℝ} (hδ : 1 ≤ δ)
    (hm : 0 ≤ m) (hl : a ≤ p) (hu : p ≤ δ * a) (hn : p * m = n)
    (hwindow : X < a * m ∧ a * m ≤ 2 * X) :
    X < n ∧ n ≤ 2 * δ * X := by
  have h1 := mul_le_mul_of_nonneg_right hl hm
  have h2 := mul_le_mul_of_nonneg_right hu hm
  have h3 := mul_le_mul_of_nonneg_left hwindow.2 (show 0 ≤ δ by linarith)
  constructor <;> nlinarith

lemma mrt_coarse_window_interior {X δ a p m n : ℝ} (hδ : 1 ≤ δ)
    (hm : 0 ≤ m) (hl : a ≤ p) (hu : p ≤ δ * a) (hn : p * m = n)
    (hinterior : δ * X < n ∧ n ≤ 2 * X) :
    X < a * m ∧ a * m ≤ 2 * X := by
  have h1 := mul_le_mul_of_nonneg_right hl hm
  have h2 := mul_le_mul_of_nonneg_right hu hm
  have hd : 0 < δ := by linarith
  constructor
  · apply (mul_lt_mul_iff_right₀ hd).mp
    nlinarith
  · linarith

lemma mrt_coarse_weight_zero (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hn : ¬((N : ℝ) < n ∧ (n : ℝ) ≤ 2 * δ * N)) :
    mrtCoarseRamareWeight P L N n = 0 := by
  apply sum_eq_zero
  intro p hp
  by_cases hpn : p ∣ n
  · have hmul : (p : ℝ) * (n / p : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hpn
    have hw : ¬((N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N) := by
      intro h
      exact hn (mrt_coarse_window_support hδ (Nat.cast_nonneg _) (hL p hp).1
        (hL p hp).2 hmul h)
    rw [ite_eq_right hw, mul_zero]
  · simp only [mrtRamareWeight, ite_eq_right hpn, zero_mul]

lemma mrt_coarse_weight_interior (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hn : δ * N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N) :
    mrtCoarseRamareWeight P L N n = ∑ p ∈ P, mrtRamareWeight P n p := by
  apply sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · have hmul : (p : ℝ) * (n / p : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hpn
    have hw := mrt_coarse_window_interior hδ (Nat.cast_nonneg _) (hL p hp).1
      (hL p hp).2 hmul hn
    rw [ite_eq_left hw, mul_one]
  · simp only [mrtRamareWeight, ite_eq_right hpn, zero_mul]

lemma mrt_coarse_boundary_abs (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (L : ℕ → ℝ) (N n : ℕ) : |mrtCoarseBoundaryCoefficient P L N n| ≤ 1 := by
  have hc0 := mrtCoarseRamareWeight_nonneg P L N n
  have hc1 := mrt_coarse_weight_le_one P hP L N n
  have hr0 : 0 ≤ ∑ p ∈ P, mrtRamareWeight P n p :=
    sum_nonneg fun p _ => mrtRamareWeight_nonneg P n p
  have hr1 := mrt_ramare_weight_sum_le_one P hP n
  unfold mrtCoarseBoundaryCoefficient
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

theorem mrt_coarse_boundary_support (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hn : n ∉ mrtBoundarySet N δ) : mrtCoarseBoundaryCoefficient P L N n = 0 := by
  have hnot := mt (mrt_mem_boundary_iff N n hδ).mpr hn
  unfold mrtCoarseBoundaryCoefficient
  by_cases hwindow : N < n ∧ n ≤ 2 * N
  · have hi : δ * N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
      constructor
      · by_contra h
        exact hnot (Or.inl ⟨hwindow.1, le_of_not_gt h⟩)
      · exact_mod_cast hwindow.2
    rw [ite_eq_left hwindow, mrt_coarse_weight_interior P L N n hδ hL hi, sub_self]
  · have ho : ¬((N : ℝ) < n ∧ (n : ℝ) ≤ 2 * δ * N) := by
      rintro ⟨hnN, hnU⟩
      have hnN' : N < n := by exact_mod_cast hnN
      have hn2 : 2 * N < n := by omega
      apply hnot
      right
      refine ⟨hn2, ?_⟩
      convert hnU using 1
      all_goals try with_reducible_and_instances rfl
      push_cast
      ring
    rw [ite_eq_right hwindow, mrt_coarse_weight_zero P L N n hδ hL ho, sub_self]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTRamareMeanError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coefficient error made by replacing the corrected Ramaré
denominator with `ω_P(m)+1`.  The pointwise error is supported on prime
squares, so the preceding second-moment count applies directly. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_ramare_correction_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (n : ℕ) :
    ‖mrtRamareCorrection P F n‖ ≤ ‖F n‖ * mrtPrimeSquareCount P n := by
  unfold mrtRamareCorrection
  rw [mrt_ramare_identity P hP F n, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, if p ^ 2 ∣ n then ‖F n‖ else 0 := by
      apply sum_le_sum
      intro p hp
      by_cases hpn : p ∣ n
      · simp only [hpn, ite_true, if_true, Nat.mul_div_cancel' hpn]
        have he : p ∣ n / p ↔ p ^ 2 ∣ n := by
          simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hpn : p ∣ n / p ↔ p * p ∣ n)
        simpa only [he] using mrt_ramare_denominator_error P hp (F n) (m := n / p)
      · have hs : ¬p ^ 2 ∣ n := by
          intro hn
          apply hpn
          exact dvd_trans (by simpa only [pow_two] using (dvd_mul_right p p)) hn
        simp only [hpn, hs, ite_false, if_false, sub_self, norm_zero, le_refl]
    _ = _ := by
      unfold mrtPrimeSquareCount
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      split_ifs <;> simp

theorem mrt_ramare_correction_oneBounded (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (hF : OneBounded F)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtRamareCorrection P F n‖ ≤ mrtPrimeSquareCount P n := by
  apply (mrt_ramare_correction_bound P hP F n).trans
  exact (mul_le_mul_of_nonneg_right (hF n hn) (mrtPrimeSquareCount_nonneg P n)).trans_eq
    (one_mul _)

/-- The literal denominator correction costs only the reciprocal square
mass in the normalized dyadic mean square.  Multiplicativity is not
needed for this error estimate. -/
theorem mrt_ramare_correction_mean_square (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtRamareCorrection P F) N t‖ ^ 2) ≤
      32 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  apply mrt_prime_square_dyadic_mean P hP _ hN _ hT
  intro n hn
  exact mrt_ramare_correction_oneBounded P hP F hF (hN.trans (mem_Ioc.mp hn).1)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCoarseMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal coarse-bin polynomial differs from the supported dyadic
polynomial by the prime-square correction and the two short boundary
strips.  Both errors are estimated before any sum over prime bins. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_dyadic_polynomial_extend (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    mrtDyadicPolynomial b N t =
      mrtExponentialPolynomial (Ioc 0 (4 * N))
        (fun n => (if N < n ∧ n ≤ 2 * N then b n else 0) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  calc
    _ = ∑ n ∈ Ioc N (2 * N),
        ((if N < n ∧ n ≤ 2 * N then b n else 0) / (n : ℂ)) *
          Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
      apply sum_congr rfl
      intro n hn
      rw [ite_eq_left (mem_Ioc.mp hn)]
    _ = _ := by
      apply sum_subset
      · intro n hn
        have hn' := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨by omega, by omega⟩
      · intro n _ hn
        simp only [mem_Ioc] at hn
        rw [ite_eq_right hn, zero_div, zero_mul]

/-- Exact boundary identity, with the original and coarse polynomials
both retaining their actual numerical coefficients. -/
theorem mrt_coarse_boundary_identity (P : Finset ℕ) (L : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ) (t : ℝ) :
    mrtDyadicPolynomial (mrtWeightedRamareCoefficient P F) N t -
        mrtCoarsePolynomial P L N F t =
      mrtCoarseBoundaryPolynomial P L N δ F t := by
  rw [mrt_dyadic_polynomial_extend]
  unfold mrtCoarsePolynomial mrtCoarseBoundaryPolynomial mrtExponentialPolynomial
  rw [← sum_sub_distrib]
  calc
    _ = ∑ n ∈ Ioc 0 (4 * N),
        (F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ) / (n : ℂ)) *
          Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
      apply sum_congr rfl
      intro n _
      unfold mrtWeightedRamareCoefficient mrtCoarseBoundaryCoefficient
      by_cases hn : N < n ∧ n ≤ 2 * N
      · simp only [ite_eq_left hn, Complex.ofReal_sub]
        ring
      · simp only [ite_eq_right hn, Complex.ofReal_sub, Complex.ofReal_zero]
        ring
    _ = _ := by
      symm
      apply sum_subset
      · intro n hn
        obtain ⟨hn1, hn2⟩ := mrt_boundary_range hN hδ2 hn
        exact mem_Ioc.mpr ⟨by omega, hn2⟩
      · intro n _ hn
        dsimp only
        rw [mrt_coarse_boundary_support P L N n hδ hL hn,
          Complex.ofReal_zero, mul_zero, zero_div, zero_mul]

lemma mrt_coarse_boundary_coefficient_norm (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) (N : ℕ)
    (F : ℕ → ℂ) (hF : OneBounded F) {n : ℕ} (hn : 0 < n) :
    ‖F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (hF n hn) (mrt_coarse_boundary_abs P hP L N n)
    (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem mrt_coarse_boundary_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (F : ℕ → ℂ) (hF : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtCoarseBoundaryPolynomial P L N δ F t‖ ^ 2) ≤
      96 * Real.exp 1 * (T / (N : ℝ) + 1) * (δ - 1) := by
  apply mrt_boundary_mean_square
    (fun n => F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ)) hN hδ hδ2 _ hT
  intro n hn
  exact mrt_coarse_boundary_coefficient_norm P hP L N F hF
    (hN.trans (mrt_boundary_range hN hδ2 hn).1)

lemma mrt_weighted_ramare_sum (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    (∑ p ∈ P, if p ∣ n then
      F n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) =
      mrtWeightedRamareCoefficient P F n := by
  unfold mrtWeightedRamareCoefficient
  rw [Complex.ofReal_sum, mul_sum]
  apply sum_congr rfl
  intro p _
  unfold mrtRamareWeight
  by_cases hp : p ∣ n
  · simp only [hp, ite_true, if_true, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast]
    ring
  · simp only [hp, ite_false, if_false, Complex.ofReal_zero, mul_zero]

lemma mrt_supported_ramare_split (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    mrtSupportedCoefficient P F n =
      mrtRamareCorrection P F n + mrtWeightedRamareCoefficient P F n := by
  unfold mrtSupportedCoefficient mrtRamareCorrection
  rw [mrt_weighted_ramare_sum]
  ring

lemma mrt_dyadic_polynomial_add (a b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    mrtDyadicPolynomial (fun n => a n + b n) N t =
      mrtDyadicPolynomial a N t + mrtDyadicPolynomial b N t := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  simp only [add_div, add_mul, sum_add_distrib]

theorem mrt_coarse_error_identity (P : Finset ℕ) (L : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ) (t : ℝ) :
    mrtDyadicPolynomial (mrtSupportedCoefficient P F) N t -
        mrtCoarsePolynomial P L N F t =
      mrtDyadicPolynomial (mrtRamareCorrection P F) N t +
        mrtCoarseBoundaryPolynomial P L N δ F t := by
  have hs : mrtSupportedCoefficient P F =
      fun n => mrtRamareCorrection P F n + mrtWeightedRamareCoefficient P F n :=
    funext (mrt_supported_ramare_split P F)
  rw [hs, mrt_dyadic_polynomial_add]
  rw [← mrt_coarse_boundary_identity P L hN hδ hδ2 hL F t]
  ring

/-- Coarse-bin decoupling costs the reciprocal square mass and the bin
width.  There is no loss depending on the number of bins. -/
theorem mrt_coarse_error_mean_square (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ) (hF : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtSupportedCoefficient P F) N t -
      mrtCoarsePolynomial P L N F t‖ ^ 2) ≤
      192 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
  let A := mrtDyadicPolynomial (mrtRamareCorrection P F) N
  let B := mrtCoarseBoundaryPolynomial P L N δ F
  have hA : Continuous A := mrtExponentialPolynomial_continuous _ _ _
  have hB : Continuous B := mrtExponentialPolynomial_continuous _ _ _
  have ha : IntervalIntegrable (fun t => ‖A t‖ ^ 2) volume (-T) T :=
    (hA.norm.pow 2).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun t => ‖B t‖ ^ 2) volume (-T) T :=
    (hB.norm.pow 2).intervalIntegrable _ _
  have hab : IntervalIntegrable (fun t => ‖A t + B t‖ ^ 2) volume (-T) T :=
    ((hA.add hB).norm.pow 2).intervalIntegrable _ _
  have hmajor : (∫ t in -T..T, ‖A t + B t‖ ^ 2) ≤
      2 * (∫ t in -T..T, ‖A t‖ ^ 2) + 2 * (∫ t in -T..T, ‖B t‖ ^ 2) := by
    calc
      _ ≤ ∫ t in -T..T, (2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on (by linarith : -T ≤ T) hab
          ((ha.const_mul 2).add (hb.const_mul 2))
        intro t _
        have hh := norm_add_le (A t) (B t)
        nlinarith [sq_nonneg (‖A t‖ - ‖B t‖), norm_nonneg (A t + B t),
          norm_nonneg (A t), norm_nonneg (B t)]
      _ = _ := by
        rw [intervalIntegral.integral_add (ha.const_mul 2) (hb.const_mul 2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [mrt_coarse_error_identity P L hN hδ hδ2 hL F]
  change (∫ t in -T..T, ‖A t + B t‖ ^ 2) ≤ _
  apply hmajor.trans
  have hma := mrt_ramare_correction_mean_square P hP F hF hN hT
  have hmb := mrt_coarse_boundary_mean P hP L hN hδ hδ2 F hF hT
  change (∫ t in -T..T, ‖A t‖ ^ 2) ≤ _ at hma
  change (∫ t in -T..T, ‖B t‖ ^ 2) ≤ _ at hmb
  have hc : 0 ≤ Real.exp 1 * (T / (N : ℝ) + 1) := by positivity
  have hs : 0 ≤ (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
      (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 := by positivity
  nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCoarseFactorization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact factorization of the coarse Ramaré polynomial into short prime
polynomials and cofactor polynomials with fixed multiplicative windows. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_dirichlet_atom_mul_of_product (F A B : ℕ → ℂ)
    {p m : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hF : F (p * m) = A p * B m) (t : ℝ) :
    mrtDirichletAtom F (p * m) t =
      mrtDirichletAtom A p t * mrtDirichletAtom B m t := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : Complex.exp (((-Real.log ((p * m : ℕ) : ℝ)) * t : ℝ) * Complex.I) =
      Complex.exp (((-Real.log (p : ℝ)) * t : ℝ) * Complex.I) *
        Complex.exp (((-Real.log (m : ℝ)) * t : ℝ) * Complex.I) := by
    rw [Nat.cast_mul, Real.log_mul hpR.ne' hmR.ne', neg_add, add_mul,
      Complex.ofReal_add, add_mul, Complex.exp_add]
  unfold mrtDirichletAtom
  rw [hF, Nat.cast_mul, he]
  ring

lemma mrt_coarse_polynomial_prime_sum (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (F : ℕ → ℂ) (t : ℝ) :
    mrtCoarsePolynomial P L N F t =
      ∑ p ∈ P, ∑ n ∈ Icc 1 (4 * N),
        if p ∣ n then
          if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
            mrtDirichletAtom F n t /
              ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
          else 0
        else 0 := by
  unfold mrtCoarsePolynomial mrtExponentialPolynomial mrtCoarseRamareWeight
  simp only [Complex.ofReal_sum, mul_sum, sum_div, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [show Ioc 0 (4 * N) = Icc 1 (4 * N) by ext n; simp only [mem_Ioc, mem_Icc]; omega]
  apply sum_congr rfl
  intro n _
  unfold mrtRamareWeight mrtDirichletAtom
  by_cases hp : p ∣ n
  · by_cases hw : (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N
    · simp only [ite_eq_left hp, ite_eq_left hw, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
      ring
    · simp only [ite_eq_left hp, ite_eq_right hw, mul_zero, Complex.ofReal_zero,
        zero_mul, zero_div]
  · simp only [ite_eq_right hp, zero_mul, Complex.ofReal_zero, mul_zero, zero_div]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTTypicalFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

/-- Dividing out a number smaller than all the selected primes does not
change membership in the typical-factorization set. -/
theorem mrtTypical_mul_of_avoids {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime) {d : ℕ}
    (hd : mrtPrimeAvoids (J.biUnion P) d) (n : ℕ) :
    mrtTypical J P (d * n) ↔ mrtTypical J P n := by
  constructor
  · intro h j hj
    obtain ⟨p, hp, hpdn⟩ := h j hj
    refine ⟨p, hp, ?_⟩
    exact ((hP j hj p hp).dvd_mul.mp hpdn).resolve_left
      (hd p (mem_biUnion.mpr ⟨j, hj, hp⟩))
  · intro h j hj
    obtain ⟨p, hp, hpn⟩ := h j hj
    exact ⟨p, hp, dvd_mul_of_dvd_right hpn d⟩

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MertensScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The bounded-error estimate controls the reciprocal-prime mass
at the rough-sieve scale. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma sievePrimesUpTo_prime (y : ℝ) (p : ℕ) (hp : p ∈ sievePrimesUpTo y) :
    Nat.Prime p := (mem_filter.mp hp).2

lemma sievePrimesUpTo_le (y : ℝ) (hy : 0 ≤ y) (p : ℕ)
    (hp : p ∈ sievePrimesUpTo y) : (p : ℝ) ≤ y := by
  exact (Nat.le_floor_iff hy).mp (mem_Iic.mp (mem_filter.mp hp).1)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTPrimeBands
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The only classical input here is the already discharged Mertens theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrtPrimeBand_prime {P Q : ℝ} {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : p.Prime :=
  sievePrimesUpTo_prime Q p (mem_sdiff.mp hp).1

lemma mrtPrimeBand_bounds {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : P < p ∧ (p : ℝ) ≤ Q := by
  have hpQ := (mem_sdiff.mp hp).1
  have hpP := (mem_sdiff.mp hp).2
  refine ⟨?_, sievePrimesUpTo_le Q hQ p hpQ⟩
  by_contra hnot
  have hple : (p : ℝ) ≤ P := le_of_not_gt hnot
  exact hpP (mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hP).mpr hple),
    mrtPrimeBand_prime hp⟩)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMultiplicativeReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := ite_eq_right hn.ne'

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTTypicalRamare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramaré factorization on the actual typical-factorization set.  Removing
one selected prime band leaves exactly the remaining-band condition; the
prime-square correction and its bound are retained. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

lemma mrtTypical_count_pos {ι : Type*} {J : Finset ι} {P : ι → Finset ℕ}
    {j : ι} (hj : j ∈ J) {n : ℕ} (hn : mrtTypical J P n) :
    0 < finitePrimeDivisorCount (P j) n := by
  obtain ⟨p, hp, hpn⟩ := hn j hj
  exact finitePrimeDivisorCount_pos_of_mem hp hpn

lemma mrtTypical_prime_mul {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    {p : ℕ} (hp : p ∈ P j) (m : ℕ) :
    mrtTypical J P (p * m) ↔ mrtTypical (J.erase j) P m := by
  have hnot (i : ι) (hi : i ∈ J.erase j) : p ∉ P i := by
    intro hpi
    exact Finset.disjoint_left.mp (hdis (mem_erase.mp hi).2 hj (mem_erase.mp hi).1)
      hpi hp
  have hd : mrtPrimeAvoids ((J.erase j).biUnion P) p := by
    intro q hq hqp
    obtain ⟨i, hi, hqi⟩ := mem_biUnion.mp hq
    have he : q = p := (Nat.prime_dvd_prime_iff_eq
      (hP i (mem_erase.mp hi).2 q hqi) (hP j hj p hp)).mp hqp
    exact hnot i hi (he ▸ hqi)
  have hmul := mrtTypical_mul_of_avoids (J.erase j) P
    (fun i hi => hP i (mem_erase.mp hi).2) hd m
  constructor
  · intro h
    apply hmul.mp
    exact fun i hi => h i (mem_erase.mp hi).2
  · intro h i hi
    by_cases hij : i = j
    · subst i
      exact ⟨p, hp, dvd_mul_right p m⟩
    · exact hmul.mpr h i (mem_erase.mpr ⟨hij, hi⟩)

lemma mrtTypical_ramare_supported {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    {j : ι} (hj : j ∈ J) (F : ℕ → ℂ) (n : ℕ) :
    (if finitePrimeDivisorCount (P j) n = 0 then 0 else
      if mrtTypical J P n then F n else 0) =
      if mrtTypical J P n then F n else 0 := by
  by_cases ht : mrtTypical J P n
  · have hpos := mrtTypical_count_pos hj ht
    simp only [ht, ite_true, if_true, ne_of_gt hpos, ite_false, if_false]
  · simp only [ht, ite_false, if_false, ite_self]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTTypicalCoarse
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse Ramaré factorization on the actual typical-factorization set.
Removing a prime from the selected band leaves precisely the other-band
mask; the square and endpoint errors retain their uniform finite bounds. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrtTypicalCoefficient_oneBounded {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) :
    OneBounded (mrtTypicalCoefficient J P F) := by
  intro n hn
  unfold mrtTypicalCoefficient
  split_ifs
  · exact hF n hn
  · simp

lemma mrtTypicalCoefficient_supported {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) {j : ι} (hj : j ∈ J) (F : ℕ → ℂ) :
    mrtSupportedCoefficient (P j) (mrtTypicalCoefficient J P F) =
      mrtTypicalCoefficient J P F := by
  funext n
  exact mrtTypical_ramare_supported J P hj F n

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFrequencyPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-small-band frequency partition. Every later class supplies
an actual large polynomial in the preceding band; the exceptional set is
exactly the set on which every band has a large polynomial. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_no_small_band_large_witness {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) {J j : ℕ} (hj : j < J)
    {t : ℝ} (ht : t ∈ mrtNoSmallBand K Q A J) :
    ∃ k ∈ K j, A j k < ‖Q j k t‖ := by
  have hn : t ∉ mrtSmallFrequencyBand K Q A j := by
    intro hsmall
    exact ht (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨mem_range.mpr hj, hsmall⟩⟩)
  simp only [mrtSmallFrequencyBand, Set.mem_ofPred_eq, not_forall, not_le, exists_prop] at hn
  exact hn

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeneralPrimeError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general-multiplicative discrepancy in extracting a prime factor.
It vanishes unless that prime divides the cofactor, and hence has the
same prime-square support as the corrected Ramaré denominator error. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrtTypicalCoefficient_prime_mul_coprime {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (hF : Multiplicative F)
    {p : ℕ} (hp : p ∈ P j) {m : ℕ} (hm : 0 < m) (hpm : ¬p ∣ m) :
    mrtTypicalCoefficient J P F (p * m) =
      F p * mrtTypicalCoefficient (J.erase j) P F m := by
  unfold mrtTypicalCoefficient
  rw [mrtTypical_prime_mul J P hP hdis hj hp]
  split_ifs
  · exact hF p m (hP j hj p hp).pos hm ((hP j hj p hp).coprime_iff_not_dvd.mpr hpm)
  · simp

theorem mrt_prime_product_error_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (active : ℕ → ℕ → Prop) (C A B : ℕ → ℂ)
    (hC : OneBounded C) (hA : OneBounded A) (hB : OneBounded B)
    (hproduct : ∀ p ∈ P, ∀ m, 0 < m → ¬p ∣ m → C (p * m) = A p * B m)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtPrimeProductError P active C A B n‖ ≤ 2 * mrtPrimeSquareCount P n := by
  unfold mrtPrimeProductError
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, if p ^ 2 ∣ n then (2 : ℝ) else 0 := by
      apply sum_le_sum
      intro p hp
      by_cases hgate : p ∣ n ∧ active p n
      · rw [ite_eq_left hgate]
        have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hgate.1) (hP p hp).pos
        by_cases hsquare : p ^ 2 ∣ n
        · rw [ite_eq_left hsquare, norm_div, Complex.norm_natCast]
          have hc : ‖C n - A p * B (n / p)‖ ≤ 2 := by
            apply (norm_sub_le _ _).trans
            rw [norm_mul]
            have hab := mul_le_mul (hA p (hP p hp).pos) (hB (n / p) hm)
              (norm_nonneg _) zero_le_one
            nlinarith [hC n hn]
          calc
            _ ≤ 2 / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hc (by positivity)
            _ ≤ 2 := div_le_self (by norm_num) (by norm_num)
        · have hnot : ¬p ∣ n / p := by
            intro hd
            apply hsquare
            simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hgate.1).mp hd
          have he : C n = A p * B (n / p) := by
            calc
              C n = C (p * (n / p)) := congrArg C (Nat.mul_div_cancel' hgate.1).symm
              _ = _ := hproduct p hp (n / p) hm hnot
          rw [he, sub_self, zero_div, norm_zero, ite_eq_right hsquare]
      · rw [ite_eq_right hgate, norm_zero]
        split_ifs <;> norm_num
    _ = _ := by
      unfold mrtPrimeSquareCount
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      split_ifs <;> norm_num

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeneralPrimeMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mean-square control of the general multiplicative prime-extraction
error. The broad coarse window is handled before any sum over bins. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_prime_square_broad_coefficient_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (4 * N), ‖b n‖ ≤ 2 * mrtPrimeSquareCount P n) :
    (∑ n ∈ Ioc N (4 * N), ‖b n / (n : ℂ)‖ ^ 2) ≤
      (16 / (N : ℝ)) * ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ n ∈ Ioc N (4 * N), ((2 * mrtPrimeSquareCount P n) / (N : ℝ)) ^ 2 := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_natCast]
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div₀ (mul_nonneg (by norm_num) (mrtPrimeSquareCount_nonneg P n))
        (hb n hn) hNr
        (by exact_mod_cast (mem_Ioc.mp hn).1.le)
    _ = (4 * (N : ℝ)⁻¹ ^ 2) * ∑ n ∈ Ioc N (4 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      have he (n : ℕ) : ((2 * mrtPrimeSquareCount P n) / (N : ℝ)) ^ 2 =
          (4 * (N : ℝ)⁻¹ ^ 2) * (mrtPrimeSquareCount P n) ^ 2 := by ring
      simp_rw [he]
      rw [← mul_sum]
    _ ≤ (4 * (N : ℝ)⁻¹ ^ 2) * ∑ n ∈ Icc 1 (4 * N), (mrtPrimeSquareCount P n) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      · exact fun _ _ _ => sq_nonneg _
    _ ≤ (4 * (N : ℝ)⁻¹ ^ 2) * ((4 * N : ℕ) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_count_second_moment P hP (4 * N))
        (by positivity)
    _ = _ := by
      push_cast
      field_simp
      ring

/-- A prime-extraction error of size twice the square-divisor count has
an absolute mean-square cost on the complete coarse window. -/
theorem mrt_prime_square_broad_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Ioc N (4 * N), ‖b n‖ ≤ 2 * mrtPrimeSquareCount P n)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial (Ioc N (4 * N))
      (fun n => b n / (n : ℂ)) (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      512 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := mrt_dirichlet_mean_square_subset (Ioc N (4 * N)) (N := 4 * N)
    (by intro n hn; exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,
      (mem_Ioc.mp hn).2⟩) (fun n => b n / (n : ℂ)) hT
  apply hm.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (4 * N : ℕ)) * ((16 / (N : ℝ)) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mrt_prime_square_broad_coefficient_mass P hP b hN hb)
        (by positivity)
    _ = 128 * Real.exp 1 * (T / (N : ℝ) + 4) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
      push_cast
      field_simp
      ring
    _ ≤ _ := by
      have hc : 0 ≤ (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 := by positivity
      nlinarith [mul_nonneg (Real.exp_pos 1).le hc,
        mul_nonneg (div_nonneg hT.le hNr.le) (mul_nonneg (Real.exp_pos 1).le hc)]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeneralFactorization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coarse prime extraction with its prime-square discrepancy.
Only coprime multiplicativity is needed when the discrepancy is bounded. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_prime_cofactor_expansion (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hδ2 : δ ≤ 2) {p : ℕ} (hp : p ∈ P) (hp0 : 0 < p)
    (A B : ℕ → ℂ) (t : ℝ) :
    mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t =
      ∑ n ∈ Icc 1 (4 * N), if p ∣ n then
        if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
          ((A p * B (n / p)) / (n : ℂ) *
            Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I)) /
              ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
        else 0
      else 0 := by
  let F : ℕ → ℂ := fun n => A p * B (n / p)
  let G : ℕ → ℂ := fun n =>
    if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
      mrtDirichletAtom F n t / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
    else 0
  have he := divisibility_positivePrefix G p (4 * N) hp0
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, ite_mul, one_mul, zero_mul] at he
  change _ = ∑ n ∈ Icc 1 (4 * N), if p ∣ n then G n else 0
  rw [he]
  have hrange : Icc 1 (4 * N / p) ⊆ Icc 1 (4 * N) := by
    intro m hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1,
      (mem_Icc.mp hm).2.trans (Nat.div_le_self _ _)⟩
  have hf (m : ℕ) : F (p * m) = A p * B m := by
    dsimp [F]
    rw [Nat.mul_div_cancel_left m hp0]
  have hexpand : (∑ m ∈ Icc 1 (4 * N / p), G (p * m)) =
      ∑ m ∈ Icc 1 (4 * N), G (p * m) := by
    apply sum_subset hrange
    intro m hm hout
    dsimp only [G]
    rw [Nat.mul_div_cancel_left m hp0]
    apply ite_eq_right
    intro hw
    have hpm := (mrt_coarse_window_support hδ (show (0 : ℝ) ≤ m by positivity)
      (hL p hp).1 (hL p hp).2 rfl hw).2
    have hmul : (p : ℝ) * m ≤ (4 * N : ℕ) := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      push_cast
      nlinarith
    have hnat : p * m ≤ 4 * N := by exact_mod_cast hmul
    exact hout (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,
      (Nat.le_div_iff_mul_le hp0).mpr (by simpa only [Nat.mul_comm] using hnat)⟩)
  rw [hexpand]
  unfold mrtCofactorPolynomial
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  dsimp only [G]
  rw [Nat.mul_div_cancel_left m hp0]
  by_cases hw : (N : ℝ) < L p * m ∧ L p * m ≤ 2 * N
  · rw [ite_eq_left hw, ite_eq_left hw,
      mrt_dirichlet_atom_mul_of_product F A B hp0 (mem_Icc.mp hm).1 (hf m)]
    ring
  · simp only [ite_eq_right hw, mul_zero]

lemma mrt_prime_extraction_error_zero (P : Finset ℕ) (L : ℕ → ℝ)
    (hL : ∀ p ∈ P, L p ≤ p) (N : ℕ) (C A B : ℕ → ℂ)
    {n : ℕ} (hn : n ≤ N) : mrtPrimeExtractionError P L N C A B n = 0 := by
  unfold mrtPrimeExtractionError mrtPrimeProductError
  apply sum_eq_zero
  intro p hp
  apply ite_eq_right
  rintro ⟨hd, hlo, _⟩
  have hprod : L p * (n / p : ℕ) ≤ (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (hL p hp) (show (0 : ℝ) ≤ (n / p : ℕ) by positivity)
    simpa only [← Nat.cast_mul, Nat.mul_div_cancel' hd] using hh
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  linarith

/-- The exact polynomial identity precedes all norm estimates and keeps
one discrepancy coefficient per integer, rather than per prime bin. -/
theorem mrt_general_prime_factorization (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) (N : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (C A B : ℕ → ℂ) (t : ℝ) :
    mrtCoarsePolynomial P L N C t -
      (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t) =
      mrtExponentialPolynomial (Ioc N (4 * N))
        (fun n => mrtPrimeExtractionError P L N C A B n / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  have hex : (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t) =
      ∑ p ∈ P, ∑ n ∈ Icc 1 (4 * N), if p ∣ n then
        if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
          ((A p * B (n / p)) / (n : ℂ) *
            Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I)) /
              ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
        else 0
      else 0 := by
    apply sum_congr rfl
    intro p hp
    exact mrt_prime_cofactor_expansion P L N hδ hL hδ2 hp (hP p hp).pos A B t
  rw [mrt_coarse_polynomial_prime_sum, hex, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  rw [sum_comm]
  unfold mrtExponentialPolynomial
  calc
    _ = ∑ n ∈ Icc 1 (4 * N),
        (mrtPrimeExtractionError P L N C A B n / (n : ℂ)) *
          Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
      apply sum_congr rfl
      intro n _
      unfold mrtPrimeExtractionError mrtPrimeProductError
      rw [sum_div, sum_mul]
      apply sum_congr rfl
      intro p _
      by_cases hd : p ∣ n
      · by_cases hw : (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N
        · simp only [hd, hw, ite_true, if_true, and_self, mrtDirichletAtom]
          ring
        · simp only [hd, hw, ite_true, if_true, ite_false, if_false, and_false, sub_self, zero_div, zero_mul]
      · simp only [hd, false_and, ite_false, if_false, sub_self, zero_div, zero_mul]
    _ = _ := by
      symm
      apply sum_subset
      · intro n hn
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      · intro n hn hnot
        have hnN : n ≤ N := by
          by_contra h
          exact hnot (mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩)
        dsimp only
        rw [mrt_prime_extraction_error_zero P L (fun p hp => (hL p hp).1) N C A B hnN]
        simp


/-- The coarse prime-product factorization is valid for general
multiplicative coefficients up to the already controlled square error. -/
theorem mrt_general_prime_factorization_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (C A B : ℕ → ℂ) (hC : OneBounded C) (hA : OneBounded A) (hB : OneBounded B)
    (hproduct : ∀ p ∈ P, ∀ m, 0 < m → ¬p ∣ m → C (p * m) = A p * B m)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtCoarsePolynomial P L N C t -
      (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t)‖ ^ 2) ≤
      512 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  simp_rw [mrt_general_prime_factorization P hP L N hδ hδ2 hL C A B]
  apply mrt_prime_square_broad_mean P hP _ hN _ hT
  intro n hn
  exact mrt_prime_product_error_bound P hP _ C A B hC hA hB hproduct
    (hN.trans (mem_Ioc.mp hn).1)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeneralTypical
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual typical-set Ramaré approximation for ordinary
multiplicative functions. Prime squares account for every failure of
complete multiplicativity, before any frequency-class witness cover. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrtCofactorPolynomial_continuous (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a : ℝ) : Continuous (mrtCofactorPolynomial P F N a) := by
  unfold mrtCofactorPolynomial
  apply continuous_finsetSum
  intro m _
  by_cases hw : (N : ℝ) < a * m ∧ a * m ≤ 2 * N
  · simp only [ite_eq_left hw]
    unfold mrtDirichletAtom
    fun_prop
  · simp only [ite_eq_right hw]
    exact continuous_const

lemma mrt_extracted_prime_bins {κ : Type*} [DecidableEq κ]
    (K : Finset κ) (P : Finset ℕ) (bin : ℕ → κ)
    (hbin : ∀ p ∈ P, bin p ∈ K) (lower : κ → ℝ) (N : ℕ)
    (A B : ℕ → ℂ) (t : ℝ) :
    (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (lower (bin p)) t) =
      ∑ k ∈ K,
        mrtExponentialPolynomial (P.filter (fun p => bin p = k))
          (fun p => A p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t *
        mrtCofactorPolynomial P B N (lower k) t := by
  rw [← sum_fiberwise_of_maps_to hbin]
  apply sum_congr rfl
  intro k _
  unfold mrtExponentialPolynomial
  rw [sum_mul]
  apply sum_congr rfl
  intro p hp
  have hbp := (mem_filter.mp hp).2
  simp only [mrtDirichletAtom, hbp]

theorem mrt_typical_general_prime_mean_square {ι : Type*}
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (lower : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower p ≤ p ∧ (p : ℝ) ≤ δ * lower p)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t -
        ∑ p ∈ P j, mrtDirichletAtom F p t *
          mrtCofactorPolynomial (P j) (mrtTypicalCoefficient (J.erase j) P F) N (lower p) t‖ ^ 2) ≤
      1408 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
  let C := mrtTypicalCoefficient J P F
  let B := mrtTypicalCoefficient (J.erase j) P F
  let D := mrtDyadicPolynomial C N
  let G := mrtCoarsePolynomial (P j) lower N C
  let H : ℝ → ℂ := fun t => ∑ p ∈ P j, mrtDirichletAtom F p t *
    mrtCofactorPolynomial (P j) B N (lower p) t
  have hD : Continuous D := mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := mrtExponentialPolynomial_continuous _ _ _
  have hR (p : ℕ) : Continuous (fun t => mrtCofactorPolynomial (P j) B N (lower p) t) :=
    mrtCofactorPolynomial_continuous (P j) B N (lower p)
  have hH : Continuous H := by
    apply continuous_finsetSum
    intro p _
    apply Continuous.mul _ (hR p)
    unfold mrtDirichletAtom
    fun_prop
  have hboundary := mrt_coarse_error_mean_square (P j) (hP j hj) lower
    hN hδ hδ2 hL C (mrtTypicalCoefficient_oneBounded J P F hFb) hT
  rw [mrtTypicalCoefficient_supported J P hj F] at hboundary
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at hboundary
  have hproduct := mrt_general_prime_factorization_mean (P j) (hP j hj) lower hN hδ hδ2 hL
    C F B (mrtTypicalCoefficient_oneBounded J P F hFb) hFb
    (mrtTypicalCoefficient_oneBounded (J.erase j) P F hFb)
    (fun p hp m hm hpm => mrtTypicalCoefficient_prime_mul_coprime J P hP hdis hj F hF hp hm hpm)
    hT
  change (∫ t in -T..T, ‖G t - H t‖ ^ 2) ≤ _ at hproduct
  have hproduct' : (∫ t in -T..T, ‖G t - H t‖ ^ 2) ≤
      512 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
    apply hproduct.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_right (by linarith)
  have hs := mrt_restricted_energy_split (fun t => D t - H t) (fun t => G t - H t)
    (hD.sub hH) (hG.sub hH) hT.le (Set.Subset.refl (Set.Ioc (-T) T))
  have he (t : ℝ) : (D t - H t) - (G t - H t) = D t - G t := by ring
  simp only [he, ← intervalIntegral.integral_of_le (show -T ≤ T by linarith)] at hs
  apply hs.trans
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hboundary (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hproduct' (by norm_num : (0 : ℝ) ≤ 2))
  convert hh using 1 <;> first | rfl | ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFrequencyExponents
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The increasing prime-polynomial thresholds in MRT's multiscale
partition, indexed from zero to match `mrtFirstSmallBand`. -/

namespace TwoPointCorrelations

lemma mrtFrequencyExponent_bounds {η : ℝ} (hη : 0 ≤ η) (j : ℕ) :
    1 / 4 - 3 * η / 2 ≤ mrtFrequencyExponent η j ∧
      mrtFrequencyExponent η j ≤ 1 / 4 - η := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hi : (1 : ℝ) / (2 * ((j : ℝ) + 1)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hi0 : (0 : ℝ) ≤ 1 / (2 * ((j : ℝ) + 1)) := by positivity
  unfold mrtFrequencyExponent
  constructor
  · have hh := mul_le_mul_of_nonneg_left hi hη
    nlinarith
  · have hh := mul_nonneg hη hi0
    nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTLogPrimeBins
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual logarithmic bins used in the MRT factorization. Their integer
index and multiplicative width are controlled with the original floor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_prime_log_lower_one {H : ℝ} (hH : 0 < H) (k : ℕ) :
    1 ≤ mrtPrimeLogLower H k :=
  Real.one_le_exp (div_nonneg (Nat.cast_nonneg k) hH.le)

lemma mrt_prime_log_bin_bounds {H : ℝ} (hH : 0 < H) {p : ℕ} (hp : 1 ≤ p) :
    mrtPrimeLogLower H (mrtPrimeLogBin H p) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (1 / H) * mrtPrimeLogLower H (mrtPrimeLogBin H p) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp1
  have hlo : (mrtPrimeLogBin H p : ℝ) ≤ H * Real.log p :=
    Nat.floor_le (mul_nonneg hH.le (Real.log_nonneg hp1))
  have hhi : H * Real.log p < (mrtPrimeLogBin H p : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · calc
      _ ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr
        ((div_le_iff₀ hH).mpr (by nlinarith))
      _ = _ := Real.exp_log hp0
  · calc
      (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log hp0).symm
      _ ≤ Real.exp (1 / H + (mrtPrimeLogBin H p : ℝ) / H) := by
        apply Real.exp_le_exp.mpr
        rw [← add_div]
        apply (le_div_iff₀ hH).mpr
        nlinarith
      _ = _ := by rw [Real.exp_add]; rfl

lemma mrt_prime_log_bin_range {H P Q : ℝ} (hH : 0 ≤ H)
    (hP : 0 < P) {p : ℕ} (hp : P ≤ p) (hq : (p : ℝ) ≤ Q) :
    mrtPrimeLogBin H p ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊ := by
  have hp0 : (0 : ℝ) < p := hP.trans_le hp
  apply mem_Icc.mpr
  constructor
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.log_le_log hP hp) hH)
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hq) hH)

lemma mrt_prime_log_width {H : ℝ} (hH : 2 ≤ H) :
    1 ≤ Real.exp (1 / H) ∧ Real.exp (1 / H) ≤ 2 ∧
      Real.exp (1 / H) - 1 ≤ 2 / H := by
  have hH0 : 0 < H := by linarith
  have hi0 : (0 : ℝ) ≤ 1 / H := by positivity
  have hi : (1 : ℝ) / H ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hH
  have he := Real.exp_bound' hi0 (show (1 : ℝ) / H ≤ 1 by linarith) (n := 1) (by norm_num)
  norm_num at he
  have he' : Real.exp (1 / H) ≤ 1 + (1 / H) * 2 := by simpa only [one_div] using he
  refine ⟨Real.one_le_exp hi0, ?_, ?_⟩
  · nlinarith [he']
  · simpa only [div_eq_mul_inv, one_mul] using
      (show Real.exp (1 / H) - 1 ≤ 2 * (1 / H) by linarith [he'])

lemma mrt_prime_log_lower_le_upper {H Q : ℝ} (hH : 0 < H) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : k ≤ ⌊H * Real.log Q⌋₊) : mrtPrimeLogLower H k ≤ Q := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hf : (⌊H * Real.log Q⌋₊ : ℝ) ≤ H * Real.log Q :=
    Nat.floor_le (mul_nonneg hH.le (Real.log_nonneg hQ))
  have hkR : (k : ℝ) ≤ ⌊H * Real.log Q⌋₊ := by exact_mod_cast hk
  calc
    _ ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr
      ((div_le_iff₀ hH).mpr (by nlinarith))
    _ = _ := Real.exp_log hQ0

lemma mrt_log_bin_card {H Q P : ℝ} (hH : 0 ≤ H) (hQ : 1 ≤ Q) :
    ((Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card : ℝ) ≤ H * Real.log Q + 1 := by
  have hc : (Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card ≤ ⌊H * Real.log Q⌋₊ + 1 := by
    rw [Nat.card_Icc]
    omega
  have hf : (⌊H * Real.log Q⌋₊ : ℝ) ≤ H * Real.log Q :=
    Nat.floor_le (mul_nonneg hH (Real.log_nonneg hQ))
  have hcR : ((Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card : ℝ) ≤
      (⌊H * Real.log Q⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  linarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTLogBinEndpoints
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint control for every logarithmic bin, including the first
partially filled bin below the original lower endpoint. -/

namespace TwoPointCorrelations

open Finset

lemma mrt_log_bin_lower_endpoint {H P : ℝ} (hH : 1 ≤ H) (hP : 0 < P)
    {k : ℕ} (hk : ⌊H * Real.log P⌋₊ ≤ k) :
    Real.exp (-1) * P ≤ mrtPrimeLogLower H k := by
  have hH0 : 0 < H := by linarith
  have hkR : (⌊H * Real.log P⌋₊ : ℝ) ≤ k := by exact_mod_cast hk
  have hf : H * Real.log P < (k : ℝ) + 1 :=
    (Nat.lt_floor_add_one (H * Real.log P)).trans_le (by linarith)
  have hi : (1 : ℝ) / H ≤ 1 := (div_le_one hH0).mpr hH
  have hl : Real.log P - 1 ≤ (k : ℝ) / H := by
    have hh : Real.log P < ((k : ℝ) + 1) / H :=
      (lt_div_iff₀ hH0).mpr (by nlinarith)
    rw [add_div] at hh
    linarith
  calc
    _ = Real.exp (Real.log P - 1) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hP]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hl

lemma mrt_log_bin_endpoints {H P Q : ℝ} (hH : 1 ≤ H) (hP : 0 < P) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : k ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊) :
    Real.exp (-1) * P ≤ mrtPrimeLogLower H k ∧ mrtPrimeLogLower H k ≤ Q :=
  ⟨mrt_log_bin_lower_endpoint hH hP (mem_Icc.mp hk).1,
    mrt_prime_log_lower_le_upper (by linarith) hQ (mem_Icc.mp hk).2⟩

lemma mrt_log_bin_prime_support {H : ℝ} (hH : 2 ≤ H) {p : ℕ} (hp : 1 ≤ p) :
    mrtPrimeLogLower H (mrtPrimeLogBin H p) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ 2 * mrtPrimeLogLower H (mrtPrimeLogBin H p) := by
  have hb := mrt_prime_log_bin_bounds (by linarith : 0 < H) hp
  refine ⟨hb.1, hb.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mrt_prime_log_width hH).2.1
    (Real.exp_pos _).le

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTResolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic bin resolution used in the multiscale partition.
Its balance with the first prime threshold is exact. -/

namespace TwoPointCorrelations

open Finset

lemma mrtBaseResolution_pos (P Q η : ℝ) : 0 < mrtBaseResolution P Q η :=
  Real.exp_pos _

lemma mrtResolution_pos (P Q η : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    0 < mrtResolution P Q η j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  exact mul_pos (sq_pos_of_pos hj0) (mrtBaseResolution_pos P Q η)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBinPrefactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial factors in the later-band estimate are absorbed
by a small part of the saving from the true band endpoints. -/

namespace TwoPointCorrelations

lemma mrt_log_band_upper_mono {Q : ℝ} (hQ : 1 ≤ Real.log Q)
    {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    Real.log (mrtBandUpper Q i) ≤ Real.log (mrtBandUpper Q k) := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (hi.trans hik)
  have hik' : (i : ℝ) ≤ k := by exact_mod_cast hik
  simp only [mrtBandUpper, Real.log_exp]
  apply mul_le_mul
  · exact (pow_le_pow_left₀ hi0 hik' _).trans
      (pow_le_pow_right₀ hk1 (by omega))
  · exact pow_le_pow_right₀ hQ hik
  · positivity
  · positivity

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CanonicalMellinBands
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published logarithmic prime bands in the actual energy partition -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma canonical_resolution_ge_two {P Q η : ℝ}
    (hH : 2 ≤ mrtBaseResolution P Q η) (j : ℕ) :
    2 ≤ mrtResolution P Q η (j+1) := by
  have hj : (1 : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast (show 1 ≤ j+1 by omega)
  have hp := one_le_pow₀ (n := 2) hj
  unfold mrtResolution
  nlinarith [mrtBaseResolution_pos P Q η]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinBandSelection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximal band selection below the square-root logarithmic cutoff -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

lemma mellinBandCount_next (Q Y : ℝ) (hQ : 1 ≤ Real.log Q) :
    Y < Real.log (mrtBandUpper Q (mellinBandCount Q Y hQ+1)) :=
  Nat.find_spec (exists_mellin_band_above Q Y hQ)

lemma mellinBandCount_good (Q Y : ℝ) (hQ : 1 ≤ Real.log Q)
    {j : ℕ} (hj : j < mellinBandCount Q Y hQ) :
    mrtBandUpper Q (j+1) ≤ Real.exp Y := by
  have hh : ¬Y < Real.log (mrtBandUpper Q (j+1)) :=
    Nat.find_min (exists_mellin_band_above Q Y hQ) hj
  have hl := le_of_not_gt hh
  have hup : 0 < mrtBandUpper Q (j+1) := Real.exp_pos _
  calc
    _ = Real.exp (Real.log (mrtBandUpper Q (j+1))) := (Real.exp_log hup).symm
    _ ≤ _ := Real.exp_le_exp.mpr hl

lemma mellinBandCount_tendsto (Q : ℝ) (hQ : 1 ≤ Real.log Q) :
    Tendsto (fun Y => mellinBandCount Q Y hQ) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (Real.log (mrtBandUpper Q (b+1)))] with Y hY
  by_contra hnot
  have hb : mellinBandCount Q Y hQ+1 ≤ b+1 := by omega
  have hh := mrt_log_band_upper_mono hQ (by omega) hb
  linarith [mellinBandCount_next Q Y hQ]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinLastBandGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final selected band lies beyond every fixed logarithmic power -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

lemma next_band_log_le_lower_sq {P Q : ℝ} (hP : 1 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) {j : ℕ} (hj : 8 ≤ j) :
    Real.log (mrtBandUpper Q (j+1)) ≤ (Real.log (mrtBandLower P Q j))^2 := by
  have hj4 : (4:ℝ) ≤ j := by exact_mod_cast (show 4 ≤ j by omega)
  have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
  have hstep : ((j+1:ℕ):ℝ) ≤ 2*(j:ℝ) := by push_cast <;> linarith
  have htwo : (2:ℝ)^(4*j+6) ≤ (j:ℝ)^(4*j-6) := by
    calc
      _ ≤ (2:ℝ)^(2*(4*j-6)) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (4:ℝ)^(4*j-6) := by rw [pow_mul]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hj4 _
  have hp : ((j+1:ℕ):ℝ)^(4*(j+1)+2) ≤ (j:ℝ)^(8*j) := by
    calc
      _ = ((j+1:ℕ):ℝ)^(4*j+6) := by congr 1
      _ ≤ (2*(j:ℝ))^(4*j+6) := pow_le_pow_left₀ (by positivity) hstep _
      _ = (2:ℝ)^(4*j+6)*(j:ℝ)^(4*j+6) := mul_pow _ _ _
      _ ≤ (j:ℝ)^(4*j-6)*(j:ℝ)^(4*j+6) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = (j:ℝ)^(8*j) := by rw [← pow_add]; congr 1; omega
  have hqpow : (Real.log Q)^(j+1) ≤ (Real.log Q)^(2*(j-1)) :=
    pow_le_pow_right₀ hQ (by omega)
  have hpp : 1 ≤ (Real.log P)^2 := one_le_pow₀ hP
  simp only [mrtBandUpper,mrtBandLower,Real.log_exp]
  rw [mul_pow,mul_pow,← pow_mul,← pow_mul]
  have hprod := mul_le_mul hp hqpow (by positivity) (by positivity)
  have he1 : 4*j*2=8*j := by omega
  rw [he1]
  simpa only [Nat.mul_comm] using hprod.trans
    (le_mul_of_one_le_right
      (show 0 ≤ (j:ℝ)^(8*j)*(Real.log Q)^(2*(j-1)) by positivity) hpp)

/-- Maximality below `exp(sqrt(log X))` and the explicit adjacent-band
formula force the lower endpoint to grow faster than `exp(log X^(1/4))`. -/
theorem last_selected_band_lower (P Q : ℝ) (hP : 1 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) :
    ∀ᶠ X : ℝ in atTop, let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
      8 ≤ J ∧ (Real.log X)^(1/4:ℝ) ≤ Real.log (mrtBandLower P Q J) := by
  have hJ := (mellinBandCount_tendsto Q hQ).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hJ.eventually (eventually_ge_atTop 8),eventually_ge_atTop 1]
    with X hXJ hX
  dsimp only
  let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
  refine ⟨hXJ,?_⟩
  have hl := (mellinBandCount_next Q (Real.sqrt (Real.log X)) hQ).le.trans
    (next_band_log_le_lower_sq hP hQ hXJ)
  have hL : 0 ≤ Real.log (mrtBandLower P Q J) := by
    simp only [mrtBandLower,Real.log_exp]
    positivity
  have hs : Real.sqrt (Real.sqrt (Real.log X)) ≤ Real.log (mrtBandLower P Q J) :=
    (Real.sqrt_le_iff).mpr ⟨hL,hl⟩
  have he : Real.sqrt (Real.sqrt (Real.log X)) = (Real.log X)^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul (Real.log_nonneg hX)]
    norm_num
  rwa [he] at hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinEndpointScales
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint range needed by the growing prime moment -/
namespace JointDickman
open Filter
open scoped Topology

theorem mellin_endpoint_scales : ∀ᶠ X : ℝ in atTop, ∀ L : ℝ,
    Real.exp ((Real.log X)^(1/4:ℝ)-1) ≤ L → L ≤ Real.exp (Real.sqrt (Real.log X)) →
    let M := ⌈2*L⌉₊
    2 ≤ M ∧ 1 ≤ Real.log (M:ℝ) ∧ (Real.log X)^100 ≤ (M:ℝ) ∧
      (M:ℝ) ≤ X^(1/100:ℝ) := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp Real.tendsto_log_atTop
  have hlim : Tendsto (fun X : ℝ => 100*Real.log (Real.log X)/(Real.log X)^(1/4:ℝ))
      atTop (𝓝 0) := by
    have hh := ((log_power_div_power_tendsto_zero 1 (by norm_num : (0:ℝ)<1/4)).comp
      Real.tendsto_log_atTop).const_mul 100
    simpa only [Function.comp_def,Real.rpow_one,mul_zero,mul_div_assoc] using hh
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop 100000),
    hpow.eventually (eventually_ge_atTop 2),
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2)),
    eventually_gt_atTop (0:ℝ)] with X hlog hpowX hlimX hX
  change 2 ≤ (Real.log X)^(1/4:ℝ) at hpowX
  intro L hLlo hLhi M
  have hlog0 : 0 < Real.log X := by linarith
  have hp0 : 0 < (Real.log X)^(1/4:ℝ) := Real.rpow_pos_of_pos hlog0 _
  have hb := (div_le_iff₀ hp0).mp hlimX
  have hlowlog : 100*Real.log (Real.log X) ≤ (Real.log X)^(1/4:ℝ)-1 := by
    linarith
  have hLe : Real.exp 1 ≤ L := (Real.exp_le_exp.mpr (by linarith)).trans hLlo
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hLe
  have hMlo : 2*L ≤ (M:ℝ) := Nat.le_ceil _
  have hMhi : (M:ℝ) ≤ 3*L := by
    have hh := Nat.ceil_lt_add_one (show 0≤2*L by positivity)
    dsimp [M]
    linarith
  have hM0 : 0 < (M:ℝ) := by linarith
  refine ⟨by exact_mod_cast (show (2:ℝ)≤M by linarith),?_,?_,?_⟩
  · have hh := Real.log_le_log (Real.exp_pos 1) (hLe.trans (by linarith : L≤(M:ℝ)))
    simpa only [Real.log_exp] using hh
  · have he : (Real.log X)^100 = Real.exp (100*Real.log (Real.log X)) := by
      rw [show Real.exp (100*Real.log (Real.log X)) =
        (Real.exp (Real.log (Real.log X)))^100 by
          simpa using Real.exp_nat_mul (Real.log (Real.log X)) 100,
        Real.exp_log hlog0]
    rw [he]
    exact ((Real.exp_le_exp.mpr hlowlog).trans hLlo).trans (by linarith)
  · have hs : Real.sqrt (Real.log X) ≤ Real.log X/200 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · positivity
      · have hm := mul_nonneg (show 0≤Real.log X-40000 by linarith) hlog0.le
        nlinarith
    have hlog3 : Real.log 3 ≤ 2 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
      linarith
    have he : 3*Real.exp (Real.sqrt (Real.log X)) ≤ X^(1/100:ℝ) := by
      rw [Real.rpow_def_of_pos hX,show (3:ℝ)=Real.exp (Real.log 3) by
        rw [Real.exp_log (by norm_num : (0:ℝ)<3)],← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    exact hMhi.trans ((mul_le_mul_of_nonneg_left hLhi (by norm_num)).trans he)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ChebyshevDischarge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Chebyshev estimate needed for finite prime-product errors -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem primeCounting_le_self (N : ℕ) : Nat.primeCounting N ≤ N := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    _ ≤ (Icc 1 N).card := card_le_card (fun p hp =>
      mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.one_le,(Nat.mem_primesLE.mp hp).1⟩)
    _ = N := by simp

theorem chebyshevPrimeCountingInput : PublishedInputs.ChebyshevPrimeCountingInput := by
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  let C : ℝ := max (Real.log 4+1) (Real.log (max 2 x₀))
  have hC : 0 ≤ C := (by positivity : (0 : ℝ) ≤ Real.log 4+1).trans (le_max_left _ _)
  refine ⟨C,hC,fun x hx => ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hxx : x₀ ≤ x
  · exact (hx₀ x hxx).trans (by
      apply div_le_div_of_nonneg_right _ hlog.le
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · have hpn : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast primeCounting_le_self ⌊x⌋₊
    have hp : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x :=
      hpn.trans (Nat.floor_le (by linarith))
    have hlC : Real.log x ≤ C :=
      (Real.log_le_log (by linarith) ((le_of_not_ge hxx).trans (le_max_right _ _))).trans
        (le_max_right _ _)
    apply (le_div_iff₀ hlog).mpr
    calc
      _ ≤ x * Real.log x := mul_le_mul_of_nonneg_right hp hlog.le
      _ ≤ x * C := mul_le_mul_of_nonneg_left hlC (by linarith)
      _ = _ := mul_comm _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeReciprocalSquareMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal-square mass of a dyadic prime interval -/
namespace JointDickman
open Finset

/-- Chebyshev's proved prime bound supplies the second logarithmic saving
when sparse sampling is applied to a reciprocal prime polynomial. -/
theorem prime_reciprocal_square_mass : ∃ D : ℝ, 0 < D ∧
    ∀ (N : ℝ), 2 ≤ N → ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∑ p ∈ Q, 1/(p:ℝ)^2) ≤ D/(N*Real.log N) := by
  obtain ⟨C,hC,hcount⟩ := chebyshevPrimeCountingInput
  refine ⟨2*(C+1),by positivity,?_⟩
  intro N hN Q hQ
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog2 : Real.log N ≤ Real.log (2*N) :=
    Real.log_le_log hN0 (by linarith)
  have hcard : (Q.card:ℝ) ≤ C*(2*N)/Real.log (2*N) := by
    apply le_trans (b := (Nat.primeCounting ⌊2*N⌋₊:ℝ))
    · rw [← Nat.primesLE_card_eq_primeCounting]
      exact_mod_cast card_le_card (show Q ⊆ Nat.primesLE ⌊2*N⌋₊ by
        intro p hp
        exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hQ p hp).2.2, (hQ p hp).1⟩)
    · exact hcount (2*N) (by linarith)
  have hcard' : (Q.card:ℝ) ≤ 2*C*N/Real.log N := by
    exact hcard.trans (by
      rw [show C*(2*N)=2*C*N by ring]
      exact div_le_div_of_nonneg_left (by positivity) hlog hlog2)
  calc
    _ ≤ ∑ _p ∈ Q, 1/N^2 := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le (sq_pos_of_pos hN0)
        (pow_le_pow_left₀ hN0.le (hQ p hp).2.1 2)
    _ = (Q.card:ℝ)/N^2 := by simp [div_eq_mul_inv]
    _ ≤ (2*C*N/Real.log N)/N^2 := div_le_div_of_nonneg_right hcard' (sq_nonneg N)
    _ = 2*C/(N*Real.log N) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTSampling
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling a differentiable function at separated points.  Unit
intervals give a finite Sobolev estimate, which will be applied to the
prime-polynomial powers already expanded into Dirichlet coefficients. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped RealInnerProductSpace

lemma mrt_value_le_unit_integral (F F' B : ℝ → ℝ)
    (hF : Continuous F) (hF' : ∀ t, HasDerivAt F (F' t) t)
    (hB : Continuous B) (hB0 : ∀ t, 0 ≤ B t)
    (hd : ∀ t, |F' t| ≤ B t) (a : ℝ) :
    F a ≤ ∫ t in a..(a + 1), F t + B t := by
  have hiB : IntervalIntegrable B volume a (a + 1) := hB.intervalIntegrable a (a + 1)
  have hp (y : ℝ) (hy : y ∈ Icc a (a + 1)) :
      F a ≤ F y + ∫ t in a..(a + 1), B t := by
    have hdiff : ‖F y - F a‖ ≤ ∫ t in a..y, B t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hy.1 hF.continuousOn
        (fun t _ => (hF' t).differentiableAt.differentiableWithinAt)
      · exact Filter.Eventually.of_forall fun t _ => by
          rw [(hF' t).deriv, Real.norm_eq_abs]
          exact hd t
      · exact hB.intervalIntegrable a y
    have hm : (∫ t in a..y, B t) ≤ ∫ t in a..(a + 1), B t :=
      intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
        (Filter.Eventually.of_forall hB0) hiB
    have he : F a - F y ≤ ‖F y - F a‖ := by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact le_abs_self _
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + 1)
    (continuous_const.intervalIntegrable a (a + 1))
    ((hF.add continuous_const).intervalIntegrable a (a + 1)) hp
  change (∫ t in a..(a + 1), F a) ≤
    ∫ t in a..(a + 1), F t + (∫ u in a..(a + 1), B u) at hi
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hF.intervalIntegrable a (a + 1))
    (continuous_const.intervalIntegrable a (a + 1)), intervalIntegral.integral_const] at hi
  have hlen : a + 1 - a = 1 := by ring
  simp only [hlen, one_smul] at hi
  rw [intervalIntegral.integral_add (hF.intervalIntegrable a (a + 1)) hiB]
  exact hi

lemma mrt_unit_intervals_disjoint (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    Set.Pairwise (S : Set ℝ) (fun x y => Disjoint (Set.Ioc x (x + 1))
      (Set.Ioc y (y + 1))) := by
  intro x hx y hy hne
  have h := hsep x hx y hy hne
  by_cases hxy : x ≤ y
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    exact Ioc_disjoint_Ioc_of_le (by linarith)
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))] at h
    exact (Ioc_disjoint_Ioc_of_le (by linarith : y + 1 ≤ x)).symm

lemma mrt_sum_unit_integrals_le (S : Finset ℝ) (G : ℝ → ℝ)
    (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ x ∈ S, a ≤ x ∧ x + 1 ≤ b) :
    (∑ x ∈ S, ∫ t in x..(x + 1), G t) ≤ ∫ t in a..b, G t := by
  have hint (x : ℝ) : (∫ t in x..(x + 1), G t) = ∫ t in Ioc x (x + 1), G t :=
    intervalIntegral.integral_of_le (by linarith)
  simp_rw [hint]
  rw [← integral_biUnion_finset S (fun _ _ => measurableSet_Ioc)
    (mrt_unit_intervals_disjoint S hsep)
    (fun x _ => (hG.intervalIntegrable x (x + 1)).1),
    intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set (hG.intervalIntegrable a b).1
    (Filter.Eventually.of_forall hG0)
  exact Filter.Eventually.of_forall fun t ht => by
    obtain ⟨x, hx, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨lt_of_le_of_lt (hS x hx).1 ht.1, ht.2.trans (hS x hx).2⟩

/-- A finite separated sample is controlled by the ordinary square
integrals of a function and its derivative. -/
theorem mrt_separated_square_samples (S : Finset ℝ) (q q' : ℝ → ℂ)
    (hq : Continuous q) (hq' : Continuous q')
    (hd : ∀ t, HasDerivAt q (q' t) t)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (a b : ℝ) (hab : a ≤ b) (hS : ∀ x ∈ S, a ≤ x ∧ x + 1 ≤ b) :
    (∑ x ∈ S, ‖q x‖ ^ 2) ≤ ∫ t in a..b, 2 * ‖q t‖ ^ 2 + ‖q' t‖ ^ 2 := by
  let F := fun t => ‖q t‖ ^ 2
  let B := fun t => ‖q t‖ ^ 2 + ‖q' t‖ ^ 2
  have hB : Continuous B := (hq.norm.pow 2).add (hq'.norm.pow 2)
  have hder (t : ℝ) : |2 * inner ℝ (q t) (q' t)| ≤ B t := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hi := abs_real_inner_le_norm (q t) (q' t)
    dsimp only [B]
    nlinarith [sq_nonneg (‖q t‖ - ‖q' t‖)]
  calc
    _ ≤ ∑ x ∈ S, ∫ t in x..(x + 1), F t + B t := by
      apply sum_le_sum
      intro x _
      exact mrt_value_le_unit_integral F (fun t => 2 * inner ℝ (q t) (q' t)) B
        (hq.norm.pow 2) (fun t => (hd t).norm_sq) hB
        (fun t => by dsimp only [B] <;> positivity) hder x
    _ ≤ ∫ t in a..b, F t + B t :=
      mrt_sum_unit_integrals_le S (fun t => F t + B t) ((hq.norm.pow 2).add hB)
        (fun t => by dsimp only [F, B] <;> positivity)
        hsep a b hab hS
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [F, B]
      ring

lemma mrt_exponential_polynomial_deriv {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    HasDerivAt (mrtExponentialPolynomial S a freq)
      (mrtExponentialPolynomial S (fun i => a i * ((freq i : ℂ) * Complex.I)) freq t) t := by
  unfold mrtExponentialPolynomial
  apply HasDerivAt.fun_sum
  intro i _
  have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (freq i : ℂ)).mul_const
    Complex.I).cexp.const_mul (a i)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp only [Complex.ofReal_mul, Complex.ofRealCLM_apply]
  · simp only [Complex.ofReal_mul, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
    ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTLargeValues
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large values at one-separated heights, obtained from the exact
prime-product expansion and the finite sampling inequality. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_dirichlet_derivative_mass (N : ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ Ioc 0 N, ‖a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I)‖ ^ 2) ≤
      (Real.log (N : ℝ)) ^ 2 * ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hn0 : 0 < n := (mem_Ioc.mp hn).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp hn).2
  have hlog0 := Real.log_nonneg hn1
  have hlogN := Real.log_le_log (by positivity : (0 : ℝ) < n) hnN
  simp only [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog0, mul_pow]
  calc
    _ ≤ ‖a n‖ ^ 2 * (Real.log (N : ℝ)) ^ 2 := by gcongr
    _ = _ := mul_comm _ _

theorem mrt_dirichlet_separated_samples (N : ℕ) (a : ℕ → ℂ)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial (Ioc 0 N) a
      (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + 1 + N) * (2 + (Real.log (N : ℝ)) ^ 2) *
        ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2 := by
  let q := mrtExponentialPolynomial (Ioc 0 N) a (fun n => -Real.log (n : ℝ))
  let q' := mrtExponentialPolynomial (Ioc 0 N)
    (fun n => a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I))
    (fun n => -Real.log (n : ℝ))
  have hq := mrtExponentialPolynomial_continuous (Ioc 0 N) a
    (fun n => -Real.log (n : ℝ))
  have hq' := mrtExponentialPolynomial_continuous (Ioc 0 N)
    (fun n => a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I))
    (fun n => -Real.log (n : ℝ))
  have hder (t : ℝ) : HasDerivAt q (q' t) t := by
    simpa only [q, q', Complex.ofReal_neg] using
      mrt_exponential_polynomial_deriv (Ioc 0 N) a (fun n => -Real.log (n : ℝ)) t
  have hs := mrt_separated_square_samples S q q' hq hq' hder hsep (-(T + 1)) (T + 1)
    (by linarith) (fun t ht => by
      have hh := abs_le.mp (hS t ht)
      constructor <;> linarith)
  have hm := mrt_dirichlet_mean_square N a (show 0 < T + 1 by linarith)
  have hm' := mrt_dirichlet_mean_square N
    (fun n => a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I))
    (show 0 < T + 1 by linarith)
  have hd := mrt_dirichlet_derivative_mass N a
  have hp : 0 ≤ 8 * Real.exp 1 * (T + 1 + N) := by positivity
  calc
    _ ≤ ∫ t in -(T + 1)..(T + 1), 2 * ‖q t‖ ^ 2 + ‖q' t‖ ^ 2 := hs
    _ = 2 * (∫ t in -(T + 1)..(T + 1), ‖q t‖ ^ 2) +
        ∫ t in -(T + 1)..(T + 1), ‖q' t‖ ^ 2 := by
      have hiq : IntervalIntegrable (fun t => 2 * ‖q t‖ ^ 2) volume (-(T + 1)) (T + 1) :=
        (continuous_const.mul (hq.norm.pow 2)).intervalIntegrable _ _
      have hiq' : IntervalIntegrable (fun t => ‖q' t‖ ^ 2) volume (-(T + 1)) (T + 1) :=
        (hq'.norm.pow 2).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hiq hiq', intervalIntegral.integral_const_mul]
    _ ≤ 2 * (8 * Real.exp 1 * (T + 1 + N) * ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2) +
        8 * Real.exp 1 * (T + 1 + N) *
          ((Real.log (N : ℝ)) ^ 2 * ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num))
        (hm'.trans (mul_le_mul_of_nonneg_left hd hp))
    _ = _ := by ring

/-- The sampled `2r`-th moment of an actual prime Dirichlet polynomial.
The extra logarithmic square comes only from sampling the continuous
moment on unit intervals. -/
theorem mrt_prime_separated_moment (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t‖ ^
      (2 * r)) ≤
      8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2) *
        (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
  have he (t : ℝ) : ‖mrtExponentialPolynomial P a
      (fun p => -Real.log (p : ℝ)) t‖ ^ (2 * r) =
      ‖mrtExponentialPolynomial (Ioc 0 (N ^ r)) (mrtPrimePowerCoefficient P a r)
        (fun n => -Real.log (n : ℝ)) t‖ ^ 2 := by
    rw [← mrt_prime_polynomial_power P a N r hP hN t, norm_pow, ← pow_mul]
    rw [Nat.mul_comm]
  simp_rw [he]
  apply (mrt_dirichlet_separated_samples (N ^ r) (mrtPrimePowerCoefficient P a r)
    S hT hS hsep).trans
  calc
    _ ≤ (8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2)) *
        ((r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r) := by
      apply mul_le_mul_of_nonneg_left (mrt_prime_power_coefficient_mass P a N r hP hN)
      positivity
    _ = _ := by ring

/-- A cardinality bound for one-separated large values. -/
theorem mrt_prime_large_values (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hlarge : ∀ t ∈ S,
      V ≤ ‖mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t‖) :
    (S.card : ℝ) ≤
      (8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2) *
        (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r) / V ^ (2 * r) := by
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  calc
    _ = ∑ _t ∈ S, V ^ (2 * r) := by simp
    _ ≤ ∑ t ∈ S, ‖mrtExponentialPolynomial P a
        (fun p => -Real.log (p : ℝ)) t‖ ^ (2 * r) := by
      apply sum_le_sum
      intro t ht
      exact pow_le_pow_left₀ hV.le (hlarge t ht) _
    _ ≤ _ := mrt_prime_separated_moment P a N r hP hN S hT hS hsep

/-- A convenient geometric-decay form.  The hypothesis compares the
moment order times the coefficient square mass with the large-value
threshold, rather than hiding this numerical requirement in an input. -/
theorem mrt_prime_large_values_geometric (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T V ρ : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hmass : (r : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ≤ ρ * V ^ 2)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hlarge : ∀ t ∈ S,
      V ≤ ‖mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t‖) :
    (S.card : ℝ) ≤
      (8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2)) * ρ ^ r := by
  have hf : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by
    exact_mod_cast Nat.factorial_le_pow r
  have hmass0 : 0 ≤ ∑ p ∈ P, ‖a p‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hpow : (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r ≤
      ρ ^ r * V ^ (2 * r) := by
    calc
      _ ≤ (r : ℝ) ^ r * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r :=
        mul_le_mul_of_nonneg_right hf (pow_nonneg hmass0 _)
      _ = ((r : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2)) ^ r := (mul_pow _ _ _).symm
      _ ≤ (ρ * V ^ 2) ^ r := pow_le_pow_left₀ (by positivity) hmass _
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hconst : 0 ≤ 8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
      (2 + (Real.log (N ^ r : ℕ)) ^ 2) := by positivity
  apply (mrt_prime_large_values P a N r hP hN S hT hV hS hsep hlarge).trans
  apply (div_le_iff₀ (pow_pos hV _)).mpr
  have hh := mul_le_mul_of_nonneg_left hpow hconst
  first | (convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeMomentNormalized
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed prime moment at its natural reciprocal normalization -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

theorem fixed_prime_moment_large_bound (r : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ a : ℝ, Real.exp 1 ≤ a → ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ f : ℕ → ℂ, OneBounded f → ∀ U : Finset ℝ,
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ U, |t| ≤ a^r) → ∀ V : ℝ, 0 < V →
      (∀ t ∈ U, V ≤ ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ)) t‖) →
      (U.card:ℝ) ≤ C*(Real.log a)^2/V^(2*r) := by
  obtain ⟨D,hD,hmass⟩ := prime_reciprocal_square_mass
  let C := 8*Real.exp 1*(2+(3:ℝ)^r)*(2+9*(r:ℝ)^2)*(r.factorial:ℝ)*D^r
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  intro a ha Q hQ f hf U hsep hU V hV hlarge
  have ha1 : 1 ≤ a := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans ha
  have ha0 : 0 < a := by linarith
  have ha2 : 2 ≤ a := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hlog : 1 ≤ Real.log a := by simpa using Real.log_le_log (Real.exp_pos 1) ha
  let M := ⌈2*a⌉₊
  have hMlo : 2*a ≤ (M:ℝ) := Nat.le_ceil _
  have hMhi : (M:ℝ) ≤ 3*a := by
    have hh := Nat.ceil_lt_add_one (show 0≤2*a by positivity)
    dsimp [M]
    linarith
  have hM0 : 0 < (M:ℝ) := by linarith
  have hcoeff : (∑ p ∈ Q, ‖f p/(p:ℂ)‖^2) ≤ D/a := by
    calc
      _ ≤ ∑ p ∈ Q, 1/(p:ℝ)^2 := by
        apply sum_le_sum
        intro p hp
        rw [norm_div,Complex.norm_natCast,div_pow]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith [hf p (hQ p hp).1.pos,norm_nonneg (f p)]
      _ ≤ D/(a*Real.log a) := hmass a ha2 Q hQ
      _ ≤ D/a := div_le_div_of_nonneg_left hD.le ha0 (by nlinarith)
  have hbound := mrt_prime_large_values Q (fun p => f p/(p:ℂ)) M r
    (fun p hp => (hQ p hp).1)
    (fun p hp => by exact_mod_cast (hQ p hp).2.2.trans hMlo) U
    (show 0 ≤ a^r by positivity) hV hU hsep hlarge
  have hpow : ((M^r:ℕ):ℝ) ≤ (3:ℝ)^r*a^r := by
    simpa only [Nat.cast_pow,mul_pow] using pow_le_pow_left₀ hM0.le hMhi r
  have hfirst : a^r+1+((M^r:ℕ):ℝ) ≤ (2+(3:ℝ)^r)*a^r := by
    have hh : 1 ≤ a^r := one_le_pow₀ ha1
    nlinarith
  have hlogM : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by linarith)
  have hlogMu : Real.log (M:ℝ) ≤ 3*Real.log a := by
    have hh := Real.log_le_log hM0 hMhi
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) ha0.ne'] at hh
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  have hsecond : 2+(Real.log ((M^r:ℕ):ℝ))^2 ≤ (2+9*(r:ℝ)^2)*(Real.log a)^2 := by
    rw [Nat.cast_pow,Real.log_pow]
    have hp := pow_le_pow_left₀ hlogM hlogMu 2
    have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (r:ℝ))
    nlinarith [sq_nonneg (Real.log a-1),sq_nonneg (r:ℝ)]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hV.le _)
  calc
    _ ≤ (8*Real.exp 1*((2+(3:ℝ)^r)*a^r)*
        ((2+9*(r:ℝ)^2)*(Real.log a)^2)*(r.factorial:ℝ))*(D/a)^r := by
      gcongr
    _ = C*(Real.log a)^2 := by
      dsimp [C]
      rw [div_pow]
      field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SubsquarePrimeSamples
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A sub-square-root sample count from a growing prime moment -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem subsquare_prime_samples : ∀ᶠ X : ℝ in atTop,
    ∀ (M r : ℕ), 2 ≤ M → (M:ℝ)^r ≤ X → X ≤ (M:ℝ)^(r+1) →
      (M:ℝ) ≤ X^(1/100:ℝ) →
      ∀ (P : Finset ℕ) (a : ℕ → ℂ), (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ M) →
      ∀ (T V : ℝ), 0 ≤ T → T ≤ X → 0 < V →
      (r:ℝ)*(∑ p ∈ P, ‖a p‖^2) ≤ (M:ℝ)^(-5/8:ℝ)*V^2 →
      ∀ U : Finset ℝ, (∀ t ∈ U, |t| ≤ T) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ U, V ≤ ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖) →
      (U.card:ℝ) ≤ X^(5/12:ℝ) := by
  have hlim : Tendsto (fun X : ℝ => 72*Real.exp 1*(Real.log X)^2/X^(17/480:ℝ))
      atTop (𝓝 0) := by
    have hh := (log_power_div_power_tendsto_zero 2 (by norm_num : (0:ℝ)<17/480)).const_mul
      (72*Real.exp 1)
    simpa only [Real.rpow_ofNat,mul_zero,mul_div_assoc] using hh
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with X hX hbudget
  intro M r hM hMX hXM hscale P a hP ha T V hT hTX hV hmass U hU hsep hlarge
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hX
  have hlog : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hM0 : 0 < (M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hM1 : 1 ≤ (M:ℝ) := by exact_mod_cast (show 1≤M by omega)
  have hp1 : 1 ≤ (M:ℝ)^r := one_le_pow₀ hM1
  have hlogM : 0 ≤ Real.log ((M:ℝ)^r) := Real.log_nonneg hp1
  have hlogMX : Real.log ((M:ℝ)^r) ≤ Real.log X :=
    Real.log_le_log (by positivity) hMX
  have hs : 2+(Real.log ((M:ℝ)^r))^2 ≤ 3*(Real.log X)^2 := by
    nlinarith [pow_le_pow_left₀ hlogM hlogMX 2]
  have hquot : X/(M:ℝ) ≤ (M:ℝ)^r := by
    apply (div_le_iff₀ hM0).mpr
    simpa only [pow_succ] using hXM
  have hdecay : ((M:ℝ)^(-5/8:ℝ))^r ≤ X^(-99/160:ℝ) := by
    rw [Real.rpow_pow_comm hM0.le]
    calc
      _ ≤ (X/(M:ℝ))^(-5/8:ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hquot (by norm_num)
      _ = X^(-5/8:ℝ)*(M:ℝ)^(5/8:ℝ) := by
        rw [Real.div_rpow hX0.le hM0.le,div_eq_mul_inv,← Real.rpow_neg hM0.le]
        norm_num
      _ ≤ X^(-5/8:ℝ)*(X^(1/100:ℝ))^(5/8:ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM0.le hscale (by norm_num)) (by positivity)
      _ = _ := by rw [← Real.rpow_mul hX0.le,← Real.rpow_add hX0]; norm_num
  have hh := mrt_prime_large_values_geometric P a M r hP ha U hT hV hmass hU hsep hlarge
  simp only [Nat.cast_pow] at hh
  apply hh.trans
  calc
    _ ≤ (8*Real.exp 1*(3*X)*(3*(Real.log X)^2))*X^(-99/160:ℝ) := by
      gcongr
      linarith
    _ = (72*Real.exp 1*(Real.log X)^2/X^(17/480:ℝ))*X^(5/12:ℝ) := by
      have hd : (72*Real.exp 1*(Real.log X)^2/X^(17/480:ℝ)) =
          (72*Real.exp 1*(Real.log X)^2)*X^(-17/480:ℝ) := by
        rw [show (-17/480:ℝ)= -(17/480:ℝ) by ring,Real.rpow_neg hX0.le]
        rfl
      rw [hd]
      have he : X*X^(-99/160:ℝ)=X^(-17/480:ℝ)*X^(5/12:ℝ) := by
        conv_lhs => lhs; rw [← Real.rpow_one X]
        rw [← Real.rpow_add hX0,← Real.rpow_add hX0]
        norm_num
      linear_combination (norm := ring_nf) (72*Real.exp 1*(Real.log X)^2)*he
    _ ≤ X^(5/12:ℝ) := mul_le_of_le_one_left (by positivity) hbudget

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GrowingMomentParameters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary parameters for the growing prime moment -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

lemma growingPrimeMoment_bounds {X M : ℝ} (hX : 1 ≤ X) (hM : 1 ≤ Real.log M)
    (hM0 : 0 < M) :
    M^(growingPrimeMoment X M) ≤ X ∧
      X ≤ M^(growingPrimeMoment X M+1) ∧
      (growingPrimeMoment X M:ℝ) ≤ Real.log X := by
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlogM : 0 < Real.log M := by linarith
  have hX0 : 0 < X := by linarith
  have hfloor := Nat.floor_le (div_nonneg hlogX hlogM.le)
  have hceil := Nat.lt_floor_add_one (Real.log X/Real.log M)
  refine ⟨?_,?_,?_⟩
  · rw [← Real.rpow_natCast,Real.rpow_def_of_pos hM0]
    calc
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by
        have hh := (le_div_iff₀ hlogM).mp hfloor
        dsimp [growingPrimeMoment]
        nlinarith)
      _ = X := Real.exp_log hX0
  · rw [← Real.rpow_natCast,Real.rpow_def_of_pos hM0]
    calc
      X = Real.exp (Real.log X) := (Real.exp_log hX0).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := (div_lt_iff₀ hlogM).mp hceil
        dsimp [growingPrimeMoment]
        push_cast
        linarith)
  · exact hfloor.trans (div_le_self hlogX hM)

lemma growing_moment_mass {X M V : ℝ} {r : ℕ}
    (hlog : 3 ≤ Real.log X) (hM : 0 < M) (hlarge : (Real.log X)^100 ≤ M)
    (hr : (r:ℝ) ≤ Real.log X) (hV : M^(-1/6:ℝ) ≤ V)
    {A : ℝ} (hA : A ≤ 9/M) :
    (r:ℝ)*A ≤ M^(-5/8:ℝ)*V^2 := by
  have hl0 : 0 < Real.log X := by linarith
  have hroot : (Real.log X)^(25/6:ℝ) ≤ M^(1/24:ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hl0.le 100) hlarge (by norm_num : (0:ℝ)≤1/24)
    rw [← Real.rpow_natCast,← Real.rpow_mul hl0.le] at hh
    norm_num at hh
    exact hh
  have hcube : (Real.log X)^3 ≤ (Real.log X)^(25/6:ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlow : 9*Real.log X ≤ M^(1/24:ℝ) := by
    have hp : 0 ≤ (Real.log X)*((Real.log X)-3)*((Real.log X)+3) := by positivity
    have hh : 9*Real.log X ≤ (Real.log X)^3 := by nlinarith
    exact hh.trans (hcube.trans hroot)
  have hnum : (r:ℝ)*9 ≤ M^(1/24:ℝ) := by linarith
  have hpow : M^(-1/3:ℝ) ≤ V^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hM.le (-1/6:ℝ)) hV 2
    rw [← Real.rpow_mul_natCast hM.le] at hh
    norm_num at hh
    simpa only [neg_div] using hh
  calc
    (r:ℝ)*A ≤ (r:ℝ)*(9/M) := mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg r)
    _ ≤ M^(1/24:ℝ)/M := by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hnum hM.le
    _ = M^(-5/8:ℝ)*M^(-1/3:ℝ) := by
      rw [← Real.rpow_sub_one hM.ne',← Real.rpow_add hM]
      norm_num
    _ ≤ M^(-5/8:ℝ)*V^2 := mul_le_mul_of_nonneg_left hpow (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_GrowingPrimeSamples
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform sparse samples of a prime block with growing endpoints -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma prime_block_reciprocal_mass (M : ℕ) (hM : 0 < M) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (M:ℝ)/3 ≤ (p:ℝ) ∧ p ≤ M)
    (f : ℕ → ℂ) (hf : OneBounded f) :
    (∑ p ∈ P, ‖f p/(p:ℂ)‖^2) ≤ 9/(M:ℝ) := by
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  have hcard : (P.card:ℝ) ≤ M := by
    have hs : P ⊆ Icc 1 M := fun p hp => mem_Icc.mpr ⟨(hP p hp).1.pos,(hP p hp).2.2⟩
    have hh := card_le_card hs
    simpa using (show (P.card:ℝ) ≤ ((Icc 1 M).card:ℝ) by exact_mod_cast hh)
  calc
    _ ≤ ∑ _p ∈ P, (3/(M:ℝ))^2 := by
      apply sum_le_sum
      intro p hp
      have hpr : 0 < (p:ℝ) := by exact_mod_cast (hP p hp).1.pos
      rw [norm_div,Complex.norm_natCast]
      apply pow_le_pow_left₀ (by positivity)
      apply (div_le_div_of_nonneg_right (hf p (hP p hp).1.pos) hpr.le).trans
      apply (div_le_div_iff₀ hpr hMr).mpr
      linarith [(hP p hp).2.1]
    _ = (P.card:ℝ)*(3/(M:ℝ))^2 := by simp
    _ ≤ (M:ℝ)*(3/(M:ℝ))^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = 9/(M:ℝ) := by field_simp <;> norm_num

/-- At threshold `M^(-1/6)`, a block whose endpoints grow faster than a
large logarithmic power has fewer than `X^(5/12)` separated large values. -/
theorem growing_prime_samples : ∀ᶠ X : ℝ in atTop,
    ∀ M : ℕ, 2 ≤ M → 1 ≤ Real.log (M:ℝ) →
      (Real.log X)^100 ≤ (M:ℝ) → (M:ℝ) ≤ X^(1/100:ℝ) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (M:ℝ)/3 ≤ (p:ℝ) ∧ p ≤ M) →
      ∀ f : ℕ → ℂ, OneBounded f → ∀ V : ℝ, 0 < V → (M:ℝ)^(-1/6:ℝ) ≤ V →
      ∀ U : Finset ℝ, (∀ t ∈ U, |t| ≤ X) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ U, V ≤ ‖mrtExponentialPolynomial P (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ)) t‖) → (U.card:ℝ) ≤ X^(5/12:ℝ) := by
  filter_upwards [subsquare_prime_samples,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 3),eventually_ge_atTop 1]
    with X hX hlogX hX1
  intro M hM hlogM hlarge hscale P hP f hf V hV hMV U hU hsep hlargeU
  have hM0 : 0 < (M:ℝ) := by exact_mod_cast (show 0<M by omega)
  obtain ⟨hlo,hhi,hr⟩ := growingPrimeMoment_bounds hX1 hlogM hM0
  apply hX M (growingPrimeMoment X M) hM hlo hhi hscale P
    (fun p => f p/(p:ℂ)) (fun p hp => (hP p hp).1) (fun p hp => (hP p hp).2.2)
    X V (by linarith) le_rfl hV _ U hU hsep hlargeU
  exact growing_moment_mass hlogX hM0 hlarge hr hMV
    (prime_block_reciprocal_mass M (by omega) P hP f hf)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LastBandSamples
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse samples in each bin of the last selected band -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem last_band_bin_samples (P Q : ℝ) (_hP : 2*Real.exp 1 ≤ P)
    (_hPQ : P ≤ Q) (hlogP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hH : 2 ≤ mrtBaseResolution P Q (1/12)) :
    ∀ᶠ X : ℝ in atTop, let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
      let D := canonicalMellinBands P Q (1/12)
      0 < J ∧ ∀ k ∈ D.bins (J-1), ∀ f : ℕ → ℂ, OneBounded f →
        ∀ U : Finset ℝ, (∀ t ∈ U, |t| ≤ X) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
        (∀ t ∈ U, D.threshold (J-1) k ≤ ‖D.polynomial f (J-1) k t‖) →
        (U.card:ℝ) ≤ X^(5/12:ℝ) := by
  filter_upwards [last_selected_band_lower P Q hlogP hQ,mellin_endpoint_scales,
    growing_prime_samples,eventually_ge_atTop 1] with X hlast hscale hsamples hX1
  let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
  let D := canonicalMellinBands P Q (1/12)
  change 8 ≤ J ∧ (Real.log X)^(1/4:ℝ) ≤ Real.log (mrtBandLower P Q J) at hlast
  have hJ : 0 < J := by omega
  have hJid : J-1+1=J := by omega
  refine ⟨hJ,?_⟩
  intro k hk f hf U hU hsep hlarge
  change k ∈ D.bins (J-1) at hk
  change ∀ t ∈ U, D.threshold (J-1) k ≤ ‖D.polynomial f (J-1) k t‖ at hlarge
  let H := mrtResolution P Q (1/12) J
  let L := mrtPrimeLogLower H k
  let M := ⌈2*L⌉₊
  have hH2 : 2 ≤ H := by
    simpa only [hJid] using canonical_resolution_ge_two hH (J-1)
  have hH0 : 0 < H := by linarith
  have hk' : k ∈ mrtLogBins H (mrtBandLower P Q J) (mrtBandUpper Q J) := by
    change k ∈ mrtLogBins (mrtResolution P Q (1/12) (J-1+1))
      (mrtBandLower P Q (J-1+1)) (mrtBandUpper Q (J-1+1)) at hk
    simpa only [hJid] using hk
  have hp0 : 0 < mrtBandLower P Q J := Real.exp_pos _
  have hu1 : 1 ≤ mrtBandUpper Q J := by
    unfold mrtBandUpper
    apply Real.one_le_exp
    positivity
  have hends := mrt_log_bin_endpoints (show 1≤H by linarith) hp0 hu1 hk'
  change Real.exp (-1)*mrtBandLower P Q J ≤ L ∧ L ≤ mrtBandUpper Q J at hends
  have hLl : Real.exp ((Real.log X)^(1/4:ℝ)-1) ≤ L := by
    apply le_trans (b := Real.exp (Real.log (mrtBandLower P Q J)-1))
    · exact Real.exp_le_exp.mpr (by linarith [hlast.2])
    · have he : Real.exp (Real.log (mrtBandLower P Q J)-1) =
          Real.exp (-1)*mrtBandLower P Q J := by
        rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hp0,mul_comm]
      rw [he]
      exact hends.1
  have hLu : L ≤ Real.exp (Real.sqrt (Real.log X)) := hends.2.trans
    (by simpa only [hJid] using mellinBandCount_good Q _ hQ (show J-1<J by omega))
  obtain ⟨hM2,hlogM,hMlarge,hMsmall⟩ := hscale L hLl hLu
  have hMlo : 2*L ≤ (M:ℝ) := Nat.le_ceil _
  have hL1 : 1 ≤ L := mrt_prime_log_lower_one hH0 k
  have hMhi : (M:ℝ) ≤ 3*L := by
    have hh := Nat.ceil_lt_add_one (show 0≤2*L by positivity)
    dsimp [M]
    linarith
  have hV : (M:ℝ)^(-1/6:ℝ) ≤ D.threshold (J-1) k := by
    have hM0 : 0 < (M:ℝ) := by exact_mod_cast (show 0<M by omega)
    have hl0 : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hlM : Real.log L ≤ Real.log (M:ℝ) := Real.log_le_log (by linarith) (by linarith)
    have he := (mrtFrequencyExponent_bounds (by norm_num : (0:ℝ)≤1/12) (J-1)).2
    dsimp only [D,canonicalMellinBands]
    rw [hJid]
    change (M:ℝ)^(-1/6:ℝ) ≤ Real.exp (-mrtFrequencyExponent (1/12) (J-1)*Real.log L)
    rw [Real.rpow_def_of_pos hM0]
    apply Real.exp_le_exp.mpr
    nlinarith
  apply hsamples M hM2 hlogM hMlarge hMsmall
    ((D.primes (J-1)).filter (fun p => D.bin (J-1) p=k)) _ f hf
    (D.threshold (J-1) k) (Real.exp_pos _) hV U hU hsep hlarge
  intro p hp
  obtain ⟨hp,hpk⟩ := mem_filter.mp hp
  have hpprime : p.Prime := mrtPrimeBand_prime hp
  have hb := mrt_log_bin_prime_support hH2 hpprime.one_le
  have hpk' : mrtPrimeLogBin H p=k := by simpa only [D,canonicalMellinBands,hJid,H] using hpk
  rw [hpk'] at hb
  change L ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*L at hb
  refine ⟨hpprime,by linarith,?_⟩
  exact_mod_cast hb.2.trans hMlo

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CanonicalExceptionalSamples
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual no-small-band class has sparse separated samples -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma last_selected_bin_count (P Q η : ℝ) (hQ : 1 ≤ Real.log Q) :
    ∀ᶠ X : ℝ in atTop, let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
      ((canonicalMellinBands P Q η).bins (J-1)).card ≤
        mrtBaseResolution P Q η*(Real.log X)^2+1 := by
  have hJ := (mellinBandCount_tendsto Q hQ).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hJ.eventually (eventually_ge_atTop 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with X hJX hlogX
  let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
  have hJ1 : 1 ≤ J := hJX
  have hJid : J-1+1=J := by omega
  let U := mrtBandUpper Q J
  let H := mrtResolution P Q η J
  have hH0 : 0 ≤ H := (mrtResolution_pos P Q η hJ1).le
  have hU1 : 1 ≤ U := by
    dsimp [U,mrtBandUpper]
    apply Real.one_le_exp
    positivity
  have hsmallU : U ≤ Real.exp (Real.sqrt (Real.log X)) := by
    simpa only [hJid] using mellinBandCount_good Q _ hQ (show J-1<J by omega)
  have hlogU : Real.log U ≤ Real.sqrt (Real.log X) := by
    have hh := Real.log_le_log (by linarith : 0<U) hsmallU
    simpa only [Real.log_exp] using hh
  have hJs : (J:ℝ) ≤ Real.sqrt (Real.log X) :=
    (mrt_band_index_le_log_upper Q J hJ1 hQ).trans hlogU
  have hJsq : (J:ℝ)^2 ≤ Real.log X := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg J) hJs 2
    simpa only [Real.sq_sqrt (by linarith : 0≤Real.log X)] using hh
  have hsqrt : Real.sqrt (Real.log X) ≤ Real.log X := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  have hHle : H ≤ mrtBaseResolution P Q η*Real.log X := by
    dsimp [H,mrtResolution]
    nlinarith [mrtBaseResolution_pos P Q η]
  have hc := mrt_log_bin_card (P := mrtBandLower P Q J) hH0 hU1
  change ((Icc ⌊H*Real.log (mrtBandLower P Q J)⌋₊ ⌊H*Real.log U⌋₊).card:ℝ) ≤
    H*Real.log U+1 at hc
  change (((canonicalMellinBands P Q η).bins (J-1)).card:ℝ) ≤ _
  simp only [canonicalMellinBands,hJid]
  change ((Icc ⌊H*Real.log (mrtBandLower P Q J)⌋₊ ⌊H*Real.log U⌋₊).card:ℝ) ≤ _
  apply hc.trans
  have hb := mul_le_mul hHle (hlogU.trans hsqrt) (Real.log_nonneg hU1)
    (mul_nonneg (mrtBaseResolution_pos P Q η).le (by linarith : 0≤Real.log X))
  nlinarith

theorem canonical_exceptional_samples (P Q : ℝ) (hP : 2*Real.exp 1 ≤ P)
    (hPQ : P ≤ Q) (hlogP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hH : 2 ≤ mrtBaseResolution P Q (1/12)) :
    ∀ᶠ X : ℝ in atTop, let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
      let D := canonicalMellinBands P Q (1/12)
      ∀ f : ℕ → ℂ, OneBounded f → ∀ S : Finset ℝ,
      (∀ t ∈ S, |t| ≤ X) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ S, t ∈ mrtNoSmallBand D.bins (D.polynomial f) D.threshold J) →
      (S.card:ℝ) ≤ (mrtBaseResolution P Q (1/12)*(Real.log X)^2+1)*X^(5/12:ℝ) := by
  filter_upwards [last_band_bin_samples P Q hP hPQ hlogP hQ hH,
    last_selected_bin_count P Q (1/12) hQ, eventually_ge_atTop (1 : ℝ)] with X hbin hcount hX
  let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
  let D := canonicalMellinBands P Q (1/12)
  change 0<J ∧ _ at hbin
  dsimp only
  intro f hf S hS hsep hres
  let E := fun k => S.filter (fun t => D.threshold (J-1) k ≤ ‖D.polynomial f (J-1) k t‖)
  have hcover : S ⊆ (D.bins (J-1)).biUnion E := by
    intro t ht
    obtain ⟨k,hk,hkt⟩ := mrt_no_small_band_large_witness D.bins (D.polynomial f) D.threshold
      (show J-1<J by omega) (hres t ht)
    exact mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨ht,hkt.le⟩⟩
  have hbound (k : ℕ) (hk : k ∈ D.bins (J-1)) : ((E k).card:ℝ) ≤ X^(5/12:ℝ) := by
    apply hbin.2 k hk f hf (E k)
    · intro t ht
      exact hS t (mem_filter.mp ht).1
    · intro x hx y hy hxy
      exact hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy
    · intro t ht
      exact (mem_filter.mp ht).2
  calc
    (S.card:ℝ) ≤ (((D.bins (J-1)).biUnion E).card:ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ ∑ k ∈ D.bins (J-1), ((E k).card:ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _k ∈ D.bins (J-1), X^(5/12:ℝ) := sum_le_sum hbound
    _ = ((D.bins (J-1)).card:ℝ)*X^(5/12:ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by linarith) _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryLargeSamples
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The auxiliary prime polynomial has only sparsely many large samples -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem auxiliary_large_samples (B : ℝ) (_hB : 1 ≤ B) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ a : ℝ in atTop, ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ f : ℕ → ℂ, OneBounded f → ∀ U : Finset ℝ,
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ U, |t| ≤ a^B) →
      (((U.filter (fun t => ((Real.log a)^10)⁻¹ <
        ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
          (fun p => -Real.log (p:ℝ)) t‖)).card):ℝ) ≤ a^γ := by
  let r := ⌈B⌉₊
  obtain ⟨C,hC,hbound⟩ := fixed_prime_moment_large_bound r
  let k : ℕ := 2+10*(2*r)
  have hlim : Tendsto (fun a : ℝ => C*(Real.log a)^k/a^γ) atTop (𝓝 0) := by
    have hh := (log_power_div_power_tendsto_zero (k:ℝ) hγ).const_mul C
    simpa only [Real.rpow_natCast,mul_zero,mul_div_assoc] using hh
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with a ha hsmall
  intro Q hQ f hf U hsep hU
  have ha1 : 1 ≤ a := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans ha
  have hlog : 0 < Real.log a := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    (by simpa using Real.log_le_log (Real.exp_pos 1) ha)
  have hheight : a^B ≤ a^r := by
    have hh := Real.rpow_le_rpow_of_exponent_le ha1 (Nat.le_ceil B)
    simpa only [Real.rpow_natCast] using hh
  let V := ((Real.log a)^10)⁻¹
  let S := U.filter (fun t => V < ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
    (fun p => -Real.log (p:ℝ)) t‖)
  have hh := hbound a ha Q hQ f hf S
    (fun x hx y hy hxy => hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy)
    (fun t ht => (hU t (mem_filter.mp ht).1).trans hheight) V (by dsimp [V] <;> positivity)
    (fun t ht => (mem_filter.mp ht).2.le)
  have he : C*(Real.log a)^2/V^(2*r) = C*(Real.log a)^k := by
    dsimp [V,k]
    rw [inv_pow,div_inv_eq_mul,mul_assoc,← pow_mul,← pow_add]
  apply hh.trans
  rw [he]
  exact (div_le_one (Real.rpow_pos_of_pos (by linarith : 0<a) γ)).mp hsmall

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinLowFrequencyEnergy
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The vanishing low-frequency energy of the actual centered bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

lemma angularMellinPolynomial_continuous (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (angularMellinPolynomial S a) := by
  unfold angularMellinPolynomial
  fun_prop

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_TypicalMellinLowFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The effect of the typical-set cutoff on bounded-frequency energy -/
namespace JointDickman
open Finset MeasureTheory
open scoped Classical

lemma angularMellinPolynomial_sub (S : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    angularMellinPolynomial S (fun n => a n-b n) t =
      angularMellinPolynomial S a t-angularMellinPolynomial S b t := by
  unfold angularMellinPolynomial
  simp_rw [sub_div, sub_mul]
  rw [Finset.sum_sub_distrib]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinRestrictionEnergy
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a sparse arithmetic cutoff in full frequency energy -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

theorem angularMellin_restriction_error_energy (E : ℕ → Prop) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
      (fun n => (if E n then f n else 0)-f n) t‖^2) ≤
      8*Real.exp 1*(T/N+2)*(((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N := by
  classical
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hs : (∑ n ∈ Ioc N (2*N),
      ‖((if E n then f n else 0)-f n)/(n:ℂ)‖^2) ≤
      (((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/(N:ℝ)^2 := by
    calc
      _ ≤ ∑ n ∈ Ioc N (2*N), if ¬E n then (1/(N:ℝ))^2 else 0 := by
        apply sum_le_sum
        intro n hn
        have hnr : 0 < (n:ℝ) := by exact_mod_cast hN.trans (mem_Ioc.mp hn).1
        by_cases he : E n
        · simp [he]
        · simp only [he,ite_false, if_false,not_false_eq_true,ite_true, if_true,zero_sub,norm_div,
            norm_neg,Complex.norm_natCast]
          apply pow_le_pow_left₀ (by positivity)
          exact (div_le_div_of_nonneg_right (hf n) hnr.le).trans
            (one_div_le_one_div_of_le hNr (by exact_mod_cast (mem_Ioc.mp hn).1.le))
      _ = _ := by
        rw [← sum_filter,sum_const,nsmul_eq_mul,div_pow]
        ring
  have hb := mrt_dirichlet_mean_square_subset (Ioc N (2*N)) (N := 2*N) (by
    intro n hn
    exact mem_Ioc.mpr ⟨hN.trans (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2⟩)
    (fun n => ((if E n then f n else 0)-f n)/(n:ℂ)) hT
  change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
    (fun n => (if E n then f n else 0)-f n) t‖^2) ≤ _ at hb
  apply hb.trans
  calc
    _ ≤ 8*Real.exp 1*(T+((2*N:ℕ):ℝ))*
        ((((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by push_cast; field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RamareIntegralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime/cofactor integral with auxiliary large values discharged -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem ramare_product_integral_bound (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in atTop,
      ∀ (N : ℕ) (P Q : Finset ℕ) (F f : ℕ → ℂ),
      1 ≤ a → 2 ≤ (N:ℝ)/a → OneBounded F → OneBounded f →
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ (E : Set ℝ) (T b K : ℝ), MeasurableSet E → 0 ≤ T →
      E ⊆ Set.Ioc (-T) T → 2*T ≤ a^B →
      (∀ U : Finset ℝ, (∀ t ∈ U, t ∈ E) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) → (U.card:ℝ) ≤ K) →
      (∀ t ∈ E, ‖mrtCofactorPolynomial P F N a t‖ ≤ b) →
      (∫ t in E, ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ)) t*mrtCofactorPolynomial P F N a t‖^2) ≤
        2*((((Real.log a)^10)⁻¹)^2*
          (48000*(2*(1+Real.log (2*T+1))+K*Real.sqrt (2*T)*a/N))+
          b^2*(C/(Real.log a)^2)) := by
  obtain ⟨C,γ,hC,hγ,hbound⟩ := ramare_product_sparse_integral_jd B hB
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,auxiliary_large_samples B hB hγ] with a haBound haLarge
  intro N P Q F f ha hx hF hf hQ E T b K hEm hT hET hTB hcard hb
  apply haBound N P Q F f ha hx hF hf hQ E T (((Real.log a)^10)⁻¹) b K
    hEm hT (by positivity) hET hTB
  · intro U hUE hsep
    refine ⟨hcard U hUE hsep,?_⟩
    apply haLarge Q hQ f hf U hsep
    intro t ht
    obtain ⟨hlo,hhi⟩ := hET (hUE t ht)
    have htT : |t| ≤ T := abs_le.mpr ⟨by linarith,by linarith⟩
    exact htT.trans (by linarith)
  · intro t ht _
    exact hb t ht

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinRestrictionRestore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoring the full polynomial after an arithmetic cutoff -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

theorem angularMellin_energy_of_restriction (E : ℕ → Prop) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T)
    {S : Set ℝ} (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤
      2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
        (fun n => if E n then f n else 0) t‖^2)+
      16*Real.exp 1*(T/N+2)*(((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N := by
  classical
  have hs := mrt_restricted_energy_split
    (angularMellinPolynomial (Ioc N (2*N)) f)
    (angularMellinPolynomial (Ioc N (2*N)) (fun n => if E n then f n else 0))
    (angularMellinPolynomial_continuous _ _) (angularMellinPolynomial_continuous _ _) hT.le hS
  have he := angularMellin_restriction_error_energy E f hf hN hT
  simp_rw [angularMellinPolynomial_sub, norm_sub_rev] at he
  calc
    _ ≤ _ := hs
    _ ≤ 2*(8*Real.exp 1*(T/N+2)*
        (((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N)+
        2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
          (fun n => if E n then f n else 0) t‖^2) := by gcongr
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_AuxiliaryBandEnergy
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual auxiliary-band Ramaré products -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

lemma integral_norm_sum_sq_le_card {ι : Type*} (K : Finset ι) (F : ι → ℝ → ℂ)
    (hF : ∀ k ∈ K, Continuous (F k)) {T : ℝ} (hT : 0 ≤ T)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖∑ k ∈ K, F k t‖^2) ≤
      (K.card:ℝ)*∑ k ∈ K, ∫ t in E, ‖F k t‖^2 := by
  have hi k hk := mrt_continuous_square_integrable (hF k hk) hT hE
  calc
    _ ≤ ∫ t in E, (K.card:ℝ)*∑ k ∈ K, ‖F k t‖^2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((integrable_finsetSum K hi).const_mul _)
      intro t _
      exact mrt_norm_sum_sq_le_card K (fun k => F k t)
    _ = _ := by rw [integral_const_mul,integral_finsetSum K hi]

theorem auxiliary_band_energy {κ : Type*} [DecidableEq κ]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, lower (bin p) ≤ p ∧ (p:ℝ) ≤ δ*lower (bin p))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F) t‖^2) ≤
      2816*Real.exp 1*(T/N+1)*
        ((∑ p ∈ P,1/(p:ℝ)^2)+(∑ p ∈ P,1/(p:ℝ)^2)^2+(δ-1))+
      2*(K.card:ℝ)*∑ k ∈ K, ∫ t in E,
        ‖mrtExponentialPolynomial (P.filter (fun p => bin p=k))
          (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t*
          mrtCofactorPolynomial P F N (lower k) t‖^2 := by
  let G : κ → ℝ → ℂ := fun k t =>
    mrtExponentialPolynomial (P.filter (fun p => bin p=k))
      (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t*
      mrtCofactorPolynomial P F N (lower k) t
  have hG k : Continuous (G k) :=
    (mrtExponentialPolynomial_continuous _ _ _).mul (mrtCofactorPolynomial_continuous _ _ _ _)
  have herr := mrt_typical_general_prime_mean_square ({()} : Finset Unit) (fun _ => P)
    (fun _ _ => hP) (by simpa only [coe_singleton] using Set.pairwiseDisjoint_singleton () (fun _ : Unit => P))
    (mem_singleton_self ()) (fun p => lower (bin p)) hN hδ hδ2 hL F hF hFb hT
  have hempty : mrtTypicalCoefficient (∅ : Finset Unit) (fun _ => P) F=F := by
    funext n
    simp [mrtTypicalCoefficient,mrtTypical]
  simp only [Finset.erase_singleton] at herr
  rw [hempty] at herr
  simp_rw [mrt_extracted_prime_bins K P bin hbin lower N F F] at herr
  have hs := mrt_restricted_energy_split
    (angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F))
    (fun t => ∑ k ∈ K,G k t) (angularMellinPolynomial_continuous _ _)
    (continuous_finsetSum K (fun k _ => hG k)) hT.le hE
  have hsum := integral_norm_sum_sq_le_card K G (fun k _ => hG k) hT.le hE
  change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
    (mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F) t-
    ∑ k ∈ K,G k t‖^2) ≤ _ at herr
  change _ ≤ _ + 2*(K.card:ℝ)*∑ k ∈ K, ∫ t in E, ‖G k t‖^2
  linarith

theorem auxiliary_band_full_energy {κ : Type*} [DecidableEq κ]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, lower (bin p) ≤ p ∧ (p:ℝ) ≤ δ*lower (bin p))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : ∀ n, ‖F n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
      5632*Real.exp 1*(T/N+1)*
        ((∑ p ∈ P,1/(p:ℝ)^2)+(∑ p ∈ P,1/(p:ℝ)^2)^2+(δ-1))+
      4*(K.card:ℝ)*(∑ k ∈ K, ∫ t in E,
        ‖mrtExponentialPolynomial (P.filter (fun p => bin p=k))
          (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t*
          mrtCofactorPolynomial P F N (lower k) t‖^2)+
      16*Real.exp 1*(T/N+2)*
        (((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
  classical
  have heq : (fun n => @ite ℂ (¬mrtPrimeAvoids P n) (Classical.propDecidable _) (F n) 0) =
      mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F := by
    funext n
    have hh : mrtTypical ({()} : Finset Unit) (fun _ => P) n ↔ ¬mrtPrimeAvoids P n := by
      simp [mrtTypical,mrtPrimeAvoids]
    by_cases h : mrtPrimeAvoids P n <;> simp [mrtTypicalCoefficient,hh,h]
  have hrestore := angularMellin_energy_of_restriction (fun n => ¬mrtPrimeAvoids P n)
    F hFb hN hT hE
  rw [heq] at hrestore
  simp only [not_not] at hrestore
  have haux := auxiliary_band_energy P hP K bin hbin lower hN hδ hδ2 hL
    F hF (fun n _ => hFb n) hT hE
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_AuxiliaryExceptionalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bound for the full exceptional energy -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem auxiliary_exceptional_energy (P₀ Q₀ B : ℝ)
    (hP₀ : 2*Real.exp 1 ≤ P₀) (hPQ : P₀ ≤ Q₀)
    (hlogP : 1 ≤ Real.log P₀) (hQ₀ : 1 ≤ Real.log Q₀)
    (hH : 2 ≤ mrtBaseResolution P₀ Q₀ (1/12)) (hB : 1 ≤ B) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧ ∀ᶠ X : ℝ in atTop,
      let J := mellinBandCount Q₀ (Real.sqrt (Real.log X)) hQ₀
      let D := canonicalMellinBands P₀ Q₀ (1/12)
      ∀ (N : ℕ) (P K : Finset ℕ) (bin : ℕ → ℕ) (lower : ℕ → ℝ) (δ : ℝ),
      0 < N → (∀ p ∈ P, p.Prime) → (∀ p ∈ P, bin p ∈ K) →
      1 ≤ δ → δ ≤ 2 →
      (∀ p ∈ P, lower (bin p) ≤ p ∧ (p:ℝ) ≤ δ*lower (bin p)) →
      (∀ k ∈ K, A ≤ lower k ∧ 2 ≤ (N:ℝ)/lower k) →
      ∀ (F : ℕ → ℂ), Multiplicative F → (∀ n, ‖F n‖ ≤ 1) →
      ∀ (E : Set ℝ) (T b : ℝ), MeasurableSet E → 0 < T → T ≤ X →
      E ⊆ Set.Ioc (-T) T → E ⊆ mrtNoSmallBand D.bins (D.polynomial F) D.threshold J →
      (∀ k ∈ K, 2*T ≤ (lower k)^B) →
      (∀ k ∈ K, ∀ t ∈ E, ‖mrtCofactorPolynomial P F N (lower k) t‖ ≤ b) →
      (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
        5632*Real.exp 1*(T/N+1)*
          ((∑ p ∈ P,1/(p:ℝ)^2)+(∑ p ∈ P,1/(p:ℝ)^2)^2+(δ-1))+
        8*(K.card:ℝ)*(∑ k ∈ K,
          auxiliarySampleCost C (mrtBaseResolution P₀ Q₀ (1/12)) X N T (lower k) b)+
        16*Real.exp 1*(T/N+2)*
          (((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
  obtain ⟨C,hC,hbound⟩ := ramare_product_integral_bound B hB
  obtain ⟨A,hA⟩ := eventually_atTop.mp hbound
  refine ⟨C,max 1 A,hC,le_max_left _ _,?_⟩
  filter_upwards [canonical_exceptional_samples P₀ Q₀ hP₀ hPQ hlogP hQ₀ hH] with X hX
  dsimp only at hX ⊢
  intro N P K bin lower δ hN hP hbin hδ hδ2 hL hlow F hF hFb E T b
    hEm hT hTX hET hEres hTB hb
  have hfull := auxiliary_band_full_energy P hP K bin hbin lower hN hδ hδ2 hL
    F hF hFb hT hET
  have hsum := sum_le_sum (s := K) (fun k hk => show
      (∫ t in E, ‖mrtExponentialPolynomial (P.filter (fun p => bin p=k))
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t*
        mrtCofactorPolynomial P F N (lower k) t‖^2) ≤
      2*auxiliarySampleCost C (mrtBaseResolution P₀ Q₀ (1/12)) X N T (lower k) b from by
    apply hA (lower k) ((le_max_right 1 A).trans (hlow k hk).1)
      N P (P.filter (fun p => bin p=k)) F F
      ((le_max_left 1 A).trans (hlow k hk).1) (hlow k hk).2
      (fun n _ => hFb n) (fun n _ => hFb n) ?_ E T b
      ((mrtBaseResolution P₀ Q₀ (1/12)*(Real.log X)^2+1)*X^(5/12:ℝ))
      hEm hT.le hET (hTB k hk) ?_ (hb k hk)
    · intro p hp
      obtain ⟨hp,hpk⟩ := mem_filter.mp hp
      have hl := hL p hp
      rw [hpk] at hl
      exact ⟨hP p hp,hl.1,hl.2.trans
        (mul_le_mul_of_nonneg_right hδ2 (by linarith [(hlow k hk).1,le_max_left 1 A]))⟩
    · intro U hUE hsep
      refine hX F (fun n _ => hFb n) U ?_ hsep ?_
      · intro t ht
        obtain ⟨hlo,hhi⟩ := hET (hUE t ht)
        exact (abs_le.mpr ⟨by linarith,by linarith⟩).trans hTX
      · intro t ht
        exact hEres (hUE t ht))
  rw [← mul_sum] at hsum
  have hc : (0:ℝ) ≤ K.card := Nat.cast_nonneg _
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryScalarBounds
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar bounds for summing the auxiliary logarithmic bins -/
namespace JointDickman
open Filter
open scoped Topology

lemma auxiliary_threshold_bounds {v : ℝ} (hv : 1 ≤ v) :
    ((v^10)⁻¹)^2 ≤ 1 ∧ ((v^10)⁻¹)^2 ≤ 1/v^4 := by
  have hv0 : 0 < v := by linarith
  have hp : v^2 ≤ v^10 := pow_le_pow_right₀ hv (by norm_num)
  have hi : (v^10)⁻¹ ≤ (v^2)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr hp
  constructor
  · have h10 : 1 ≤ v^10 := one_le_pow₀ hv
    have h1 : (v^10)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr h10
    nlinarith [inv_nonneg.mpr (pow_nonneg hv0.le 10)]
  · have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (v^10)⁻¹) hi 2
    simpa only [← inv_pow,← pow_mul,one_div] using hh

lemma auxiliary_frequency_log {X T : ℝ} (hX : 1 ≤ Real.log X)
    (hX0 : 0 < X) (hT : 0 ≤ T) (hTX : T ≤ X) :
    2*(1+Real.log (2*T+1)) ≤ 8*Real.log X := by
  have hX1 : 1 ≤ X := by
    have hh := Real.log_le_sub_one_of_pos hX0
    linarith
  have hl := Real.log_le_log (by linarith : 0<2*T+1)
    (show 2*T+1 ≤ 3*X by linarith)
  rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hX0.ne'] at hl
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  nlinarith

lemma auxiliary_exceptional_power {X a β : ℝ} (hX : 0 < X) (ha : 0 ≤ a)
    (hab : a ≤ X^β) :
    X^(5/12:ℝ)*Real.sqrt (2*X)*a/X ≤ 2*X^(β-1/12) := by
  have hs : Real.sqrt (2*X) ≤ 2*X^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hX.le]
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hX.le _)) hab ha
    (by positivity : 0 ≤ X^(5/12:ℝ)*(2*X^(1/2:ℝ)))
  apply (div_le_div_of_nonneg_right hb hX.le).trans_eq
  calc
    _ = 2*(X^(5/12:ℝ)*X^(1/2:ℝ)*X^β/X) := by ring
    _ = 2*X^(β-1/12) := by
      rw [← Real.rpow_add hX,← Real.rpow_add hX,← Real.rpow_sub_one hX.ne']
      congr 2
      ring

lemma eventually_auxiliary_log_lower {α : ℝ} (hα : 0 < α) :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ, Real.exp (-1)*X^α ≤ a →
      1 ≤ Real.log a ∧ (α/2)*Real.log X ≤ Real.log a := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4/α)),
    eventually_gt_atTop (0:ℝ)] with X hlog hX a ha
  have hprod : 0 < Real.exp (-1)*X^α := by positivity
  have hh := Real.log_le_log hprod ha
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hX _).ne',
    Real.log_exp,Real.log_rpow hX] at hh
  have hlarge := (div_le_iff₀ hα).mp hlog
  constructor <;> nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryLogWeights
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic bin-count factors against the prime threshold -/
namespace JointDickman

lemma auxiliary_threshold_log_weight {k L c u v : ℝ}
    (hk0 : 0 ≤ k) (hk : k ≤ L*u) (hc : 0 < c) (hu : 1 ≤ u)
    (hv : 1 ≤ v) (hcv : c*u ≤ v) :
    k^2*((v^10)⁻¹)^2*u ≤ L^2/c^4/u := by
  have hu0 : 0 < u := by linarith
  have hcu : 0 < c*u := mul_pos hc hu0
  have ht := (auxiliary_threshold_bounds hv).2.trans
    (one_div_le_one_div_of_le (pow_pos hcu 4)
      (pow_le_pow_left₀ hcu.le hcv 4))
  calc
    _ ≤ (L*u)^2*(1/(c*u)^4)*u := by gcongr
    _ = _ := by field_simp

lemma auxiliary_cofactor_log_weight {k L c u v : ℝ}
    (hk0 : 0 ≤ k) (hk : k ≤ L*u) (hc : 0 < c) (hu : 1 ≤ u)
    (hcv : c*u ≤ v) : k^2/v^2 ≤ L^2/c^2 := by
  have hu0 : 0 < u := by linarith
  have hcu : 0 < c*u := mul_pos hc hu0
  calc
    _ ≤ (L*u)^2/(c*u)^2 := by gcongr
    _ = _ := by field_simp

lemma auxiliary_cross_log_weight {k L u v H : ℝ}
    (hk0 : 0 ≤ k) (hk : k ≤ L*u) (hu : 1 ≤ u) (hv : 1 ≤ v) (hH : 0 ≤ H) :
    k^2*((v^10)⁻¹)^2*(H*u^2+1) ≤ L^2*(H+1)*u^4 := by
  have hhu : H*u^2+1 ≤ (H+1)*u^2 := by nlinarith
  calc
    _ ≤ (L*u)^2*1*((H+1)*u^2) := by
      gcongr
      exact (auxiliary_threshold_bounds hv).1
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryCostBound
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform scalar envelope for every auxiliary bin -/
namespace JointDickman

theorem auxiliary_cost_bound {N : ℕ} {T a b C H L c β k : ℝ}
    (hN : 0 < (N:ℝ)) (hlog : 1 ≤ Real.log (N:ℝ))
    (hT : 0 ≤ T) (hTN : T ≤ N) (ha : 0 ≤ a) (haβ : a ≤ (N:ℝ)^β)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hv : 1 ≤ Real.log a) (hcv : c*Real.log (N:ℝ) ≤ Real.log a)
    (hk0 : 0 ≤ k) (hk : k ≤ L*Real.log (N:ℝ)) :
    k^2*auxiliarySampleCost C H N N T a b ≤
      48000*(8*L^2/c^4/Real.log (N:ℝ)+
        2*L^2*(H+1)*(Real.log (N:ℝ))^4*(N:ℝ)^(β-1/12))+
      L^2*b^2*C/c^2 := by
  let u := Real.log (N:ℝ)
  let v := Real.log a
  let τ := ((v^10)⁻¹)^2
  have hu : 1 ≤ u := hlog
  have ht0 : 0 ≤ τ := by dsimp [τ] <;> positivity
  have hfreq := auxiliary_frequency_log hlog hN hT hTN
  have hfirst : k^2*τ*(2*(1+Real.log (2*T+1))) ≤ 8*L^2/c^4/u := by
    calc
      _ ≤ k^2*τ*(8*u) := mul_le_mul_of_nonneg_left hfreq (by positivity)
      _ = 8*(k^2*τ*u) := by ring
      _ ≤ 8*(L^2/c^4/u) := mul_le_mul_of_nonneg_left
        (auxiliary_threshold_log_weight hk0 hk hc hu hv hcv) (by norm_num)
      _ = _ := by ring
  have hscale : (N:ℝ)^(5/12:ℝ)*Real.sqrt (2*T)*a/N ≤ 2*(N:ℝ)^(β-1/12) := by
    apply le_trans _ (auxiliary_exceptional_power hN ha haβ)
    gcongr
  have hsecond : k^2*τ*((H*u^2+1)*(N:ℝ)^(5/12:ℝ)*Real.sqrt (2*T)*a/N) ≤
      2*L^2*(H+1)*u^4*(N:ℝ)^(β-1/12) := by
    calc
      _ = (k^2*τ*(H*u^2+1))*((N:ℝ)^(5/12:ℝ)*Real.sqrt (2*T)*a/N) := by ring
      _ ≤ (L^2*(H+1)*u^4)*(2*(N:ℝ)^(β-1/12)) := by
        apply mul_le_mul (auxiliary_cross_log_weight hk0 hk hu hv hH) hscale
        · positivity
        · positivity
      _ = _ := by ring
  have hthird : k^2*(b^2*(C/v^2)) ≤ L^2*b^2*C/c^2 := by
    calc
      _ = b^2*C*(k^2/v^2) := by ring
      _ ≤ b^2*C*(L^2/c^2) := mul_le_mul_of_nonneg_left
        (auxiliary_cofactor_log_weight hk0 hk hc hu hcv) (by positivity)
      _ = _ := by ring
  calc
    _ = 48000*(k^2*τ*(2*(1+Real.log (2*T+1)))+
      k^2*τ*((H*u^2+1)*(N:ℝ)^(5/12:ℝ)*Real.sqrt (2*T)*a/N))+
      k^2*(b^2*(C/v^2)) := by dsimp [auxiliarySampleCost,u,v,τ] <;> ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
      (by norm_num)) hthird

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryCostLimit
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The auxiliary sampling error vanishes after the bin-count loss -/
namespace JointDickman
open Filter
open scoped Topology

lemma auxiliaryVanishingCost_nonneg {H L c β X : ℝ} (hH : 0 ≤ H)
    (hX : 1 ≤ X) : 0 ≤ auxiliaryVanishingCost H L c β X := by
  unfold auxiliaryVanishingCost
  have hl := Real.log_nonneg hX
  positivity

theorem auxiliaryVanishingCost_tendsto (H L c : ℝ) {β : ℝ} (hβ : β < 1/12) :
    Tendsto (auxiliaryVanishingCost H L c β) atTop (𝓝 0) := by
  have hlog := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hp := log_power_div_power_tendsto_zero 4 (show 0 < 1/12-β by linarith)
  have hp' : Tendsto (fun X : ℝ => (Real.log X)^4*X^(β-1/12)) atTop (𝓝 0) := by
    apply hp.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    rw [show β-1/12=-(1/12-β) by ring,Real.rpow_neg hX.le]
    norm_num [div_eq_mul_inv]
  have h1 := hlog.const_mul (8*L^2/c^4)
  have h2 := hp'.const_mul (2*L^2*(H+1))
  have hh := (h1.add h2).const_mul 48000
  unfold auxiliaryVanishingCost
  simpa only [Function.comp_apply,div_eq_mul_inv,mul_assoc,mul_zero,add_zero] using hh

theorem auxiliary_cost_eventually_bound (C H L : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    {α β : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ T a b k : ℝ,
      0 ≤ T → T ≤ N → Real.exp (-1)*(N:ℝ)^α ≤ a → a ≤ (N:ℝ)^β →
      0 ≤ k → k ≤ L*Real.log (N:ℝ) →
      k^2*auxiliarySampleCost C H N N T a b ≤
        auxiliaryVanishingCost H L (α/2) β N+L^2*b^2*C/(α/2)^2 := by
  have hlow := (eventually_auxiliary_log_lower hα).filter_mono tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 1)
  filter_upwards [hlow,hlog,eventually_gt_atTop (0:ℕ)] with N hlow hlog hN
  intro T a b k hT hTN ha haβ hk0 hk
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hh := hlow a ha
  have ha0 : 0 ≤ a := le_trans (by positivity : 0 ≤ Real.exp (-1)*(N:ℝ)^α) ha
  exact auxiliary_cost_bound hn hlog hT hTN ha0 haβ hC hH
    (by positivity : 0<α/2) hh.1 hh.2 hk0 hk

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryCostSum
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the auxiliary costs without an extra logarithmic loss -/
namespace JointDickman
open Finset Filter
open scoped Classical Topology

lemma card_mul_sum_le_of_square {ι : Type*} (K : Finset ι) (F : ι → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hF : ∀ k ∈ K, (K.card:ℝ)^2*F k ≤ R) :
    (K.card:ℝ)*(∑ k ∈ K,F k) ≤ R := by
  by_cases hK : K.Nonempty
  · have hc : (0:ℝ)<K.card := by exact_mod_cast hK.card_pos
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      _ = ∑ k ∈ K,(K.card:ℝ)^2*F k := by rw [← mul_sum]; ring
      _ ≤ ∑ _k ∈ K,R := sum_le_sum hF
      _ = _ := by simp
  · have he : K=∅ := not_nonempty_iff_eq_empty.mp hK
    simpa only [he,card_empty,Nat.cast_zero,zero_mul] using hR

theorem auxiliary_cost_sum_bound (C H L : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    {α β : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : Finset ℕ) (a : ℕ → ℝ) (T b : ℝ),
      (K.card:ℝ) ≤ L*Real.log (N:ℝ) → 0 ≤ T → T ≤ N →
      (∀ k ∈ K, Real.exp (-1)*(N:ℝ)^α ≤ a k ∧ a k ≤ (N:ℝ)^β) →
      (K.card:ℝ)*(∑ k ∈ K,auxiliarySampleCost C H N N T (a k) b) ≤
        auxiliaryVanishingCost H L (α/2) β N+L^2*b^2*C/(α/2)^2 := by
  filter_upwards [auxiliary_cost_eventually_bound C H L hC hH hα,
    eventually_ge_atTop (1:ℕ)] with N hN hN1
  intro K a T b hK hT hTN ha
  apply card_mul_sum_le_of_square K _
  · exact add_nonneg (auxiliaryVanishingCost_nonneg hH (by exact_mod_cast hN1))
      (by positivity)
  · intro k hk
    exact hN T (a k) b K.card hT hTN (ha k hk).1 (ha k hk).2 (by positivity) hK

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryLogBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual logarithmic bins in a fixed power auxiliary band -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

lemma auxiliary_log_bins_card {H α β X : ℝ} (hH : 0 ≤ H)
    (hβ : 0 ≤ β) (hX : 0 < X) (hlog : 1 ≤ Real.log X) :
    ((auxiliaryLogBins H α β X).card:ℝ) ≤ (H*β+1)*Real.log X := by
  have hX1 : 1 ≤ X := by linarith [Real.log_le_sub_one_of_pos hX]
  have hQ : 1 ≤ X^β := Real.one_le_rpow hX1 hβ
  have hh := mrt_log_bin_card (P := X^α) hH hQ
  change ((auxiliaryLogBins H α β X).card:ℝ) ≤ _ at hh
  rw [Real.log_rpow hX] at hh
  nlinarith

lemma auxiliary_log_bins_endpoints {H α β X : ℝ} (hH : 1 ≤ H)
    (hβ : 0 ≤ β) (hX : 1 ≤ X) {k : ℕ} (hk : k ∈ auxiliaryLogBins H α β X) :
    Real.exp (-1)*X^α ≤ mrtPrimeLogLower H k ∧ mrtPrimeLogLower H k ≤ X^β := by
  exact mrt_log_bin_endpoints hH (Real.rpow_pos_of_pos (by linarith) _)
    (Real.one_le_rpow hX hβ) hk

lemma auxiliary_log_bins_mem {H α β X : ℝ} (hH : 0 ≤ H) (hX : 0 < X)
    {p : ℕ} (hp : p ∈ mrtPrimeBand (X^α) (X^β)) :
    mrtPrimeLogBin H p ∈ auxiliaryLogBins H α β X := by
  have ha := Real.rpow_pos_of_pos hX α
  have hb := Real.rpow_pos_of_pos hX β
  have hh := mrtPrimeBand_bounds ha.le hb.le hp
  exact mrt_prime_log_bin_range hH ha hh.1.le hh.2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryRangeScales
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform size bounds throughout the auxiliary power band -/
namespace JointDickman
open Filter
open scoped Topology

theorem auxiliary_range_scales (A : ℝ) {α β : ℝ} (hα : 0 < α) (hβ : β < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ,
      Real.exp (-1)*(N:ℝ)^α ≤ a → a ≤ (N:ℝ)^β →
      A ≤ a ∧ 1 ≤ a ∧ 2 ≤ (N:ℝ)/a ∧ 2*(N:ℝ) ≤ a^(4/α) := by
  have hgrow := ((tendsto_rpow_atTop hα).const_mul_atTop (Real.exp_pos (-1))).comp
    tendsto_natCast_atTop_atTop
  have hratio := (tendsto_rpow_atTop (show 0<1-β by linarith)).comp
    tendsto_natCast_atTop_atTop
  have hlog := (eventually_auxiliary_log_lower hα).filter_mono tendsto_natCast_atTop_atTop
  filter_upwards [hgrow.eventually (eventually_ge_atTop (max A 1)),
    hratio.eventually (eventually_ge_atTop 2),hlog,eventually_ge_atTop (2:ℕ)] with
    N hA hr hlog hN a ha haβ
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) hN
  have ha1 : 1 ≤ a := (le_max_right A 1).trans (hA.trans ha)
  have ha0 : 0 < a := by linarith
  have htwo : 2*(N:ℝ)^β ≤ N := by
    calc
      _ ≤ (N:ℝ)^(1-β)*(N:ℝ)^β := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by rw [← Real.rpow_add hn]; norm_num
  have hlogA := (hlog a ha).2
  have hpow : (N:ℝ)^2 ≤ a^(4/α) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos hn,Real.rpow_def_of_pos ha0]
    apply Real.exp_le_exp.mpr
    calc
      _ = (4/α)*((α/2)*Real.log (N:ℝ)) := by field_simp <;> ring
      _ ≤ (4/α)*Real.log a := mul_le_mul_of_nonneg_left hlogA (by positivity)
      _ = _ := mul_comm _ _
  refine ⟨(le_max_left A 1).trans (hA.trans ha),ha1,?_,?_⟩
  · apply (le_div_iff₀ ha0).mpr
    linarith
  · apply le_trans _ hpow
    have hn2 : (2:ℝ)≤N := by exact_mod_cast hN
    nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeBandExtractionCost
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summability of all prime-square and width errors in the MRT bands -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma primeBand_square_mass_le {L U : ℝ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    (∑ p ∈ mrtPrimeBand L U, 1 / (p : ℝ)^2) ≤ 2/L := by
  have hL0 : 0 < L := by linarith
  have hM : 0 < ⌊L⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hMN : ⌊L⌋₊ ≤ ⌊U⌋₊ := Nat.floor_mono hLU
  have hsub : mrtPrimeBand L U ⊆ Ioc ⌊L⌋₊ ⌊U⌋₊ := by
    intro p hp
    have hh := mrtPrimeBand_bounds hL0.le (hL0.le.trans hLU) hp
    exact mem_Ioc.mpr ⟨(Nat.floor_lt hL0.le).mpr hh.1,
      (Nat.le_floor_iff (hL0.le.trans hLU)).mpr hh.2⟩
  have hs : (∑ p ∈ mrtPrimeBand L U, 1 / (p : ℝ)^2) ≤ (⌊L⌋₊ : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ p ∈ Ioc ⌊L⌋₊ ⌊U⌋₊, 1 / (p : ℝ)^2 :=
        sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ ≤ (⌊L⌋₊ : ℝ)⁻¹ - (⌊U⌋₊ : ℝ)⁻¹ := by
        simpa only [one_div] using sum_Ioc_inv_sq_le_sub (α := ℝ) hM.ne' hMN
      _ ≤ _ := sub_le_self _ (by positivity)
  apply hs.trans
  rw [← one_div]
  apply (div_le_div_iff₀ (by exact_mod_cast hM) hL0).mpr
  have hh := Nat.lt_floor_add_one L
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_AuxiliaryPowerEnergy
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exceptional energy on an actual power-scale auxiliary band -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

lemma auxiliarySquareError_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (auxiliarySquareError α) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hα)).const_mul 2
  have hh := (h.add (h.pow 2)).const_mul (11264*Real.exp 1)
  unfold auxiliarySquareError
  simpa only [Function.comp_apply,div_eq_mul_inv,mul_zero,
    zero_pow (by omega : (2:ℕ)≠0),add_zero] using hh

theorem auxiliary_power_energy_jd_oai (P₀ Q₀ H : ℝ)
    (hP₀ : 2*Real.exp 1 ≤ P₀) (hPQ : P₀ ≤ Q₀)
    (hlogP : 1 ≤ Real.log P₀) (hQ₀ : 1 ≤ Real.log Q₀)
    (hH₀ : 2 ≤ mrtBaseResolution P₀ Q₀ (1/12)) (hH : 2 ≤ H)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < 1/12) :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      let P := mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)
      let K := auxiliaryLogBins H α β N
      let J := mellinBandCount Q₀ (Real.sqrt (Real.log (N:ℝ))) hQ₀
      let B := canonicalMellinBands P₀ Q₀ (1/12)
      ∀ (F : ℕ → ℂ), Multiplicative F → (∀ n, ‖F n‖ ≤ 1) →
      ∀ (E : Set ℝ) (T b : ℝ), MeasurableSet E → 0 < T → T ≤ N →
      E ⊆ Set.Ioc (-T) T → E ⊆ mrtNoSmallBand B.bins (B.polynomial F) B.threshold J →
      (∀ k ∈ K, ∀ t ∈ E, ‖mrtCofactorPolynomial P F N (mrtPrimeLogLower H k) t‖ ≤ b) →
      (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
        ε+22528*Real.exp 1/H+D*b^2+
        48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
  have hB : 1 ≤ 4/α := (le_div_iff₀ hα).mpr (by linarith)
  obtain ⟨C,A,hC,hA,henergy⟩ := auxiliary_exceptional_energy P₀ Q₀ (4/α)
    hP₀ hPQ hlogP hQ₀ hH₀ hB
  let L := H*β+1
  have hL : 0 < L := by dsimp [L] <;> nlinarith
  let D := 8*L^2*C/(α/2)^2
  refine ⟨D,by dsimp [D] <;> positivity,?_⟩
  intro ε hε
  have herr := (auxiliarySquareError_tendsto hα).add
    ((auxiliaryVanishingCost_tendsto (mrtBaseResolution P₀ Q₀ (1/12)) L (α/2) hβ).const_mul 8)
  simp only [mul_zero,add_zero] at herr
  have hevent := henergy.filter_mono tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 1)
  have hprime := ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 2)
  have hsmall := (herr.eventually (eventually_lt_nhds hε)).filter_mono tendsto_natCast_atTop_atTop
  filter_upwards [hevent,auxiliary_range_scales A hα (show β<1 by linarith),
    auxiliary_cost_sum_bound C (mrtBaseResolution P₀ Q₀ (1/12)) L hC.le
      (mrtBaseResolution_pos _ _ _).le hα,hlog,hprime,hsmall,
    eventually_ge_atTop (2:ℕ)] with N hevent hrange hcost hlog hprime hsmall hN
  dsimp only at hevent ⊢
  intro F hF hFb E T b hEm hT hTN hET hEres hb
  let P := mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)
  let K := auxiliaryLogBins H α β N
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast le_trans (by norm_num : 1≤2) hN
  have heps := mrt_prime_log_width hH
  have hend k (hk : k∈K) := auxiliary_log_bins_endpoints (show 1≤H by linarith)
    (show 0≤β by linarith) hn1 hk
  have hr k (hk : k∈K) := hrange (mrtPrimeLogLower H k) (hend k hk).1 (hend k hk).2
  have hbound := hevent N P K (mrtPrimeLogBin H) (mrtPrimeLogLower H) (Real.exp (1/H))
    (by omega) (fun _ hp => mrtPrimeBand_prime hp)
    (fun _ hp => auxiliary_log_bins_mem (by linarith) hn hp) heps.1 heps.2.1
    (fun p hp => mrt_prime_log_bin_bounds (by linarith) (mrtPrimeBand_prime hp).one_le)
    (fun k hk => ⟨(hr k hk).1,(hr k hk).2.2.1⟩) F hF hFb E T b hEm hT hTN hET hEres
    (fun k hk => (show 2*T≤2*(N:ℝ) by linarith).trans (hr k hk).2.2.2) hb
  have hc := hcost K (mrtPrimeLogLower H) T b
    (auxiliary_log_bins_card (by linarith) (show 0≤β by linarith) hn hlog) hT.le hTN hend
  have hpq : (N:ℝ)^α ≤ (N:ℝ)^β := Real.rpow_le_rpow_of_exponent_le hn1 hαβ
  have hs := primeBand_square_mass_le hprime hpq
  change (∑ p ∈ P,1/(p:ℝ)^2) ≤ 2/(N:ℝ)^α at hs
  have hs0 : 0 ≤ ∑ p ∈ P,1/(p:ℝ)^2 := sum_nonneg (fun _ _ => by positivity)
  have hratio : T/(N:ℝ) ≤ 1 := (div_le_one hn).mpr hTN
  have hbase : 5632*Real.exp 1*(T/N+1)*
      ((∑ p ∈ P,1/(p:ℝ)^2)+(∑ p ∈ P,1/(p:ℝ)^2)^2+(Real.exp (1/H)-1)) ≤
      auxiliarySquareError α N+22528*Real.exp 1/H := by
    calc
      _ ≤ 11264*Real.exp 1*(2/(N:ℝ)^α+(2/(N:ℝ)^α)^2+2/H) := by
        apply mul_le_mul
        · calc
            _ ≤ 5632*Real.exp 1*2 := mul_le_mul_of_nonneg_left
              (by linarith only [hratio]) (by positivity)
            _ = _ := by ring
        · exact add_le_add (add_le_add hs (pow_le_pow_left₀ hs0 hs 2)) heps.2.2
        · exact add_nonneg (add_nonneg hs0 (sq_nonneg _)) (sub_nonneg.mpr heps.1)
        · positivity
      _ = _ := by dsimp [auxiliarySquareError] <;> ring
  have hbad : 16*Real.exp 1*(T/N+2)*
      (((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N ≤
      48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
    have hcoef : 16*Real.exp 1*(T/N+2) ≤ 48*Real.exp 1 := by
      calc
        _ ≤ 16*Real.exp 1*3 := mul_le_mul_of_nonneg_left
          (by linarith only [hratio]) (by positivity)
        _ = _ := by ring
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)) hn.le
  have hmul := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤8)
  change (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
    ε+22528*Real.exp 1/H+D*b^2+
      48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N
  change auxiliarySquareError α N+
    8*auxiliaryVanishingCost (mrtBaseResolution P₀ Q₀ (1/12)) L (α/2) β N<ε at hsmall
  calc
    _ ≤ _ := hbound
    _ ≤ (auxiliarySquareError α N+22528*Real.exp 1/H)+
        8*(auxiliaryVanishingCost (mrtBaseResolution P₀ Q₀ (1/12)) L (α/2) β N+
          L^2*b^2*C/(α/2)^2)+
        48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N :=
      add_le_add (add_le_add hbase (by simpa only [mul_assoc] using hmul)) hbad
    _ = (auxiliarySquareError α N+
        8*auxiliaryVanishingCost (mrtBaseResolution P₀ Q₀ (1/12)) L (α/2) β N)+
        22528*Real.exp 1/H+D*b^2+
        48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
      dsimp only [D]
      ring
    _ ≤ _ := by gcongr

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.auxiliary_power_energy_jd_oai := @OAI.JointDickman.auxiliary_power_energy_jd_oai
