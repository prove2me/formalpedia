-- Prove2me | solution 1 for OAI.JointDickman.canonical_full_energy_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:27:22.237178+00:00
-- url     : https://prove2.me/submissions/46a7c2c5-7fb0-4069-84e9-e2300e27a96f

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003

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
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTDivisorPairs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The divisor-square estimate in the mixed prime/cofactor moment.
The map `(d,e) ↦ (gcd(d,e), d/gcd(d,e), e/gcd(d,e))` bounds a pair of
supported divisors by three supported factors whose product divides the
integer. Summing the divisibility tests gives a finite Euler majorant. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_gcd_triple_left (v : ℕ × ℕ) :
    (mrtGcdTriple v).1 * (mrtGcdTriple v).2.1 = v.1 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

lemma mrt_gcd_triple_right (v : ℕ × ℕ) :
    (mrtGcdTriple v).1 * (mrtGcdTriple v).2.2 = v.2 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

lemma mrt_gcd_triple_injective : Function.Injective mrtGcdTriple := by
  intro v w h
  apply Prod.ext
  · rw [← mrt_gcd_triple_left v, ← mrt_gcd_triple_left w, h]
  · rw [← mrt_gcd_triple_right v, ← mrt_gcd_triple_right w, h]

lemma mrt_gcd_triple_product {d e : ℕ} (hd : 0 < d) :
    (mrtGcdTriple (d, e)).1 *
      ((mrtGcdTriple (d, e)).2.1 * (mrtGcdTriple (d, e)).2.2) = Nat.lcm d e := by
  change Nat.gcd d e * (d / Nat.gcd d e * (e / Nat.gcd d e)) = _
  apply Nat.eq_of_mul_eq_mul_left (Nat.gcd_pos_of_pos_left e hd)
  calc
    _ = (Nat.gcd d e * (d / Nat.gcd d e)) *
        (Nat.gcd d e * (e / Nat.gcd d e)) := by ring
    _ = d * e := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
    _ = Nat.gcd d e * Nat.lcm d e := (Nat.gcd_mul_lcm d e).symm

/-- A finite divisor-closed positive set suffices; no asymptotic sieve
or mean-value theorem is hidden in the combinatorial estimate. -/
theorem mrt_divisor_pair_card (S : Finset ℕ)
    (hS : ∀ d ∈ S, 0 < d)
    (hclosed : ∀ d ∈ S, ∀ e : ℕ, 0 < e → e ∣ d → e ∈ S) (n : ℕ) :
    ((S.filter (fun d => d ∣ n)).card) ^ 2 ≤
      ((S ×ˢ (S ×ˢ S)).filter (fun v => v.1 * (v.2.1 * v.2.2) ∣ n)).card := by
  let D := S.filter (fun d => d ∣ n)
  have hm : ∀ v ∈ D ×ˢ D,
      mrtGcdTriple v ∈ (S ×ˢ (S ×ˢ S)).filter
        (fun w => w.1 * (w.2.1 * w.2.2) ∣ n) := by
    rintro ⟨d, e⟩ hv
    obtain ⟨hd, he⟩ := mem_product.mp hv
    obtain ⟨hdS, hdn⟩ := mem_filter.mp hd
    obtain ⟨heS, hen⟩ := mem_filter.mp he
    have hd0 := hS d hdS
    have he0 := hS e heS
    have hg0 := Nat.gcd_pos_of_pos_left e hd0
    have hgd := Nat.gcd_dvd_left d e
    have hge := Nat.gcd_dvd_right d e
    have hqd : 0 < d / Nat.gcd d e := Nat.div_pos (Nat.le_of_dvd hd0 hgd) hg0
    have hqe : 0 < e / Nat.gcd d e := Nat.div_pos (Nat.le_of_dvd he0 hge) hg0
    apply mem_filter.mpr
    constructor
    · exact mem_product.mpr ⟨hclosed d hdS _ hg0 hgd, mem_product.mpr
        ⟨hclosed d hdS _ hqd (Nat.div_dvd_of_dvd hgd),
          hclosed e heS _ hqe (Nat.div_dvd_of_dvd hge)⟩⟩
    · rw [mrt_gcd_triple_product hd0]
      exact Nat.lcm_dvd hdn hen
  have hc := card_le_card_of_injOn mrtGcdTriple hm
    (fun _ _ _ _ h => mrt_gcd_triple_injective h)
  simpa only [card_product, pow_two] using hc

theorem mrt_divisor_count_second_moment (S : Finset ℕ)
    (hS : ∀ d ∈ S, 0 < d)
    (hclosed : ∀ d ∈ S, ∀ e : ℕ, 0 < e → e ∣ d → e ∈ S) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((S.filter (fun d => d ∣ n)).card : ℝ) ^ 2) ≤
      (N : ℝ) * (∑ d ∈ S, 1 / (d : ℝ)) ^ 3 := by
  let K := S ×ˢ (S ×ˢ S)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ v ∈ K,
        if v.1 * (v.2.1 * v.2.2) ∣ n then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro n _
      have hc := mrt_divisor_pair_card S hS hclosed n
      have hcR : ((S.filter (fun d => d ∣ n)).card : ℝ) ^ 2 ≤
          (((S ×ˢ (S ×ˢ S)).filter
            (fun v => v.1 * (v.2.1 * v.2.2) ∣ n)).card : ℝ) := by exact_mod_cast hc
      simpa only [sum_boole] using hcR
    _ = ∑ v ∈ K, ∑ n ∈ Icc 1 N,
        if v.1 * (v.2.1 * v.2.2) ∣ n then (1 : ℝ) else 0 := sum_comm
    _ ≤ ∑ v ∈ K, (N : ℝ) / (v.1 * (v.2.1 * v.2.2) : ℕ) := by
      apply sum_le_sum
      intro v hv
      obtain ⟨h1, h23⟩ := mem_product.mp hv
      obtain ⟨h2, h3⟩ := mem_product.mp h23
      rw [mrt_count_multiples (Nat.mul_pos (hS _ h1) (Nat.mul_pos (hS _ h2) (hS _ h3)))]
      exact Nat.cast_div_le
    _ = (N : ℝ) * (∑ d ∈ S, 1 / (d : ℝ)) ^ 3 := by
      simp only [K, sum_product, Nat.cast_mul, ← div_div]
      simp_rw [div_eq_mul_inv]
      simp only [← mul_sum, ← sum_mul]
      ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTEulerProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped BigOperators ComplexConjugate

lemma mrt_local_euler_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - z)⁻¹‖ ≤ Real.exp (z.re + ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hnz : 1 - z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp only [he, norm_one] at hz1
    exact lt_irrefl _ hz1
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)).mpr
    linarith
  have hrem : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hre : (Complex.log (1 - z)⁻¹).re ≤ z.re + ‖z‖ ^ 2 := by
    have h := (Complex.re_le_norm (Complex.log (1 - z)⁻¹ - z)).trans hrem
    rw [Complex.sub_re] at h
    linarith
  calc
    _ = Real.exp (Complex.log (1 - z)⁻¹).re := by
      rw [← Complex.norm_exp, Complex.exp_log (inv_ne_zero hnz)]
    _ ≤ _ := Real.exp_le_exp.mpr hre

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFactoredReciprocal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite reciprocal mass of integers supported on a prime band. Together
with the gcd-triple injection this supplies the divisor-square mean bound
in MR's mixed prime/cofactor moment without an additional sieve input. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrtFactoredUpTo_pos (P : Finset ℕ) (N : ℕ)
    {d : ℕ} (hd : d ∈ mrtFactoredUpTo P N) : 0 < d :=
  (mem_Icc.mp (mem_filter.mp hd).1).1

lemma mrtFactoredUpTo_divisor_closed (P : Finset ℕ) (N : ℕ)
    {d : ℕ} (hd : d ∈ mrtFactoredUpTo P N)
    {e : ℕ} (he : 0 < e) (hed : e ∣ d) : e ∈ mrtFactoredUpTo P N := by
  obtain ⟨hdN, hdP⟩ := mem_filter.mp hd
  exact mem_filter.mpr ⟨mem_Icc.mpr
    ⟨he, (Nat.le_of_dvd (mem_Icc.mp hdN).1 hed).trans (mem_Icc.mp hdN).2⟩,
    Nat.mem_factoredNumbers_of_dvd hdP hed⟩

lemma mrt_reciprocal_prime_power_series {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => (1 : ℝ) / (p ^ k : ℕ)) (1 - (1 : ℝ) / p)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
  simpa only [Nat.cast_pow, one_div, inv_pow] using
    hasSum_geometric_of_lt_one (by positivity : 0 ≤ (p : ℝ)⁻¹) hi

lemma mrt_reciprocal_prime_power_norm {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => ‖(1 : ℝ) / (p ^ k : ℕ)‖) := by
  have he (k : ℕ) : ‖(1 : ℝ) / (p ^ k : ℕ)‖ = 1 / (p ^ k : ℕ) :=
    Real.norm_of_nonneg (by positivity)
  simpa only [he] using (mrt_reciprocal_prime_power_series hp).summable

lemma mrt_factored_reciprocal_series (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers P => (1 : ℝ) / (n.val : ℕ))
      (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) := by
  have h1 : (1 : ℝ) / (1 : ℕ) = 1 := by norm_num
  have hm {m n : ℕ} (_h : m.Coprime n) :
      (1 : ℝ) / (m * n : ℕ) = (1 / (m : ℝ)) * (1 / (n : ℝ)) := by
    simp only [Nat.cast_mul, one_div, mul_inv_rev]
    ring
  obtain ⟨_, he⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (1 : ℝ) / n) h1 (fun {_ _} h => hm h)
    (fun {_} h => mrt_reciprocal_prime_power_norm h) P
  have hf : P.filter Nat.Prime = P := filter_true_of_mem hP
  rw [hf] at he
  have hprod : (∏ p ∈ P, ∑' k : ℕ, (1 : ℝ) / (p ^ k : ℕ)) =
      ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ :=
    prod_congr rfl (fun p hp => (mrt_reciprocal_prime_power_series (hP p hp)).tsum_eq)
  exact hprod ▸ he

theorem mrt_factored_reciprocal_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ d ∈ mrtFactoredUpTo P N, 1 / (d : ℝ)) ≤
      ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := by
  have hi : HasSum ((Nat.factoredNumbers P).indicator (fun n : ℕ => (1 : ℝ) / n))
      (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) :=
    (hasSum_subtype_iff_indicator (s := Nat.factoredNumbers P)
      (f := fun n : ℕ => (1 : ℝ) / n)).mp (mrt_factored_reciprocal_series P hP)
  rw [← hi.tsum_eq]
  calc
    _ = ∑ d ∈ mrtFactoredUpTo P N,
        (Nat.factoredNumbers P).indicator (fun n : ℕ => (1 : ℝ) / n) d := by
      apply sum_congr rfl
      intro d hd
      exact (Set.indicator_of_mem (mem_filter.mp hd).2 (fun n : ℕ => (1 : ℝ) / n)).symm
    _ ≤ _ := hi.summable.sum_le_tsum _ (fun d _ =>
      Set.indicator_nonneg (fun n _ => by positivity) d)

lemma mrt_prime_reciprocal_euler_bound {p : ℕ} (hp : p.Prime) :
    (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hnon : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hhalf : (1 : ℝ) / p ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hp2
  have hz : ‖(((1 : ℝ) / p : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnon] using hhalf
  have he := mrt_local_euler_bound hz
  have hpos : 0 < 1 - (1 : ℝ) / p := by linarith
  have hn : ‖(1 - (((1 : ℝ) / p : ℝ) : ℂ))⁻¹‖ = (1 - (1 : ℝ) / p)⁻¹ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (1 - (1 : ℝ) / p)⁻¹)]
  simpa only [hn, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnon] using he

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

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTPrimeMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMixedCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients of a prime-polynomial power times a cofactor polynomial.
The cofactor may carry arbitrary bounded masks. Unique factorization costs
only the prime-tuple factorial; the remaining multiplicity is the literal
number of supported divisors, controlled by its second moment. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_prime_tuple_factored {r : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (v : Fin r → ℕ)
    (hv : v ∈ Fintype.piFinset (fun _ : Fin r => P)) :
    (∏ i, v i) ∈ Nat.factoredNumbers P := by
  apply Nat.mem_factoredNumbers'.mpr
  intro p hp hdiv
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff v).mp hdiv
  have hvi := Fintype.mem_piFinset.mp hv i
  have he := (Nat.prime_dvd_prime_iff_eq hp (hP _ hvi)).mp hi
  exact he.symm ▸ hvi

theorem mrt_mixed_prime_fiber_card (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ) {n U : ℕ} (hn : 0 < n) (hnU : n ≤ U) :
    (mrtMixedPrimeFiber P M r n).card ≤ r.factorial *
      (((mrtFactoredUpTo P U).filter (fun d => d ∣ n)).card) := by
  let V := Fintype.piFinset (fun _ : Fin r => P)
  let S := mrtMixedPrimeFiber P M r n
  let D := (mrtFactoredUpTo P U).filter (fun d => d ∣ n)
  have htuple (v : Fin r → ℕ) (hv : v ∈ V) : 0 < ∏ i, v i :=
    prod_pos (fun i _ => (hP _ (Fintype.mem_piFinset.mp hv i)).pos)
  have hmap : ∀ v ∈ S, (∏ i, v.1 i) ∈ D := by
    intro v hv
    obtain ⟨hvm, hprod⟩ := mem_filter.mp hv
    obtain ⟨hvP, _⟩ := mem_product.mp hvm
    have hd : (∏ i, v.1 i) ∣ n := hprod ▸ dvd_mul_right _ _
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr
      ⟨htuple _ hvP, (Nat.le_of_dvd hn hd).trans hnU⟩,
      mrt_prime_tuple_factored P hP v.1 hvP⟩, hd⟩
  have hfiber (d : ℕ) : (S.filter (fun v => (∏ i, v.1 i) = d)).card ≤ r.factorial := by
    apply le_trans (card_le_card_of_injOn Prod.fst ?_ ?_)
      (mrt_prime_product_fiber_card V (fun v hv i =>
        hP _ (Fintype.mem_piFinset.mp hv i)) d)
    · intro v hv
      obtain ⟨hvS, hvd⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨(mem_product.mp (mem_filter.mp hvS).1).1, hvd⟩
    · intro v hv w hw he
      obtain ⟨hvS, _⟩ := mem_filter.mp hv
      obtain ⟨hwS, _⟩ := mem_filter.mp hw
      have hvp := (mem_filter.mp hvS).2
      have hwp := (mem_filter.mp hwS).2
      apply Prod.ext he
      apply Nat.eq_of_mul_eq_mul_left
        (htuple v.1 (mem_product.mp (mem_filter.mp hvS).1).1)
      calc
        _ = n := hvp
        _ = _ := by rw [he]; exact hwp.symm
  have hcount : (∑ d ∈ D, (S.filter (fun v => (∏ i, v.1 i) = d)).card) = S.card := by
    simpa using (sum_fiberwise_of_maps_to hmap (fun _ => (1 : ℕ)))
  rw [← hcount]
  calc
    _ ≤ ∑ _d ∈ D, r.factorial := sum_le_sum (fun d _ => hfiber d)
    _ = _ := by simp [D, Nat.mul_comm]

theorem mrt_mixed_prime_coefficient_bound (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {n U : ℕ} (hn : 0 < n) (hnU : n ≤ U) :
    ‖mrtMixedPrimeCoefficient P M a b r n‖ ≤ (r.factorial : ℝ) *
      (((mrtFactoredUpTo P U).filter (fun d => d ∣ n)).card : ℝ) := by
  have ht (v : (Fin r → ℕ) × ℕ) (hv : v ∈ mrtMixedPrimeFiber P M r n) :
      ‖(∏ i, a (v.1 i)) * b v.2‖ ≤ 1 := by
    obtain ⟨hvm, _⟩ := mem_filter.mp hv
    obtain ⟨hvP, hvM⟩ := mem_product.mp hvm
    rw [norm_mul, norm_prod]
    have hp : (∏ i, ‖a (v.1 i)‖) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun i _ => ha _ (Fintype.mem_piFinset.mp hvP i))
    exact (mul_le_mul hp (hb _ hvM) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  calc
    _ ≤ ∑ _v ∈ mrtMixedPrimeFiber P M r n, (1 : ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum ht)
    _ = ((mrtMixedPrimeFiber P M r n).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast mrt_mixed_prime_fiber_card P M hP r hn hnU

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTWeightedTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial summation of the supported-divisor second moment. This keeps
the mixed Dirichlet coefficient square mass proportional to the inverse
lower endpoint, rather than losing the ratio of its endpoints. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_real_prefix_zero_extension (a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range (n + 1), if i = 0 then 0 else a i) = ∑ i ∈ Icc 1 n, a i := by
  rw [Nat.range_succ_eq_Icc_zero, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp only [ite_true, if_true, zero_add]
  have he : Ioc 0 n = Icc 1 n := by ext i; simp only [mem_Ioc, mem_Icc]; omega
  rw [he]
  apply sum_congr rfl
  intro i hi
  rw [ite_eq_right (by have := (mem_Icc.mp hi).1; omega)]

lemma mrt_square_reciprocal_partial_sum (a : ℕ → ℝ) {m n : ℕ} (hmn : m < n) :
    (∑ i ∈ Ioc m n, a i / (i : ℝ) ^ 2) =
      (∑ i ∈ Icc 1 n, a i) / (n : ℝ) ^ 2 -
      (∑ i ∈ Icc 1 m, a i) / (m + 1 : ℕ) ^ 2 +
      ∑ i ∈ Ioc m (n - 1), (∑ j ∈ Icc 1 i, a j) *
        (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) := by
  have he := sum_Ioc_by_parts (fun i : ℕ => (1 : ℝ) / (i : ℝ) ^ 2)
    (fun i : ℕ => if i = 0 then 0 else a i) hmn
  simp only [smul_eq_mul, mrt_real_prefix_zero_extension] at he
  have hl : (∑ i ∈ Ioc m n, 1 / (i : ℝ) ^ 2 * (if i = 0 then 0 else a i)) =
      ∑ i ∈ Ioc m n, a i / (i : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro i hi
    rw [ite_eq_right (by have := (mem_Ioc.mp hi).1; omega)]
    ring
  rw [hl] at he
  rw [he]
  have hs : (∑ i ∈ Ioc m (n - 1),
      (1 / (i + 1 : ℕ) ^ 2 - 1 / (i : ℝ) ^ 2) * (∑ j ∈ Icc 1 i, a j)) =
      -(∑ i ∈ Ioc m (n - 1), (∑ j ∈ Icc 1 i, a j) *
        (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

theorem mrt_weighted_square_tail (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {C : ℝ} (hC : 0 ≤ C)
    (hprefix : ∀ n ≤ U, (∑ i ∈ Icc 1 n, a i) ≤ C * n) :
    (∑ i ∈ Ioc L U, a i / (i : ℝ) ^ 2) ≤ 2 * C / L := by
  by_cases heq : L = U
  · subst U
    simp only [Ioc_eq_empty_of_le le_rfl, sum_empty]
    positivity
  have hlt : L < U := lt_of_le_of_ne hLU heq
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hUR : (0 : ℝ) < U := by exact_mod_cast hL.trans_le hLU
  have hgap (i : ℕ) (hi : i ∈ Ioc L (U - 1)) :
      (∑ j ∈ Icc 1 i, a j) * (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) ≤
        2 * C * (1 / (i : ℝ) - 1 / (i + 1 : ℕ)) := by
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hL.trans (mem_Ioc.mp hi).1
    have hiU : i ≤ U := (mem_Ioc.mp hi).2.trans (Nat.sub_le _ _)
    have hnon : 0 ≤ 1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2 := by
      apply sub_nonneg.mpr
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith
    calc
      _ ≤ (C * i) * (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) :=
        mul_le_mul_of_nonneg_right (hprefix i hiU) hnon
      _ ≤ _ := by
        have hg : (i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / (i + 1 : ℕ) ^ 2) ≤
            2 * (1 / (i : ℝ) - 1 / (i + 1 : ℕ)) := by
          push_cast
          field_simp
          nlinarith
        nlinarith
  have htel : (∑ i ∈ Ioc L (U - 1), (1 / (i : ℝ) - 1 / (i + 1 : ℕ))) =
      1 / (L + 1 : ℕ) - 1 / (U : ℝ) := by
    have hset : Ioc L (U - 1) = Ico (L + 1) U := by
      ext i
      simp only [mem_Ioc, mem_Ico]
      omega
    rw [hset]
    calc
      _ = -(∑ i ∈ Ico (L + 1) U, (1 / (i + 1 : ℕ) - 1 / (i : ℝ))) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [sum_Ico_sub (fun i : ℕ => (1 : ℝ) / i) (show L + 1 ≤ U by omega)]
        ring
  rw [mrt_square_reciprocal_partial_sum a hlt]
  have htop : (∑ i ∈ Icc 1 U, a i) / (U : ℝ) ^ 2 ≤ C / U := by
    apply (div_le_div_of_nonneg_right (hprefix U le_rfl) (sq_nonneg _)).trans_eq
    field_simp
  have hbot : 0 ≤ (∑ i ∈ Icc 1 L, a i) / (L + 1 : ℕ) ^ 2 :=
    div_nonneg (sum_nonneg (fun i _ => ha i)) (sq_nonneg _)
  have hsum := sum_le_sum hgap
  rw [← mul_sum, htel] at hsum
  have hn : 0 ≤ C / (U : ℝ) := div_nonneg hC hUR.le
  calc
    _ ≤ C / U + 2 * C * (1 / (L + 1 : ℕ) - 1 / (U : ℝ)) := by linarith
    _ = 2 * C / (L + 1 : ℕ) - C / U := by ring
    _ ≤ 2 * C / (L + 1 : ℕ) := sub_le_self _ hn
    _ ≤ 2 * C / L := div_le_div_of_nonneg_left (by positivity) hLR
      (by exact_mod_cast Nat.le_add_right L 1)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMixedMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mean square of the actual mixed prime/cofactor coefficients. The
factorial cost is explicit, while the finite Euler factor depends only on
the preceding short prime band, not the number of typical-set masks. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_factored_coefficient_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℂ) {L U : ℕ}
    (hL : 0 < L) (hLU : L ≤ U) {A : ℝ}
    (hb : ∀ n ∈ Ioc L U, ‖b n‖ ≤ A *
      (((mrtFactoredUpTo P U).filter (fun d => d ∣ n)).card : ℝ)) :
    (∑ n ∈ Ioc L U, ‖b n / (n : ℂ)‖ ^ 2) ≤
      (2 / (L : ℝ)) * A ^ 2 * (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  let S := mrtFactoredUpTo P U
  let g : ℕ → ℝ := fun n => ((S.filter (fun d => d ∣ n)).card : ℝ) ^ 2
  let E := ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹
  have hE : 0 ≤ E := by
    apply prod_nonneg
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    exact inv_nonneg.mpr (by linarith)
  have hpref (n : ℕ) (_hn : n ≤ U) : (∑ i ∈ Icc 1 n, g i) ≤ E ^ 3 * n := by
    have hc := mrt_divisor_count_second_moment S
      (fun _ hd => mrtFactoredUpTo_pos P U hd)
      (fun _ hd _ he hed => mrtFactoredUpTo_divisor_closed P U hd he hed) n
    calc
      _ ≤ (n : ℝ) * (∑ d ∈ S, 1 / (d : ℝ)) ^ 3 := hc
      _ ≤ (n : ℝ) * E ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity))
          (mrt_factored_reciprocal_sum P hP U) 3
      _ = _ := mul_comm _ _
  have ht := mrt_weighted_square_tail g (fun _ => sq_nonneg _) hL hLU
    (pow_nonneg hE 3) hpref
  calc
    _ ≤ ∑ n ∈ Ioc L U, A ^ 2 * (g n / (n : ℝ) ^ 2) := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_natCast, div_pow]
      apply (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hb n hn) 2) (sq_nonneg _)).trans_eq
      dsimp [g]
      ring
    _ = A ^ 2 * ∑ n ∈ Ioc L U, g n / (n : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ A ^ 2 * (2 * E ^ 3 / L) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg A)
    _ = _ := by ring

theorem mrt_mixed_coefficient_mean_square (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial (Ioc L U)
      (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ))
      (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      16 * Real.exp 1 * ((T + U) / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
        (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  have hs : Ioc L U ⊆ Ioc 0 U := by
    intro n hn
    exact mem_Ioc.mpr ⟨lt_of_lt_of_le hL (mem_Ioc.mp hn).1.le, (mem_Ioc.mp hn).2⟩
  apply (mrt_dirichlet_mean_square_subset (Ioc L U) (N := U) hs
    (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ)) hT).trans
  have hmass := mrt_factored_coefficient_mass P hP
    (mrtMixedPrimeCoefficient P M a b r) hL hLU
    (fun n hn => mrt_mixed_prime_coefficient_bound P M hP a b ha hb r
      (lt_of_lt_of_le hL (mem_Ioc.mp hn).1.le) (mem_Ioc.mp hn).2)
  calc
    _ ≤ (8 * Real.exp 1 * (T + U)) *
        ((2 / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
          (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMixedPolynomial
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prime-power times cofactor polynomial identity. This attaches
the proved mixed coefficient estimate to the actual expression used on
the multiscale large-prime frequency classes. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_multiplicative_phase {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    Complex.exp (((-Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-Real.log ((m * n : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add, Nat.cast_mul, Real.log_mul
    (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]
  congr 1
  push_cast
  ring

lemma mrt_mixed_tuple_term {r : ℕ} (v : Fin r → ℕ)
    (hv : ∀ i, 0 < v i) {m : ℕ} (hm : 0 < m) (a b : ℕ → ℂ) (t : ℝ) :
    (∏ i, (a (v i) / (v i : ℂ)) *
      Complex.exp (((-Real.log (v i : ℝ) * t : ℝ) : ℂ) * Complex.I)) *
      ((b m / (m : ℂ)) *
        Complex.exp (((-Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
      ((∏ i, a (v i)) * b m) / ((∏ i, v i) * m : ℕ) *
        Complex.exp (((-Real.log (((∏ i, v i) * m : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [prod_mul_distrib, prod_div_distrib, mrt_prime_tuple_phase v hv t]
  have hprod : 0 < ∏ i, v i := prod_pos (fun i _ => hv i)
  have he := mrt_multiplicative_phase hprod hm t
  rw [← he]
  push_cast
  ring

theorem mrt_mixed_polynomial_identity (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hM : ∀ m ∈ M, 0 < m)
    (a b : ℕ → ℂ) (r L U : ℕ)
    (hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      L < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U) (t : ℝ) :
    (mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t) ^ r *
      mrtExponentialPolynomial M (fun m => b m / (m : ℂ))
        (fun m => -Real.log (m : ℝ)) t =
      mrtExponentialPolynomial (Ioc L U)
        (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  let V := Fintype.piFinset (fun _ : Fin r => P)
  let S := V ×ˢ M
  let mult : ((Fin r → ℕ) × ℕ) → ℕ := fun v => (∏ i, v.1 i) * v.2
  let coeff : ((Fin r → ℕ) × ℕ) → ℂ := fun v => (∏ i, a (v.1 i)) * b v.2
  let term : ℕ → ℂ := fun n => (n : ℂ)⁻¹ *
    Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I)
  have hmap : ∀ v ∈ S, mult v ∈ Ioc L U := by
    intro v hv
    exact mem_Ioc.mpr (hsupport v.1 (mem_product.mp hv).1 v.2 (mem_product.mp hv).2)
  have hgroup : (∑ n ∈ Ioc L U, ∑ v ∈ S.filter (fun v => mult v = n),
      coeff v * term (mult v)) = ∑ v ∈ S, coeff v * term (mult v) :=
    sum_fiberwise_of_maps_to hmap _
  have hright : mrtExponentialPolynomial (Ioc L U)
      (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ))
      (fun n => -Real.log (n : ℝ)) t = ∑ v ∈ S, coeff v * term (mult v) := by
    rw [← hgroup]
    unfold mrtExponentialPolynomial mrtMixedPrimeCoefficient mrtMixedPrimeFiber
    apply sum_congr rfl
    intro n _
    simp only [sum_div, sum_mul]
    apply sum_congr rfl
    intro v hv
    have he : mult v = n := (mem_filter.mp hv).2
    change coeff v / (n : ℂ) * _ = coeff v * term (mult v)
    rw [he]
    dsimp [term]
    ring
  rw [hright]
  unfold mrtExponentialPolynomial
  rw [sum_pow', sum_mul]
  simp_rw [mul_sum]
  rw [sum_product]
  apply sum_congr rfl
  intro v hv
  apply sum_congr rfl
  intro m hm
  simpa only [coeff, term, mult, div_eq_mul_inv, mul_assoc] using
    mrt_mixed_tuple_term v
      (fun i => (hP _ (Fintype.mem_piFinset.mp hv i)).pos) (hM m hm) a b t

theorem mrt_mixed_prime_cofactor_mean_square (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hM : ∀ m ∈ M, 0 < m)
    (a b : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      L < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖(mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t) ^ r *
        mrtExponentialPolynomial M (fun m => b m / (m : ℂ))
          (fun m => -Real.log (m : ℝ)) t‖ ^ 2) ≤
      16 * Real.exp 1 * ((T + U) / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
        (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  simp_rw [mrt_mixed_polynomial_identity P M hP hM a b r L U hsupport]
  exact mrt_mixed_coefficient_mean_square P M hP a b ha hb r hL hLU hT

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

/-- Frequency-restricted Cauchy--Schwarz, with the actual pointwise
short-prime bounds and the cofactor energies left explicit. -/
theorem mrt_restricted_product_sum_energy {ι : Type*} (J : Finset ι)
    (Q R : ι → ℝ → ℂ) (hR : ∀ j ∈ J, Continuous (R j))
    (A : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hQ : ∀ j ∈ J, ∀ t ∈ E, ‖Q j t‖ ≤ A j) :
    (∫ t in E, ‖∑ j ∈ J, Q j t * R j t‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 *
        (∫ t in -T..T, ‖R j t‖ ^ 2) := by
  have hi (j : ι) (hj : j ∈ J) := mrt_continuous_square_integrable (hR j hj) hT hE
  calc
    _ ≤ ∫ t in E, (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * ‖R j t‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((integrable_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))).const_mul _)
      intro t ht
      apply (mrt_norm_sum_sq_le_card J (fun j => Q j t * R j t)).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j hj
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hQ j hj t ht) 2) (sq_nonneg _)
    _ = (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * (∫ t in E, ‖R j t‖ ^ 2) := by
      rw [integral_const_mul, integral_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))]
      simp only [integral_const_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (mrt_restricted_square_le_interval (hR j hj) hT hE) (sq_nonneg _)

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
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTAmplification
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification on the multiscale classes where a preceding short-prime
polynomial is large. The inserted power is estimated by the actual mixed
prime/cofactor moment, not by an assumed large-value proposition. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_amplified_energy (Q R : ℝ → ℂ) (hQ : Continuous Q) (hR : Continuous R)
    (r : ℕ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖Q t‖) :
    (∫ t in E, ‖R t‖ ^ 2) ≤
      (∫ t in -T..T, ‖Q t ^ r * R t‖ ^ 2) / V ^ (2 * r) := by
  have hprod : Continuous (fun t => Q t ^ r * R t) := (hQ.pow r).mul hR
  have hi := mrt_continuous_square_integrable hprod hT hE
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  calc
    _ = ∫ t in E, V ^ (2 * r) * ‖R t‖ ^ 2 := by
      rw [integral_const_mul]
      ring
    _ ≤ ∫ t in E, ‖Q t ^ r * R t‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => by positivity) _ hi
      intro t ht
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm r 2]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hV.le (hlarge t ht) _) (sq_nonneg _)
    _ ≤ _ := mrt_restricted_square_le_interval hprod hT hE

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
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCofactorWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cofactor polynomial has an actual fixed multiplicative window.
Finite partial summation turns its ordinary reciprocal-count prefix bound
into a pointwise bound for that polynomial. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

lemma mrt_cofactor_window_set (N : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    ((Icc 1 (4 * N)).filter (fun m : ℕ => (N : ℝ) < a * (m : ℝ) ∧ a * (m : ℝ) ≤ 2 * N)) =
      Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊ := by
  have ha0 : 0 < a := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hfloor : ⌊(2 * N : ℝ) / a⌋₊ ≤ 4 * N := by
    apply Nat.floor_le_of_le
    have hdiv : (2 * N : ℝ) / a ≤ 2 * N := div_le_self (by positivity) ha
    push_cast
    linarith
  ext m
  constructor
  · intro hm
    obtain ⟨hm, hlo, hhi⟩ := mem_filter.mp hm
    apply mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (div_nonneg hN0 ha0.le)).mpr
      apply (div_lt_iff₀ ha0).mpr
      simpa only [mul_comm] using hlo
    · apply Nat.le_floor
      apply (le_div_iff₀ ha0).mpr
      simpa only [mul_comm] using hhi
  · intro hm
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hm
    have hloR := (Nat.floor_lt (div_nonneg hN0 ha0.le)).mp hlo
    have hhiR : (m : ℝ) ≤ (2 * N : ℝ) / a :=
      (Nat.le_floor_iff (by positivity)).mp hhi
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, hhi.trans hfloor⟩, ?_⟩
    constructor
    · simpa only [mul_comm] using (div_lt_iff₀ ha0).mp hloR
    · simpa only [mul_comm] using (le_div_iff₀ ha0).mp hhiR

lemma mrt_cofactor_window_ratio (N : ℕ) {a : ℝ} (ha : 0 < a)
    (hx : 2 ≤ (N : ℝ) / a) :
    0 < ⌊(N : ℝ) / a⌋₊ ∧
      ⌊(N : ℝ) / a⌋₊ ≤ ⌊(2 * N : ℝ) / a⌋₊ ∧
      ⌊(2 * N : ℝ) / a⌋₊ ≤ 3 * ⌊(N : ℝ) / a⌋₊ := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm2 : 2 ≤ ⌊(N : ℝ) / a⌋₊ := Nat.le_floor (by exact hx)
  have hlow := Nat.lt_floor_add_one ((N : ℝ) / a)
  have hhigh := Nat.floor_le (show 0 ≤ (2 * N : ℝ) / a by positivity)
  have hdouble : (N : ℝ) / a ≤ (2 * N : ℝ) / a := by
    calc
      _ ≤ 2 * ((N : ℝ) / a) := by linarith
      _ = _ := by ring
  refine ⟨by omega, Nat.floor_le_floor hdouble, ?_⟩
  have hid : (2 * N : ℝ) / a = 2 * ((N : ℝ) / a) := by ring
  conv at hhigh => rhs; rw [hid]
  have hm2R : (2 : ℝ) ≤ ⌊(N : ℝ) / a⌋₊ := by exact_mod_cast hm2
  have hu : (⌊(2 * N : ℝ) / a⌋₊ : ℝ) ≤ 3 * (⌊(N : ℝ) / a⌋₊ : ℝ) := by linarith
  exact_mod_cast hu

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCofactorMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A mean-square bound for the actual fixed-window cofactor polynomial.
The reciprocal-count weight is a contraction, so this estimate is uniform
in all remaining typical-factorization masks. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_cofactor_exponential_polynomial (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    mrtCofactorPolynomial P F N a t =
      mrtExponentialPolynomial (Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtCofactorPolynomial
  rw [← sum_filter, mrt_cofactor_window_set N ha]
  unfold mrtExponentialPolynomial
  apply sum_congr rfl
  intro n _
  unfold mrtDirichletAtom
  ring

lemma mrt_reciprocal_count_oneBounded (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) :
    OneBounded (fun n => F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) := by
  intro n hn
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_one (by positivity : (0 : ℝ) < (finitePrimeDivisorCount P n + 1 : ℕ))).mpr
  exact (hF n hn).trans (by norm_num)

/-- The usual cofactor mean square, with its actual length `N/a`.
Neither the number nor the sizes of other prime bands enter the constant. -/
theorem mrt_cofactor_mean_square (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N : ℝ) / a) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtCofactorPolynomial P F N a t‖ ^ 2) ≤
      32 * Real.exp 1 * (T * a / (N : ℝ) + 1) := by
  let m := ⌊(N : ℝ) / a⌋₊
  let n := ⌊(2 * N : ℝ) / a⌋₊
  have ha0 : 0 < a := by linarith
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * a)
    ((le_div_iff₀ ha0).mp hx)
  obtain ⟨hm, hmn, _⟩ := mrt_cofactor_window_ratio N ha0 hx
  change 0 < m at hm
  change m ≤ n at hmn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlower : (N : ℝ) / a ≤ 2 * m := by
    have hfloor := Nat.lt_floor_add_one ((N : ℝ) / a)
    change (N : ℝ) / a < (m : ℝ) + 1 at hfloor
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hNm : (N : ℝ) ≤ 2 * a * m := by
    have hh := (div_le_iff₀ ha0).mp hlower
    nlinarith
  have hnR : (n : ℝ) ≤ 4 * m := by
    have hfloor := Nat.floor_le (show 0 ≤ (2 * N : ℝ) / a by positivity)
    change (n : ℝ) ≤ (2 * N : ℝ) / a at hfloor
    have he : (2 * N : ℝ) / a = 2 * ((N : ℝ) / a) := by ring
    rw [he] at hfloor
    linarith
  have hcoeff := mrt_reciprocal_count_oneBounded P F hF
  have hmass : (∑ k ∈ Ioc m n,
      ‖(F k / ((finitePrimeDivisorCount P k + 1 : ℕ) : ℂ)) / (k : ℂ)‖ ^ 2) ≤
      (m : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ k ∈ Ioc m n, ((k : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro k hk
        have hk0 : 0 < k := hm.trans (mem_Ioc.mp hk).1
        have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
        rw [norm_div, Complex.norm_natCast]
        calc
          _ ≤ (1 / (k : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity)
            (div_le_div_of_nonneg_right (hcoeff k hk0) hkR.le) 2
          _ = _ := by simp
      _ ≤ (m : ℝ)⁻¹ - (n : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hm.ne' hmn
      _ ≤ _ := sub_le_self _ (by positivity)
  have hmean := mrt_dirichlet_mean_square_subset (Ioc m n)
    (N := n) (by intro k hk; exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hk).1; omega,
      (mem_Ioc.mp hk).2⟩)
    (fun k => (F k / ((finitePrimeDivisorCount P k + 1 : ℕ) : ℂ)) / (k : ℂ)) hT
  have hTm : T / (m : ℝ) ≤ 2 * (T * a / (N : ℝ)) := by
    apply (div_le_iff₀ hmR).mpr
    calc
      T = (T * (N : ℝ)) / N := by field_simp
      _ ≤ (T * (2 * a * m)) / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNm hT.le) hNr.le
      _ = (2 * (T * a / (N : ℝ))) * m := by ring
  have hnm : (n : ℝ) / m ≤ 4 := (div_le_iff₀ hmR).mpr hnR
  simp_rw [mrt_cofactor_exponential_polynomial P F N ha]
  change (∫ t in -T..T, ‖mrtExponentialPolynomial (Ioc m n)
    (fun k => (F k / ((finitePrimeDivisorCount P k + 1 : ℕ) : ℂ)) / (k : ℂ))
    (fun k => -Real.log (k : ℝ)) t‖ ^ 2) ≤ _
  apply hmean.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (n : ℝ)) * (m : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 8 * Real.exp 1 * (T / (m : ℝ) + (n : ℝ) / m) := by ring
    _ ≤ 8 * Real.exp 1 * (2 * (T * a / (N : ℝ)) + 4) :=
      mul_le_mul_of_nonneg_left (add_le_add hTm hnm) (by positivity)
    _ ≤ _ := by
      have hp : 0 ≤ Real.exp 1 * (T * a / (N : ℝ)) := by positivity
      nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTShortEuler
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An absolute Euler-factor bound on one short prime bin. Counting all
integers in the bin already suffices, so this local mixed-moment constant
requires no additional prime-distribution theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_short_bin_reciprocal_mass (P : Finset ℕ) {Y : ℕ} (hY : 0 < Y)
    (hP : P ⊆ Icc Y (2 * Y)) :
    (∑ p ∈ P, (1 : ℝ) / p) ≤ 2 := by
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hc : P.card ≤ 2 * Y := by
    have hh := card_le_card hP
    rw [Nat.card_Icc] at hh
    omega
  calc
    _ ≤ ∑ _p ∈ P, (1 : ℝ) / Y := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hYR (by exact_mod_cast (mem_Icc.mp (hP hp)).1)
    _ = (P.card : ℝ) / Y := by simp [div_eq_mul_inv]
    _ ≤ 2 := (div_le_iff₀ hYR).mpr (by exact_mod_cast hc)

lemma mrt_short_bin_reciprocal_square_mass (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) {Y : ℕ} (hY : 0 < Y)
    (hP : P ⊆ Icc Y (2 * Y)) :
    (∑ p ∈ P, ((1 : ℝ) / p) ^ 2) ≤ 1 := by
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ p ∈ P, (1 : ℝ) / p := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hmem
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hmem).two_le
      have hi : (1 : ℝ) / p ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) hp2
      nlinarith [show (0 : ℝ) ≤ 1 / (p : ℝ) by positivity]
    _ ≤ (1 / 2 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left (mrt_short_bin_reciprocal_mass P hY hP) (by norm_num)
    _ = 1 := by norm_num

theorem mrt_short_bin_euler_cube (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) {Y : ℕ} (hY : 0 < Y)
    (hP : P ⊆ Icc Y (2 * Y)) :
    (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 ≤ Real.exp 9 := by
  have hprod : (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ≤
      Real.exp (∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hmem
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hmem).two_le
      have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    · exact fun p hmem => mrt_prime_reciprocal_euler_bound (hp p hmem)
  have hn : 0 ≤ ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := by
    apply prod_nonneg
    intro p hmem
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hmem).two_le
    have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    exact inv_nonneg.mpr (by linarith)
  calc
    _ ≤ (Real.exp (∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2))) ^ 3 :=
      pow_le_pow_left₀ hn hprod 3
    _ = Real.exp (3 * ∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2)) := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [sum_add_distrib]
      linarith [mrt_short_bin_reciprocal_mass P hY hP,
        mrt_short_bin_reciprocal_square_mass P hp hY hP]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTCofactorMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed moment needed by the second and later MRT frequency classes.
This is the actual reciprocal-count cofactor, with arbitrary one-bounded
remaining masks. Its only loss is the explicit prime-tuple factorial. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_short_prime_cofactor_moment (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y N : ℕ} (hY : 0 < Y) (hN : 0 < N)
    (hbin : P ⊆ Icc Y (2 * Y)) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    (r : ℕ) (hpowlo : u ≤ (Y : ℝ) ^ r) (hpowhi : (Y : ℝ) ^ r ≤ u * Y)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖(mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t) ^ r *
        mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      16 * Real.exp 10 * (T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y) *
        (r.factorial : ℝ) ^ 2 := by
  let M := Ioc ⌊(N : ℝ) / u⌋₊ ⌊(2 * N : ℝ) / u⌋₊
  let B : ℕ → ℂ := fun n => F n / ((finitePrimeDivisorCount Q n + 1 : ℕ) : ℂ)
  let U : ℕ := 2 ^ (r + 1) * Y * N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hM (m : ℕ) (hm : m ∈ M) : 0 < m := by
    have := (mem_Ioc.mp hm).1
    omega
  have hwindow (m : ℕ) (hm : m ∈ M) : (N : ℝ) < u * m ∧ u * m ≤ 2 * N := by
    change m ∈ Ioc ⌊(N : ℝ) / u⌋₊ ⌊(2 * N : ℝ) / u⌋₊ at hm
    rw [← mrt_cofactor_window_set N hu] at hm
    exact (mem_filter.mp hm).2
  have hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      N < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U := by
    intro v hv m hm
    have hlo : Y ^ r ≤ ∏ i, v i := by
      calc
        _ = ∏ _i : Fin r, Y := by simp
        _ ≤ _ := prod_le_prod' (fun i _ =>
          (mem_Icc.mp (hbin (Fintype.mem_piFinset.mp hv i))).1)
    have hhi : (∏ i, v i) ≤ (2 * Y) ^ r := by
      calc
        _ ≤ ∏ _i : Fin r, 2 * Y := prod_le_prod' (fun i _ =>
          (mem_Icc.mp (hbin (Fintype.mem_piFinset.mp hv i))).2)
        _ = _ := by simp
    have hloR : u ≤ ((∏ i, v i : ℕ) : ℝ) := hpowlo.trans (by exact_mod_cast hlo)
    have hhiR : ((∏ i, v i : ℕ) : ℝ) ≤ (2 : ℝ) ^ r * u * Y := by
      calc
        _ ≤ ((2 : ℝ) * Y) ^ r := by exact_mod_cast hhi
        _ = (2 : ℝ) ^ r * (Y : ℝ) ^ r := mul_pow _ _ _
        _ ≤ (2 : ℝ) ^ r * (u * Y) :=
          mul_le_mul_of_nonneg_left hpowhi (by positivity)
        _ = _ := by ring
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hw := hwindow m hm
    constructor
    · have hh := hw.1.trans_le (mul_le_mul_of_nonneg_right hloR hm0)
      exact_mod_cast hh
    · have hh : ((∏ i, v i : ℕ) : ℝ) * m ≤
          (2 : ℝ) ^ (r + 1) * Y * N := by
        calc
          _ ≤ ((2 : ℝ) ^ r * u * Y) * m := mul_le_mul_of_nonneg_right hhiR hm0
          _ = ((2 : ℝ) ^ r * Y) * (u * m) := by ring
          _ ≤ ((2 : ℝ) ^ r * Y) * (2 * N) :=
            mul_le_mul_of_nonneg_left hw.2 (by positivity)
          _ = _ := by rw [pow_succ]; ring
      exact_mod_cast hh
  have hNU : N ≤ U := by
    have hp : 1 ≤ 2 ^ (r + 1) := one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))
    have hfactor : 1 ≤ 2 ^ (r + 1) * Y := one_le_mul_of_one_le_of_one_le hp hY
    simpa only [U, one_mul] using Nat.mul_le_mul_right N hfactor
  have hbound := mrt_mixed_prime_cofactor_mean_square P M hP hM a B ha
    (fun m hm => mrt_reciprocal_count_oneBounded Q F hF m (hM m hm))
    r hN hNU hsupport hT
  have he (t : ℝ) : mrtCofactorPolynomial Q F N u t =
      mrtExponentialPolynomial M (fun m => B m / (m : ℂ))
        (fun m => -Real.log (m : ℝ)) t := mrt_cofactor_exponential_polynomial Q F N hu t
  simp_rw [he]
  apply hbound.trans
  have hratio : (T + (U : ℝ)) / (N : ℝ) =
      T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y := by
    dsimp [U]
    push_cast
    field_simp [hNR.ne']
  rw [hratio]
  calc
    _ ≤ 16 * Real.exp 1 * (T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y) *
        (r.factorial : ℝ) ^ 2 * Real.exp 9 :=
      mul_le_mul_of_nonneg_left (mrt_short_bin_euler_cube P hP hY hbin) (by positivity)
    _ = _ := by
      rw [show Real.exp 10 = Real.exp 1 * Real.exp 9 by rw [← Real.exp_add]; norm_num]
      ring

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
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMultiscaleEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual typical-set polynomial on a later MRT frequency class.
The preceding short prime polynomial is large, while each current-bin
polynomial is small. Amplification is applied before extending the
cofactor energy to the whole frequency interval. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_restricted_product_sum_energy_local {ι : Type*} (J : Finset ι)
    (Q R : ι → ℝ → ℂ) (hR : ∀ j ∈ J, Continuous (R j)) (A : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hQ : ∀ j ∈ J, ∀ t ∈ E, ‖Q j t‖ ≤ A j) :
    (∫ t in E, ‖∑ j ∈ J, Q j t * R j t‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * (∫ t in E, ‖R j t‖ ^ 2) := by
  have hi (j : ι) (hj : j ∈ J) := mrt_continuous_square_integrable (hR j hj) hT hE
  calc
    _ ≤ ∫ t in E, (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * ‖R j t‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((integrable_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))).const_mul _)
      intro t ht
      apply (mrt_norm_sum_sq_le_card J (fun j => Q j t * R j t)).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j hj
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hQ j hj t ht) 2) (sq_nonneg _)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))]
      simp only [integral_const_mul]

theorem mrt_short_class_cofactor_energy (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y N : ℕ} (hY : 0 < Y) (hN : 0 < N)
    (hbin : P ⊆ Icc Y (2 * Y)) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    (r : ℕ) (hpowlo : u ≤ (Y : ℝ) ^ r) (hpowhi : (Y : ℝ) ^ r ≤ u * Y)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial P
      (fun p => a p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      (16 * Real.exp 10 * (T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y) *
        (r.factorial : ℝ) ^ 2) / V ^ (2 * r) := by
  have hR : Continuous (mrtCofactorPolynomial Q F N u) := by
    have he : mrtCofactorPolynomial Q F N u =
        mrtExponentialPolynomial (Ioc ⌊(N : ℝ) / u⌋₊ ⌊(2 * N : ℝ) / u⌋₊)
          (fun n => (F n / ((finitePrimeDivisorCount Q n + 1 : ℕ) : ℂ)) / (n : ℂ))
          (fun n => -Real.log (n : ℝ)) :=
      funext (mrt_cofactor_exponential_polynomial Q F N hu)
    rw [he]
    exact mrtExponentialPolynomial_continuous _ _ _
  apply (mrt_amplified_energy _ _ (mrtExponentialPolynomial_continuous _ _ _) hR
    r hT.le hV hE hlarge).trans
  exact div_le_div_of_nonneg_right
    (mrt_short_prime_cofactor_moment P Q hP hY hN hbin a ha F hF hu r hpowlo hpowhi hT)
    (pow_nonneg hV.le _)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFrequencyPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

lemma mrt_small_frequency_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (j : ℕ) :
    MeasurableSet (mrtSmallFrequencyBand K Q A j) := by
  have he : mrtSmallFrequencyBand K Q A j =
      ⋂ k ∈ K j, {t | ‖Q j k t‖ ≤ A j k} := by
    ext t
    simp [mrtSmallFrequencyBand]
  rw [he]
  exact (K j).measurableSet_biInter (fun k _ =>
    (isClosed_le (hQ j k).norm continuous_const).measurableSet)

lemma mrt_first_small_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (j : ℕ) :
    MeasurableSet (mrtFirstSmallBand K Q A j) :=
  (mrt_small_frequency_band_measurable K Q A hQ j).diff
    ((range j).measurableSet_biUnion (fun i _ =>
      mrt_small_frequency_band_measurable K Q A hQ i))

lemma mrt_first_small_band_disjoint {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (mrtFirstSmallBand K Q A i) (mrtFirstSmallBand K Q A j) := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hj.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨mem_range.mpr hlt, hi.1⟩⟩)
  · exact hi.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨mem_range.mpr hgt, hj.1⟩⟩)

theorem mrt_frequency_partition {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (J : ℕ) (S : Set ℝ) :
    S = (S ∩ mrtNoSmallBand K Q A J) ∪
      ⋃ j ∈ range J, S ∩ mrtFirstSmallBand K Q A j := by
  ext t
  constructor
  · intro ht
    by_cases he : ∃ j < J, t ∈ mrtSmallFrequencyBand K Q A j
    · right
      let j := Nat.find he
      have hj := Nat.find_spec he
      apply Set.mem_iUnion.mpr
      refine ⟨j, Set.mem_iUnion.mpr ⟨mem_range.mpr hj.1, ht, hj.2, ?_⟩⟩
      intro hprev
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hprev
      obtain ⟨hij, hit⟩ := Set.mem_iUnion.mp hi
      have hil : i < j := mem_range.mp hij
      exact Nat.find_min he hil ⟨hil.trans hj.1, hit⟩
    · left
      refine ⟨ht, ?_⟩
      intro hsmall
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hsmall
      obtain ⟨hjJ, hjt⟩ := Set.mem_iUnion.mp hj
      exact he ⟨j, mem_range.mp hjJ, hjt⟩
  · rintro (ht | ht)
    · exact ht.1
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
      obtain ⟨_, hjt⟩ := Set.mem_iUnion.mp hj
      exact hjt.1

theorem mrt_later_band_large_witness {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) {j : ℕ} (hj : 0 < j)
    {t : ℝ} (ht : t ∈ mrtFirstSmallBand K Q A j) :
    ∃ k ∈ K (j - 1), A (j - 1) k < ‖Q (j - 1) k t‖ := by
  have hn : t ∉ mrtSmallFrequencyBand K Q A (j - 1) := by
    intro hsmall
    exact ht.2 (Set.mem_iUnion.mpr ⟨j - 1,
      Set.mem_iUnion.mpr ⟨mem_range.mpr (by omega), hsmall⟩⟩)
  simp only [mrtSmallFrequencyBand, Set.mem_ofPred_eq, not_forall, not_le, exists_prop] at hn
  exact hn

theorem mrt_frequency_partition_integral {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (J : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) (f : ℝ → ℝ) (hf : IntegrableOn f S) :
    (∫ t in S, f t) = (∫ t in S ∩ mrtNoSmallBand K Q A J, f t) +
      ∑ j ∈ range J, ∫ t in S ∩ mrtFirstSmallBand K Q A j, f t := by
  let E := S ∩ mrtNoSmallBand K Q A J
  let B := fun j => S ∩ mrtFirstSmallBand K Q A j
  have hBsub (j : ℕ) : B j ⊆ S := Set.inter_subset_left
  have hBmeas (j : ℕ) : MeasurableSet (B j) :=
    hS.inter (mrt_first_small_band_measurable K Q A hQ j)
  have hBdis : Set.Pairwise (↑(range J)) (fun i j => Disjoint (B i) (B j)) := by
    intro i _ j _ hij
    exact (mrt_first_small_band_disjoint K Q A hij).mono
      Set.inter_subset_right Set.inter_subset_right
  have hsum := integral_biUnion_finset (range J) (fun j _ => hBmeas j) hBdis
    (fun j _ => hf.mono_set (hBsub j))
  have hdis : Disjoint E (⋃ j ∈ range J, B j) := by
    apply Set.disjoint_left.mpr
    intro t ht hU
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hU
    obtain ⟨hjJ, hjt⟩ := Set.mem_iUnion.mp hj
    exact ht.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjJ, hjt.2.1⟩⟩)
  have hUsub : (⋃ j ∈ range J, B j) ⊆ S := by
    intro t ht
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
    obtain ⟨_, hjt⟩ := Set.mem_iUnion.mp hj
    exact hjt.1
  conv_lhs => rw [mrt_frequency_partition K Q A J S]
  rw [setIntegral_union hdis ((range J).measurableSet_biUnion (fun j _ => hBmeas j))
    (hf.mono_set Set.inter_subset_left) (hf.mono_set hUsub), hsum]

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
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeneralSmallEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-small-band energy bound for ordinary multiplicative
functions, including the explicit prime-square extraction error. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_general_typical_small_prime_energy {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (hlow : ∀ k ∈ K, 1 ≤ lower k) (hupper : ∀ k ∈ K, 2 ≤ (N : ℝ) / lower k)
    (F : ℕ → ℂ)
    (hF : Multiplicative F)
    (hFb : OneBounded F) {T : ℝ} (hT : 0 < T)
    (E : Set ℝ) (hE : E ⊆ Set.Ioc (-T) T) (A : κ → ℝ)
    (hsmall : ∀ k ∈ K, ∀ t ∈ E,
      ‖mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
        (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖ ≤ A k) :
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      2816 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) +
      64 * Real.exp 1 * (K.card : ℝ) *
        ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1) := by
  let B := mrtTypicalCoefficient (J.erase j) P F
  let Q : κ → ℝ → ℂ := fun k =>
    mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
      (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ))
  let R : κ → ℝ → ℂ := fun k => mrtCofactorPolynomial (P j) B N (lower k)
  let D := mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N
  let G : ℝ → ℂ := fun t => ∑ k ∈ K, Q k t * R k t
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded _ _ _ hFb
  have hR (k : κ) (_hk : k ∈ K) : Continuous (R k) :=
    mrtCofactorPolynomial_continuous (P j) B N (lower k)
  have hD : Continuous D := mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := continuous_finsetSum K (fun k hk =>
    (mrtExponentialPolynomial_continuous _ _ _).mul (hR k hk))
  have hg := mrt_restricted_product_sum_energy K Q R hR A hT.le hE hsmall
  have hg' : (∫ t in E, ‖G t‖ ^ 2) ≤
      32 * Real.exp 1 * (K.card : ℝ) *
        ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1) := by
    change (∫ t in E, ‖∑ k ∈ K, Q k t * R k t‖ ^ 2) ≤ _
    apply hg.trans
    calc
      _ ≤ (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
          (32 * Real.exp 1 * (T * lower k / (N : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (mrt_cofactor_mean_square (P j) B hB N (hlow k hk) (hupper k hk) hT)
          (sq_nonneg _)
      _ = _ := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro k _
        ring
  have herr := mrt_typical_general_prime_mean_square J P hP hdis hj
    (fun p => lower (bin p)) hN hδ hδ2 hL F hF hFb hT
  simp_rw [mrt_extracted_prime_bins K (P j) bin hbin lower N F
    (mrtTypicalCoefficient (J.erase j) P F)] at herr
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at herr
  apply (mrt_restricted_energy_split D G hD hG hT.le hE).trans
  calc
    _ ≤ 2 * (1408 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1))) +
        2 * (32 * Real.exp 1 * (K.card : ℝ) *
          ∑ k ∈ K, (A k) ^ 2 * (T * lower k / (N : ℝ) + 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num))
        (mul_le_mul_of_nonneg_left hg' (by norm_num))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFrequencyCover
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refinement of a later frequency class by its actual preceding-bin
large-value witnesses. The witnesses may overlap; the finite sum charges
each preceding bin explicitly. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_nonnegative_integral_cover {ι : Type*} (I : Finset ι)
    (E : ι → Set ℝ) (hE : ∀ i ∈ I, MeasurableSet (E i)) {S : Set ℝ}
    (hS : MeasurableSet S) (f : ℝ → ℝ) (hf : IntegrableOn f S)
    (hf0 : ∀ t ∈ S, 0 ≤ f t) (hcover : ∀ t ∈ S, ∃ i ∈ I, t ∈ E i) :
    (∫ t in S, f t) ≤ ∑ i ∈ I, ∫ t in S ∩ E i, f t := by
  have hi (i : ι) (hmem : i ∈ I) : IntegrableOn ((E i).indicator f) S :=
    hf.indicator (hE i hmem)
  calc
    _ ≤ ∫ t in S, ∑ i ∈ I, (E i).indicator f t := by
      apply setIntegral_mono_on hf (integrable_finsetSum I hi) hS
      intro t ht
      obtain ⟨i, hiI, hit⟩ := hcover t ht
      calc
        f t = (E i).indicator f t := (Set.indicator_of_mem hit f).symm
        _ ≤ ∑ i ∈ I, (E i).indicator f t := by
          apply single_le_sum _ hiI
          intro k _
          by_cases hk : t ∈ E k
          · rw [Set.indicator_of_mem hk f]
            exact hf0 t ht
          · rw [Set.indicator_of_notMem hk f]
    _ = ∑ i ∈ I, ∫ t in S, (E i).indicator f t := integral_finsetSum I hi
    _ = _ := by
      apply sum_congr rfl
      intro i hiI
      exact setIntegral_indicator (hE i hiI)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTAmplificationPower
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit amplification order used between two successive MRT
prime scales. The integer ceiling satisfies the exact support inequalities
needed by the mixed cofactor moment. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_nat_pow_eq_exp {Y : ℝ} (hY : 0 < Y) (r : ℕ) :
    Y ^ r = Real.exp ((r : ℝ) * Real.log Y) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hY]
  congr 1
  ring

theorem mrt_amplification_order_bounds {Y u : ℝ} (hY : 1 < Y) (hu : 1 ≤ u) :
    u ≤ Y ^ mrtAmplificationOrder Y u ∧
      Y ^ mrtAmplificationOrder Y u ≤ u * Y ∧
      (mrtAmplificationOrder Y u : ℝ) < Real.log u / Real.log Y + 1 := by
  have hY0 : 0 < Y := by linarith
  have hu0 : 0 < u := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hquot : 0 ≤ Real.log u / Real.log Y :=
    div_nonneg (Real.log_nonneg hu) hlogY.le
  have hlo : Real.log u / Real.log Y ≤ (mrtAmplificationOrder Y u : ℝ) :=
    Nat.le_ceil _
  have hhi : (mrtAmplificationOrder Y u : ℝ) < Real.log u / Real.log Y + 1 :=
    Nat.ceil_lt_add_one hquot
  refine ⟨?_, ?_, hhi⟩
  · calc
      u = Real.exp (Real.log u) := (Real.exp_log hu0).symm
      _ ≤ Real.exp ((mrtAmplificationOrder Y u : ℝ) * Real.log Y) :=
        Real.exp_le_exp.mpr ((div_le_iff₀ hlogY).mp hlo)
      _ = _ := (mrt_nat_pow_eq_exp hY0 _).symm
  · have hh : (mrtAmplificationOrder Y u : ℝ) * Real.log Y <
        Real.log u + Real.log Y := by
      have hh := (mul_lt_mul_of_pos_right hhi hlogY)
      rw [add_mul, div_mul_cancel₀ _ hlogY.ne', one_mul] at hh
      exact hh
    calc
      _ = Real.exp ((mrtAmplificationOrder Y u : ℝ) * Real.log Y) :=
        mrt_nat_pow_eq_exp hY0 _
      _ ≤ Real.exp (Real.log u + Real.log Y) := Real.exp_le_exp.mpr hh.le
      _ = u * Y := by rw [Real.exp_add, Real.exp_log hu0, Real.exp_log hY0]

theorem mrt_short_class_cofactor_energy_chosen (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y N : ℕ} (hY : 1 < Y) (hN : 0 < N)
    (hbin : P ⊆ Icc Y (2 * Y)) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial P
      (fun p => a p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      (16 * Real.exp 10 *
        (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder Y u + 1) * Y) *
          ((mrtAmplificationOrder Y u).factorial : ℝ) ^ 2) /
        V ^ (2 * mrtAmplificationOrder Y u) := by
  obtain ⟨hlo, hhi, _⟩ := mrt_amplification_order_bounds
    (show (1 : ℝ) < Y by exact_mod_cast hY) hu
  exact mrt_short_class_cofactor_energy P Q hP (by omega) hN hbin a ha F hF hu _
    hlo hhi hT hV hE hlarge

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTRealPrimeBins
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real short-prime bins, as used in the Ramaré decomposition, fit the
integer endpoint mixed-moment theorem without moving any prime. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_real_prime_bin_subset (P : Finset ℕ) {Y : ℝ}
    (hbin : ∀ p ∈ P, Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y) :
    P ⊆ Icc ⌈Y⌉₊ (2 * ⌈Y⌉₊) := by
  intro p hp
  refine mem_Icc.mpr ⟨Nat.ceil_le.mpr (hbin p hp).1, ?_⟩
  have hh : (p : ℝ) ≤ 2 * (⌈Y⌉₊ : ℝ) :=
    (hbin p hp).2.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil Y) (by norm_num))
  exact_mod_cast hh

lemma mrt_real_prime_bin_ceil {Y : ℝ} (hY : 1 < Y) :
    1 < ⌈Y⌉₊ ∧ Y ≤ (⌈Y⌉₊ : ℝ) ∧ (⌈Y⌉₊ : ℝ) ≤ 2 * Y ∧
      Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log Y + Real.log 2 := by
  have hY0 : 0 < Y := by linarith
  have hlo : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  have hhi : (⌈Y⌉₊ : ℝ) ≤ 2 * Y := by
    have hh := Nat.ceil_lt_add_one hY0.le
    linarith
  refine ⟨Nat.lt_ceil.mpr (by simpa using hY), hlo, hhi, ?_⟩
  calc
    _ ≤ Real.log (2 * Y) := Real.log_le_log (hY0.trans_le hlo) hhi
    _ = _ := by rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY0.ne']; ring

theorem mrt_real_short_class_cofactor_energy (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y : ℝ} (hY : 1 < Y)
    (hbin : ∀ p ∈ P, Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y)
    {N : ℕ} (hN : 0 < N) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial P
      (fun p => a p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      (16 * Real.exp 10 *
        (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
          ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2) /
        V ^ (2 * mrtAmplificationOrder ⌈Y⌉₊ u) := by
  exact mrt_short_class_cofactor_energy_chosen P Q hP
    (mrt_real_prime_bin_ceil hY).1 hN
    (mrt_real_prime_bin_subset P hbin) a ha F hF hu hT hV hE hlarge

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTWitnessedEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coarse energy on a later MRT class, summed over actual large
preceding-bin witnesses. The Ramaré error is deliberately absent here:
it is charged once, before this finite cover is used. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_witnessed_cofactor_energy {κ β : Type*}
    (K : Finset κ) (Q : κ → ℝ → ℂ) (A lower : κ → ℝ)
    (P : Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) (hlower : ∀ k ∈ K, 1 ≤ lower k)
    (B : Finset β) (Pprev : β → Finset ℕ) (Y : β → ℝ)
    (hY : ∀ b ∈ B, 1 < Y b)
    (hPprev : ∀ b ∈ B, ∀ p ∈ Pprev b, p.Prime)
    (hprevbin : ∀ b ∈ B, ∀ p ∈ Pprev b, Y b ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y b)
    (a : β → ℕ → ℂ) (ha : ∀ b ∈ B, ∀ p ∈ Pprev b, ‖a b p‖ ≤ 1)
    (V : β → ℝ) (hV : ∀ b ∈ B, 0 < V b)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hS : MeasurableSet S)
    (hST : S ⊆ Set.Ioc (-T) T) (hQ : ∀ k ∈ K, Continuous (Q k))
    (hsmall : ∀ k ∈ K, ∀ t ∈ S, ‖Q k t‖ ≤ A k)
    (hcover : ∀ t ∈ S, ∃ b ∈ B, V b ≤
      ‖mrtExponentialPolynomial (Pprev b) (fun p => a b p / (p : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in S, ‖∑ k ∈ K, Q k t * mrtCofactorPolynomial P F N (lower k) t‖ ^ 2) ≤
      ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
        ((16 * Real.exp 10 *
          (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y b⌉₊ (lower k) + 1) * ⌈Y b⌉₊) *
            ((mrtAmplificationOrder ⌈Y b⌉₊ (lower k)).factorial : ℝ) ^ 2) /
          (V b) ^ (2 * mrtAmplificationOrder ⌈Y b⌉₊ (lower k))) := by
  let R : κ → ℝ → ℂ := fun k => mrtCofactorPolynomial P F N (lower k)
  let G : ℝ → ℂ := fun t => ∑ k ∈ K, Q k t * R k t
  let E : β → Set ℝ := fun b => {t | V b ≤
    ‖mrtExponentialPolynomial (Pprev b) (fun p => a b p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t‖}
  have hR (k : κ) (hk : k ∈ K) : Continuous (R k) := by
    have he : R k = mrtExponentialPolynomial
        (Ioc ⌊(N : ℝ) / lower k⌋₊ ⌊(2 * N : ℝ) / lower k⌋₊)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) :=
      funext (mrt_cofactor_exponential_polynomial P F N (hlower k hk))
    rw [he]
    exact mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := continuous_finsetSum K (fun k hk => (hQ k hk).mul (hR k hk))
  have hE (b : β) : MeasurableSet (E b) :=
    (isClosed_le continuous_const
      (mrtExponentialPolynomial_continuous _ _ _).norm).measurableSet
  have hiG : IntegrableOn (fun t => ‖G t‖ ^ 2) S :=
    mrt_continuous_square_integrable hG hT.le hST
  change (∫ t in S, ‖G t‖ ^ 2) ≤ _
  apply (mrt_nonnegative_integral_cover B E (fun b _ => hE b) hS
    (fun t => ‖G t‖ ^ 2) hiG (fun _ _ => sq_nonneg _) hcover).trans
  apply sum_le_sum
  intro b hb
  change (∫ t in S ∩ E b, ‖∑ k ∈ K, Q k t * R k t‖ ^ 2) ≤ _
  have hsub : S ∩ E b ⊆ Set.Ioc (-T) T := Set.inter_subset_left.trans hST
  apply (mrt_restricted_product_sum_energy_local K Q R hR A hT.le hsub
    (fun k hk t ht => hsmall k hk t ht.1)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact mrt_real_short_class_cofactor_energy (Pprev b) P (hPprev b hb) (hY b hb)
    (hprevbin b hb) hN (a b) (ha b hb) F hF (hlower k hk) hT (hV b hb)
    hsub (fun t ht => ht.2)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeneralWitnessed
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Witnessed multiscale energy for ordinary multiplicative functions.
The prime-square extraction error permits ordinary multiplicativity
in the multiscale estimate. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_general_typical_witnessed_energy {ι κ β : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (hlow : ∀ k ∈ K, 1 ≤ lower k)
    (F : ℕ → ℂ)
    (hF : Multiplicative F)
    (hFb : OneBounded F)
    (B : Finset β) (Pprev : β → Finset ℕ) (Y : β → ℝ)
    (hY : ∀ b ∈ B, 1 < Y b)
    (hprev : ∀ b ∈ B, ∀ p ∈ Pprev b, p.Prime)
    (hprevbin : ∀ b ∈ B, ∀ p ∈ Pprev b, Y b ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y b)
    (V : β → ℝ) (hV : ∀ b ∈ B, 0 < V b)
    {T : ℝ} (hT : 0 < T) {E : Set ℝ} (hE : MeasurableSet E)
    (hET : E ⊆ Set.Ioc (-T) T) (A : κ → ℝ)
    (hsmall : ∀ k ∈ K, ∀ t ∈ E,
      ‖mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
        (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖ ≤ A k)
    (hcover : ∀ t ∈ E, ∃ b ∈ B, V b ≤
      ‖mrtExponentialPolynomial (Pprev b) (fun p => F p / (p : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      2816 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) +
      2 * ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
        ((16 * Real.exp 10 *
          (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y b⌉₊ (lower k) + 1) * ⌈Y b⌉₊) *
            ((mrtAmplificationOrder ⌈Y b⌉₊ (lower k)).factorial : ℝ) ^ 2) /
          (V b) ^ (2 * mrtAmplificationOrder ⌈Y b⌉₊ (lower k))) := by
  let C := mrtTypicalCoefficient (J.erase j) P F
  let Q : κ → ℝ → ℂ := fun k =>
    mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
      (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ))
  let G : ℝ → ℂ := fun t => ∑ k ∈ K, Q k t * mrtCofactorPolynomial (P j) C N (lower k) t
  let D := mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N
  have hG : Continuous G := continuous_finsetSum K (fun k _ =>
    (mrtExponentialPolynomial_continuous _ _ _).mul
      (mrtCofactorPolynomial_continuous (P j) C N (lower k)))
  have hc := mrt_witnessed_cofactor_energy K Q A lower (P j) C
    (mrtTypicalCoefficient_oneBounded _ _ _ hFb) hN hlow B Pprev Y hY hprev hprevbin
    (fun _ => F) (fun b hb p hp => hFb p (hprev b hb p hp).pos) V hV hT hE hET
    (fun _ _ => mrtExponentialPolynomial_continuous _ _ _) hsmall hcover
  change (∫ t in E, ‖G t‖ ^ 2) ≤ _ at hc
  have herr := mrt_typical_general_prime_mean_square J P hP hdis hj
    (fun p => lower (bin p)) hN hδ hδ2 hL F hF hFb hT
  simp_rw [mrt_extracted_prime_bins K (P j) bin hbin lower N F
    (mrtTypicalCoefficient (J.erase j) P F)] at herr
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at herr
  apply (mrt_restricted_energy_split D G
    (mrtExponentialPolynomial_continuous _ _ _) hG hT.le hET).trans
  have hh := add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))
  convert hh using 1 <;> first | rfl | ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MultiscaleMellinEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual multiscale prime partition in the Mellin convention

The costs below are the proved Ramaré extraction and amplified cofactor
costs. The integral over the class with no small prime polynomial remains
explicit; no estimate for that exceptional class is assumed here.
-/
namespace JointDickman
open Finset MeasureTheory
open TwoPointCorrelations

namespace MellinPrimeBands

lemma angular_eq_dyadic (f : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    angularMellinPolynomial (Ioc N (2*N)) f t = mrtDyadicPolynomial f N t := rfl

lemma polynomial_continuous (D : MellinPrimeBands) (f : ℕ → ℂ) (j k : ℕ) :
    Continuous (D.polynomial f j k) := mrtExponentialPolynomial_continuous _ _ _

theorem firstSmallBand_energy_le (D : MellinPrimeBands) {J N : ℕ}
    (hD : D.Valid J N) (hJ : 0 < J) (hN : 0 < N)
    (f : ℕ → ℂ) (hf : Multiplicative f) (hb : OneBounded f)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S ∩ mrtFirstSmallBand D.bins (D.polynomial f) D.threshold 0,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (range J) D.primes f) N t‖^2) ≤
      D.extractionCost 0 N T + D.initialCost N T := by
  have hj : 0 ∈ range J := mem_range.mpr hJ
  apply mrt_general_typical_small_prime_energy (range J) D.primes hD.prime hD.disjoint hj
    (D.bins 0) (D.bin 0) (hD.bin_mem 0 hj) (D.lower 0) hN
    (hD.resolution_one 0 hj) (hD.resolution_two 0 hj) (hD.prime_bounds 0 hj)
    (fun k hk => le_trans (by norm_num) (hD.lower_two 0 hj k hk))
    (hD.upper 0 hj) f hf hb hT _ (Set.inter_subset_left.trans hS)
  intro k hk t ht
  exact ht.2.1 k hk

theorem laterSmallBand_energy_le (D : MellinPrimeBands) {J N j : ℕ}
    (hD : D.Valid J N) (hj : j ∈ range J) (hj0 : 0 < j) (hN : 0 < N)
    (f : ℕ → ℂ) (hf : Multiplicative f) (hb : OneBounded f)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S ∩ mrtFirstSmallBand D.bins (D.polynomial f) D.threshold j,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (range J) D.primes f) N t‖^2) ≤
      D.extractionCost j N T + D.laterCost j N T := by
  have hp : j-1 ∈ range J := mem_range.mpr (by have := mem_range.mp hj; omega)
  apply mrt_general_typical_witnessed_energy (range J) D.primes hD.prime hD.disjoint hj
    (D.bins j) (D.bin j) (hD.bin_mem j hj) (D.lower j) hN
    (hD.resolution_one j hj) (hD.resolution_two j hj) (hD.prime_bounds j hj)
    (fun k hk => le_trans (by norm_num) (hD.lower_two j hj k hk)) f hf hb
    (D.bins (j-1)) (fun b => (D.primes (j-1)).filter (fun p => D.bin (j-1) p = b))
    (D.lower (j-1)) (fun b hb => lt_of_lt_of_le (by norm_num) (hD.lower_two _ hp b hb))
    (fun b _ p hpb => hD.prime _ hp p (mem_filter.mp hpb).1) ?_
    (D.threshold (j-1)) (hD.threshold_pos _ hp) hT
    (hSm.inter (mrt_first_small_band_measurable _ _ _ (D.polynomial_continuous f) j))
    (Set.inter_subset_left.trans hS) (D.threshold j) ?_ ?_
  · intro b _ p hpb
    obtain ⟨hmem, heq⟩ := mem_filter.mp hpb
    have hbounds := hD.prime_bounds (j-1) hp p hmem
    rw [heq] at hbounds
    exact ⟨hbounds.1, hbounds.2.trans (mul_le_mul_of_nonneg_right
      (hD.resolution_two _ hp) (by have := hD.lower_two _ hp b (heq ▸ hD.bin_mem _ hp p hmem); linarith))⟩
  · intro k hk t ht
    exact ht.2.1 k hk
  · intro t ht
    obtain ⟨b, hb, hlarge⟩ := mrt_later_band_large_witness D.bins (D.polynomial f)
      D.threshold hj0 ht.2
    exact ⟨b, hb, hlarge.le⟩

/-- Every nonexceptional class is bounded by its actual small-prime or
amplified cofactor estimate. Only the no-small-band integral is left. -/
theorem partition_energy_le (D : MellinPrimeBands) {J N : ℕ}
    (hD : D.Valid J N) (hN : 0 < N)
    (f : ℕ → ℂ) (hf : Multiplicative f) (hb : OneBounded f)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient (range J) D.primes f) t‖^2) ≤
    (∫ t in S ∩ mrtNoSmallBand D.bins (D.polynomial f) D.threshold J,
      ‖angularMellinPolynomial (Ioc N (2*N))
        (mrtTypicalCoefficient (range J) D.primes f) t‖^2) +
    ∑ j ∈ range J, (D.extractionCost j N T +
      if j = 0 then D.initialCost N T else D.laterCost j N T) := by
  simp_rw [angular_eq_dyadic]
  rw [mrt_frequency_partition_integral D.bins (D.polynomial f) D.threshold
    (D.polynomial_continuous f) J hSm
    (fun t => ‖mrtDyadicPolynomial (mrtTypicalCoefficient (range J) D.primes f) N t‖^2)
    (mrt_continuous_square_integrable (mrtExponentialPolynomial_continuous _ _ _) hT.le hS)]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro j hj
  split_ifs with hj0
  · subst j
    exact D.firstSmallBand_energy_le hD (mem_range.mp hj) hN f hf hb hT hS
  · exact D.laterSmallBand_energy_le hD hj (Nat.pos_of_ne_zero hj0) hN f hf hb hT hSm hS

end MellinPrimeBands
end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBandParameters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit prime-band endpoints from MRT, Definition 2.1. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma mrtBandLower_one (P Q : ℝ) (hP : 0 < P) : mrtBandLower P Q 1 = P := by
  simp [mrtBandLower, Real.exp_log hP]

lemma mrtBandUpper_one (Q : ℝ) (hQ : 0 < Q) : mrtBandUpper Q 1 = Q := by
  simp [mrtBandUpper, Real.exp_log hQ]

lemma mrt_band_endpoints (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogQ : 1 ≤ Real.log Q) :
    2 ≤ mrtBandLower P Q j ∧ mrtBandLower P Q j ≤ mrtBandUpper Q j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp0 : 0 < P := by linarith
  have hq0 : 0 < Q := hp0.trans_le hPQ
  have hlp : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hlpq : Real.log P ≤ Real.log Q := Real.log_le_log hp0 hPQ
  have hc : 1 ≤ (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) (one_le_pow₀ hlogQ)
  constructor
  · calc
      2 ≤ P := hP
      _ = Real.exp (Real.log P) := (Real.exp_log hp0).symm
      _ ≤ mrtBandLower P Q j := by
        apply Real.exp_le_exp.mpr
        nlinarith
  · apply Real.exp_le_exp.mpr
    have hpow : (Real.log Q) ^ j = (Real.log Q) ^ (j - 1) * Real.log Q := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log P ≤
          (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlpq (by positivity)
      _ = (j : ℝ) ^ (4 * j) * Real.log Q ^ j := by rw [hpow]; ring
      _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hj1 (by omega)) (by positivity)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBandSeparation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual MRT bands are disjoint, as required by the corrected
Ramaré decomposition; no disjointness hypothesis on those bands remains. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_adjacent_band_gap (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q j < mrtBandLower P Q (j + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hpow : (j : ℝ) ^ (4 * j + 2) ≤ ((j : ℝ) + 1) ^ (4 * (j + 1)) := by
    calc
      _ ≤ ((j : ℝ) + 1) ^ (4 * j + 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  apply Real.exp_lt_exp.mpr
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hlogQ.le j)
  have hp : 0 < (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by positivity
  nlinarith

lemma mrt_band_lower_monotone (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandLower P Q i ≤ mrtBandLower P Q j := by
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  refine Nat.le_induction le_rfl (fun k hk ih => ?_) j hij
  exact ih.trans (((mrt_band_endpoints P Q k (hi.trans hk) hP hPQ hlogQ).2).trans
    (mrt_adjacent_band_gap P Q k (hi.trans hk) hP hPQ hlogP).le)

lemma mrt_band_gap (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q i < mrtBandLower P Q j :=
  (mrt_adjacent_band_gap P Q i hi hP hPQ hlogP).trans_le
    (mrt_band_lower_monotone P Q (i + 1) j (by omega) (by omega) hP hPQ hlogP)

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

lemma mrtFrequencyExponent_zero (η : ℝ) :
    mrtFrequencyExponent η 0 = 1 / 4 - 3 * η / 2 := by
  unfold mrtFrequencyExponent
  norm_num
  ring

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

lemma mrtFrequencyExponent_nonneg {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 6)
    (j : ℕ) : 0 ≤ mrtFrequencyExponent η j := by
  have hh := (mrtFrequencyExponent_bounds hη j).1
  linarith

lemma mrtFrequencyExponent_gap (η : ℝ) (j : ℕ) :
    mrtFrequencyExponent η (j + 1) - mrtFrequencyExponent η j =
      η / (2 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  unfold mrtFrequencyExponent
  push_cast
  field_simp [h1, h2]
  ring

lemma mrtFrequencyExponent_gap_lower {η : ℝ} (hη : 0 ≤ η) (j : ℕ) :
    η / (2 * ((j : ℝ) + 2) ^ 2) ≤
      mrtFrequencyExponent η (j + 1) - mrtFrequencyExponent η j := by
  rw [mrtFrequencyExponent_gap]
  apply div_le_div_of_nonneg_left hη (by positivity)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- After paying half of the threshold gap for the mixed-moment
factorial, the remaining exponential saving is still summable. -/
lemma mrt_frequency_gap_saving {η x : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x) (j : ℕ) :
    2 * x * (mrtFrequencyExponent η j - mrtFrequencyExponent η (j + 1) +
      η / (4 * ((j : ℝ) + 2) ^ 2)) ≤ -η * x / (2 * ((j : ℝ) + 2) ^ 2) := by
  have hh := mul_le_mul_of_nonneg_left (mrtFrequencyExponent_gap_lower hη j)
    (show 0 ≤ 2 * x by positivity)
  have he : 2 * (η / (4 * ((j : ℝ) + 2) ^ 2)) =
      η / (2 * ((j : ℝ) + 2) ^ 2) := by
    field_simp
    ring
  rw [show -η * x / (2 * ((j : ℝ) + 2) ^ 2) =
      -x * (η / (2 * ((j : ℝ) + 2) ^ 2)) by ring]
  nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTAmplificationGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit factorial and ceiling costs in the multiscale mixed moment.
These estimates keep the numerical scale requirements visible. -/

namespace TwoPointCorrelations

lemma mrt_factorial_square_exp (r : ℕ) :
    (r.factorial : ℝ) ^ 2 ≤
      Real.exp (2 * (r : ℝ) * Real.log (max 1 (r : ℝ))) := by
  by_cases hr : r = 0
  · subst r
    norm_num
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hf : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
    calc
      _ ≤ ((r : ℝ) ^ r) ^ 2 := pow_le_pow_left₀ (by positivity) hf 2
      _ = _ := by
        rw [max_eq_right hrR, mrt_nat_pow_eq_exp (by positivity : (0 : ℝ) < r),
          ← Real.exp_nat_mul]
        congr 1
        ring

lemma mrt_amplification_log_cost {Y u : ℝ}
    (hY : 1 ≤ Real.log Y) (hu : 1 ≤ Real.log u) (hY0 : 0 < Y) (hu0 : 0 < u) :
    (mrtAmplificationOrder Y u : ℝ) *
        Real.log (max 1 (mrtAmplificationOrder Y u : ℝ)) ≤
      (Real.log u / Real.log Y + 1) * (Real.log (Real.log u) + 1) := by
  have hY1 : 1 < Y := (Real.log_pos_iff hY0.le).mp (by linarith)
  have hu1 : 1 ≤ u := (Real.log_nonneg_iff hu0).mp (by linarith)
  let r : ℕ := mrtAmplificationOrder Y u
  have hr := (mrt_amplification_order_bounds hY1 hu1).2.2.le
  change (r : ℝ) ≤ Real.log u / Real.log Y + 1 at hr
  have hx0 : 0 < Real.log u := by linarith
  have hquot : Real.log u / Real.log Y ≤ Real.log u :=
    div_le_self hx0.le hY
  have hmax : max 1 (r : ℝ) ≤ 2 * Real.log u := by
    apply max_le
    · linarith
    · linarith
  have hlog : Real.log (max 1 (r : ℝ)) ≤ Real.log (Real.log u) + 1 := by
    calc
      _ ≤ Real.log (2 * Real.log u) := Real.log_le_log (by positivity) hmax
      _ = Real.log 2 + Real.log (Real.log u) := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul hr hlog (Real.log_nonneg (le_max_left _ _))
    (by positivity)

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMixedThreshold
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The factorial and support growth in the amplified cofactor moment
are paid from half of the gap between successive prime thresholds. -/

namespace TwoPointCorrelations

lemma mrt_mixed_threshold_exponent {η x y : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 6) (hx : 0 ≤ x) (j r : ℕ)
    (hr : (r : ℝ) * y ≤ x + y)
    (hcost : mrtAmplificationCost r y (mrtFrequencyExponent η j) ≤
      η * x / (2 * ((j : ℝ) + 2) ^ 2)) :
    -2 * mrtFrequencyExponent η (j + 1) * x +
      (((r : ℝ) + 1) * Real.log 2 + y) +
      2 * (r : ℝ) * Real.log (max 1 (r : ℝ)) +
      2 * (r : ℝ) * mrtFrequencyExponent η j * y ≤
      -η * x / (2 * ((j : ℝ) + 2) ^ 2) := by
  have ha := mrtFrequencyExponent_nonneg hη hη' j
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * mrtFrequencyExponent η j
    by positivity)
  have hg := mrt_frequency_gap_saving hη hx j
  have he : 2 * x * (η / (4 * ((j : ℝ) + 2) ^ 2)) =
      η * x / (2 * ((j : ℝ) + 2) ^ 2) := by field_simp <;> ring
  unfold mrtAmplificationCost at hcost
  nlinarith

theorem mrt_mixed_threshold_bound {η x y τ : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 6) (hx : 0 ≤ x) (hy : 0 ≤ y) (hτ : 0 ≤ τ)
    (j r : ℕ) (hr : (r : ℝ) * y ≤ x + y)
    (hcost : mrtAmplificationCost r y (mrtFrequencyExponent η j) ≤
      η * x / (2 * ((j : ℝ) + 2) ^ 2)) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x) *
        (τ + (2 : ℝ) ^ (r + 1) * Real.exp y) * (r.factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * y) ^ (2 * r) ≤
      (τ + 1) * Real.exp (-η * x / (2 * ((j : ℝ) + 2) ^ 2)) := by
  let g := ((r : ℝ) + 1) * Real.log 2 + y
  let f := 2 * (r : ℝ) * Real.log (max 1 (r : ℝ))
  let d := -(2 * (r : ℝ) * mrtFrequencyExponent η j * y)
  have hpow : (2 : ℝ) ^ (r + 1) * Real.exp y = Real.exp g := by
    rw [mrt_nat_pow_eq_exp (by norm_num), ← Real.exp_add]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    rfl
  have hden : Real.exp (-mrtFrequencyExponent η j * y) ^ (2 * r) =
      Real.exp d := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [d]
    push_cast
    ring
  have hg0 : 0 ≤ g := by
    dsimp [g]
    positivity
  have hg1 : 1 ≤ Real.exp g := Real.one_le_exp_iff.mpr hg0
  have hsum : τ + Real.exp g ≤ (τ + 1) * Real.exp g := by nlinarith
  rw [hpow, hden]
  calc
    _ ≤ Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x) *
        ((τ + 1) * Real.exp g) * Real.exp f / Real.exp d := by
      apply div_le_div_of_nonneg_right _ (Real.exp_pos d).le
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
      · exact mrt_factorial_square_exp r
      · positivity
      · positivity
    _ = (τ + 1) * Real.exp
        (-2 * mrtFrequencyExponent η (j + 1) * x + g + f - d) := by
      have he : Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x + g + f - d) =
          Real.exp (-2 * mrtFrequencyExponent η (j + 1) * x) *
            Real.exp g * Real.exp f / Real.exp d := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_add]
      rw [he]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ τ + 1)
      apply Real.exp_le_exp.mpr
      dsimp [g, f, d]
      convert mrt_mixed_threshold_exponent hη hη' hx j r hr hcost using 1
      all_goals try with_reducible_and_instances rfl
      ring

lemma mrt_amplification_cost_bound {Y u a : ℝ}
    (hY : 1 ≤ Real.log Y) (hu : 1 ≤ Real.log u) (hY0 : 0 < Y) (hu0 : 0 < u) :
    mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y) a ≤
      (Real.log u / Real.log Y + 2) * Real.log 2 + Real.log Y +
        2 * (Real.log u / Real.log Y + 1) * (Real.log (Real.log u) + 1) +
        2 * a * Real.log Y := by
  have hY1 : 1 < Y := (Real.log_pos_iff hY0.le).mp (by linarith)
  have hu1 : 1 ≤ u := (Real.log_nonneg_iff hu0).mp (by linarith)
  have hr := (mrt_amplification_order_bounds hY1 hu1).2.2.le
  have hc := mrt_amplification_log_cost hY hu hY0 hu0
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_right (add_le_add_right hr 1) hlog2
  unfold mrtAmplificationCost
  nlinarith

theorem mrt_mixed_threshold_amplification {η Y u τ : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 6) (hY : 1 < Y) (hu : 1 ≤ u) (hτ : 0 ≤ τ) (j : ℕ)
    (hcost : mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y)
        (mrtFrequencyExponent η j) ≤
      η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder Y u + 1) * Y) *
        ((mrtAmplificationOrder Y u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder Y u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hy := Real.log_pos hY
  have hr := mul_le_mul_of_nonneg_right
    (mrt_amplification_order_bounds hY hu).2.2.le hy.le
  rw [add_mul, div_mul_cancel₀ _ hy.ne', one_mul] at hr
  simpa only [Real.exp_log (by linarith : 0 < Y)] using
    mrt_mixed_threshold_bound hη hη' (Real.log_nonneg hu) hy.le hτ j
      (mrtAmplificationOrder Y u) hr hcost

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMixedScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit sufficient logarithmic scale separations for the amplified
moment. The factorial budget is derived, rather than assumed. -/

namespace TwoPointCorrelations

lemma mrt_amplification_cost_coarse {Y u a : ℝ}
    (hY0 : 0 < Y) (hu0 : 0 < u) (hY : 1 ≤ Real.log Y)
    (hYu : Real.log Y ≤ Real.log u) (ha : a ≤ 1 / 4) :
    mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y) a ≤
      8 * (Real.log u / Real.log Y) * (Real.log (Real.log u) + 1) +
        2 * Real.log Y := by
  have hu : 1 ≤ Real.log u := hY.trans hYu
  have hx0 : 0 ≤ Real.log u := by linarith
  have hy0 : 0 < Real.log Y := by linarith
  have hq : 1 ≤ Real.log u / Real.log Y := (le_div_iff₀ hy0).mpr (by simpa using hYu)
  have hl : 1 ≤ Real.log (Real.log u) + 1 := by
    linarith [Real.log_nonneg hu]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := mul_le_mul_of_nonneg_left hlog1
    (show 0 ≤ Real.log u / Real.log Y + 2 by positivity)
  have hql := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ Real.log u / Real.log Y by positivity)
  have hq1 := mul_le_mul_of_nonneg_right hq
    (show 0 ≤ Real.log (Real.log u) + 1 by positivity)
  have hay := mul_le_mul_of_nonneg_right ha hy0.le
  have hc := mrt_amplification_cost_bound hY hu hY0 hu0 (a := a)
  nlinarith

lemma mrt_mixed_scale_guard {η x y d : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hd : 0 < d)
    (hsep : 32 * d * (Real.log x + 1) ≤ η * y)
    (hsize : 8 * d * y ≤ η * x) :
    8 * (x / y) * (Real.log x + 1) + 2 * y ≤ η * x / (2 * d) := by
  have hh := mul_le_mul_of_nonneg_left hsep (div_nonneg hx hy.le)
  have he : x / y * (η * y) = η * x := by field_simp
  rw [he] at hh
  apply (le_div_iff₀ (by positivity : 0 < 2 * d)).mpr
  nlinarith

theorem mrt_amplification_cost_of_separation {η Y u : ℝ}
    (hη : 0 ≤ η) (j : ℕ) (hY0 : 0 < Y) (hu0 : 0 < u)
    (hY : 1 ≤ Real.log Y) (hYu : Real.log Y ≤ Real.log u)
    (hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y)
    (hsize : 8 * ((j : ℝ) + 2) ^ 2 * Real.log Y ≤ η * Real.log u) :
    mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y)
        (mrtFrequencyExponent η j) ≤
      η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2) := by
  apply (mrt_amplification_cost_coarse hY0 hu0 hY hYu
    (show mrtFrequencyExponent η j ≤ 1 / 4 by
      have hh := (mrtFrequencyExponent_bounds hη j).2
      linarith)).trans
  exact mrt_mixed_scale_guard (by linarith : 0 ≤ Real.log u)
    (by linarith : 0 < Real.log Y) (by positivity) hsep hsize

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMixedRealBins
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real prime-bin threshold survives the integer endpoint
used by the finite mixed-moment theorem. -/

namespace TwoPointCorrelations

theorem mrt_mixed_real_bin_threshold {η Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ) (hY : 1 < Y)
    (hu : 1 ≤ u) (hτ : 0 ≤ τ)
    (hcost : mrtAmplificationCost (mrtAmplificationOrder ⌈Y⌉₊ u)
        (Real.log (⌈Y⌉₊ : ℝ)) (mrtFrequencyExponent η j) ≤
      η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hc := mrt_real_prime_bin_ceil hY
  have hlog : Real.log Y ≤ Real.log (⌈Y⌉₊ : ℝ) :=
    Real.log_le_log (by linarith) hc.2.1
  have ha := mrtFrequencyExponent_nonneg hη hη' j
  have hden : Real.exp (-mrtFrequencyExponent η j * Real.log (⌈Y⌉₊ : ℝ)) ≤
      Real.exp (-mrtFrequencyExponent η j * Real.log Y) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog (by linarith))
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le hden
    (2 * mrtAmplificationOrder ⌈Y⌉₊ u)
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
  exact mrt_mixed_threshold_amplification hη hη'
    (by exact_mod_cast hc.1) hu hτ j hcost

theorem mrt_mixed_real_bin_separation {η Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ) (hY : 1 < Y)
    (hlogY : 1 ≤ Real.log Y)
    (hYu : Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log u) (hu0 : 0 < u) (hτ : 0 ≤ τ)
    (hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y)
    (hsize : 8 * ((j : ℝ) + 2) ^ 2 * (Real.log Y + Real.log 2) ≤
      η * Real.log u) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hc := mrt_real_prime_bin_ceil hY
  have hlog : Real.log Y ≤ Real.log (⌈Y⌉₊ : ℝ) :=
    Real.log_le_log (by linarith) hc.2.1
  apply mrt_mixed_real_bin_threshold hη hη' j hY
    ((Real.log_nonneg_iff hu0).mp (by linarith)) hτ
  apply mrt_amplification_cost_of_separation hη j
    (by exact_mod_cast (show 0 < ⌈Y⌉₊ by omega)) hu0 (hlogY.trans hlog) hYu
  · exact hsep.trans (mul_le_mul_of_nonneg_left hlog hη)
  · exact (mul_le_mul_of_nonneg_left hc.2.2.2 (by positivity)).trans hsize

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBandLogGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scalar growth estimates for the actual MRT band endpoints.
They will discharge the mixed-moment factorial budget for every band. -/

namespace TwoPointCorrelations

lemma mrt_log_log_band_upper (Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hQ : 1 ≤ Real.log Q) :
    Real.log (Real.log (mrtBandUpper Q j)) + 1 ≤
      8 * (j : ℝ) ^ 2 * (Real.log (Real.log Q) + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hq0 : 0 < Real.log Q := by linarith
  have hl0 : 0 ≤ Real.log (Real.log Q) := Real.log_nonneg hQ
  have hlj : Real.log (j : ℝ) ≤ j :=
    (Real.log_le_sub_one_of_pos hj0).trans (by linarith)
  have hj2 : (j : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hlj
    (show 0 ≤ 4 * (j : ℝ) + 2 by positivity)
  have hq := mul_le_mul_of_nonneg_right hj2 hl0
  simp only [mrtBandUpper, Real.log_exp]
  rw [Real.log_mul (pow_ne_zero _ hj0.ne') (pow_ne_zero _ hq0.ne'),
    Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

lemma mrt_log_band_lower_fourth (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) :
    (j : ℝ) ^ 4 * Real.log P ≤ Real.log (mrtBandLower P Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp : (j : ℝ) ^ 4 ≤ (j : ℝ) ^ (4 * j) :=
    pow_le_pow_right₀ hj1 (by omega)
  have hq : 1 ≤ Real.log Q ^ (j - 1) := one_le_pow₀ hQ
  simp only [mrtBandLower, Real.log_exp]
  apply mul_le_mul_of_nonneg_right _ hP
  exact hp.trans (le_mul_of_one_le_right (by positivity) hq)

lemma mrt_band_adjacent_log_product (P Q : ℝ) (j : ℕ)
    (hP : 0 ≤ Real.log P) (hQ : 0 ≤ Real.log Q) :
    ((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) * Real.log P ≤
      Real.log (mrtBandLower P Q (j + 1)) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hp : (j : ℝ) ^ (4 * j + 2) ≤ ((j : ℝ) + 1) ^ (4 * j + 2) :=
    pow_le_pow_left₀ hj0 (by linarith) _
  have he : ((j : ℝ) + 1) ^ 2 * (j : ℝ) ^ (4 * j + 2) ≤
      ((j : ℝ) + 1) ^ (4 * (j + 1)) := by
    calc
      _ ≤ ((j : ℝ) + 1) ^ 2 * ((j : ℝ) + 1) ^ (4 * j + 2) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right he (pow_nonneg hQ j)) hP
  simpa only [mrtBandUpper, mrtBandLower, Real.log_exp,
    Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_assoc] using hh

theorem mrt_band_factorial_separation {η P Q : ℝ} (hη : 0 ≤ η)
    (j : ℕ) (hj : 1 ≤ j) (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 4096 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P) :
    32 * ((j : ℝ) + 1) ^ 2 *
        (Real.log (Real.log (mrtBandUpper Q (j + 1))) + 1) ≤
      η * Real.log (mrtBandLower P Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hl : 0 ≤ Real.log (Real.log Q) + 1 := by
    linarith [Real.log_nonneg hQ]
  have hu := mrt_log_log_band_upper Q (j + 1) (by omega) hQ
  simp only [Nat.cast_add, Nat.cast_one] at hu
  have hp : ((j : ℝ) + 1) ^ 4 ≤ 16 * (j : ℝ) ^ 4 := by
    calc
      _ ≤ (2 * (j : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by ring
  calc
    _ ≤ 32 * ((j : ℝ) + 1) ^ 2 *
        (8 * ((j : ℝ) + 1) ^ 2 * (Real.log (Real.log Q) + 1)) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = 256 * ((j : ℝ) + 1) ^ 4 * (Real.log (Real.log Q) + 1) := by ring
    _ ≤ 4096 * (j : ℝ) ^ 4 * (Real.log (Real.log Q) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hp hl]
    _ = (j : ℝ) ^ 4 * (4096 * (Real.log (Real.log Q) + 1)) := by ring
    _ ≤ (j : ℝ) ^ 4 * (η * Real.log P) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = η * ((j : ℝ) ^ 4 * Real.log P) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mrt_log_band_lower_fourth P Q j hj hP hQ) hη

theorem mrt_band_support_separation {η P Q : ℝ} (hη : 0 ≤ η)
    (j : ℕ) (hj : 1 ≤ j) (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 16 ≤ η * Real.log P) :
    8 * ((j : ℝ) + 1) ^ 2 * (Real.log (mrtBandUpper Q j) + Real.log 2) ≤
      η * Real.log (mrtBandLower P Q (j + 1)) := by
  have hy : 1 ≤ Real.log (mrtBandUpper Q j) := by
    have hh := mrt_band_index_le_log_upper Q j hj hQ
    exact (show (1 : ℝ) ≤ j by exact_mod_cast hj).trans hh
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hp := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ ((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) by positivity)
  calc
    _ ≤ 16 * ((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) := by
      nlinarith [mul_le_mul_of_nonneg_left (show Real.log 2 ≤
        Real.log (mrtBandUpper Q j) by linarith)
        (show 0 ≤ 8 * ((j : ℝ) + 1) ^ 2 by positivity)]
    _ ≤ η * (((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) * Real.log P) := by
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mrt_band_adjacent_log_product P Q j hP (by linarith)) hη

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBandMixedBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical mixed-moment coefficient on two successive actual
MRT bands. The only initial scale condition is stated on P and Q. -/

namespace TwoPointCorrelations

theorem mrt_actual_band_mixed_bound {η P Q Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hYlo : Real.exp (-1) * mrtBandLower P Q (j + 1) ≤ Y)
    (hYhi : Y ≤ mrtBandUpper Q (j + 1))
    (hulo : Real.exp (-1) * mrtBandLower P Q (j + 2) ≤ u)
    (huhi : u ≤ mrtBandUpper Q (j + 2)) (hτ : 0 ≤ τ) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hP0 : 0 ≤ Real.log P := by linarith
  have hbase (k : ℕ) (hk : 1 ≤ k) :
      2 ≤ Real.log (mrtBandLower P Q k) := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hh := mrt_log_band_lower_fourth P Q k hk hP0 hQ
    have hp : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1
    have hp2 : (2 : ℝ) ≤ (k : ℝ) ^ 4 * Real.log P := by
      have hmul := mul_le_mul hp hP (by norm_num : (0 : ℝ) ≤ 2) (by positivity)
      norm_num at hmul
      exact hmul
    exact hp2.trans hh
  have hY0 : 0 < Y := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le hYlo
  have hu0 : 0 < u := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le hulo
  have hlogYlo : Real.log (mrtBandLower P Q (j + 1)) - 1 ≤ Real.log Y := by
    have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hYlo
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp] at hh
    change -1 + Real.log (mrtBandLower P Q (j + 1)) ≤ Real.log Y at hh
    linarith
  have hlogulo : Real.log (mrtBandLower P Q (j + 2)) - 1 ≤ Real.log u := by
    have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hulo
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp] at hh
    change -1 + Real.log (mrtBandLower P Q (j + 2)) ≤ Real.log u at hh
    linarith
  have hybase := hbase (j + 1) (by omega)
  have hubase := hbase (j + 2) (by omega)
  have hlogY : 1 ≤ Real.log Y := by linarith
  have hlogu : 1 ≤ Real.log u := by linarith
  have hYhalf : Real.log (mrtBandLower P Q (j + 1)) / 2 ≤ Real.log Y := by linarith
  have huhalf : Real.log (mrtBandLower P Q (j + 2)) / 2 ≤ Real.log u := by linarith
  have hY1 : 1 < Y := (Real.log_pos_iff hY0.le).mp (by linarith)
  have hlogYhi : Real.log Y ≤ Real.log (mrtBandUpper Q (j + 1)) :=
    Real.log_le_log hY0 hYhi
  have hloguhi : Real.log u ≤ Real.log (mrtBandUpper Q (j + 2)) :=
    Real.log_le_log hu0 huhi
  have hhalfBudget : 4096 * (Real.log (Real.log Q) + 1) ≤ (η / 2) * Real.log P := by
    linarith
  have hsep0 := mrt_band_factorial_separation (show 0 ≤ η / 2 by positivity)
    (j + 1) (by omega) hP0 hQ hhalfBudget
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, show 1 + 1 = 2 by decide] at hsep0
  have hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y := by
    calc
      _ ≤ 32 * ((j : ℝ) + 2) ^ 2 *
          (Real.log (Real.log (mrtBandUpper Q (j + 2))) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (Real.log_le_log (by linarith) hloguhi) le_rfl
      _ ≤ (η / 2) * Real.log (mrtBandLower P Q (j + 1)) := by
        convert hsep0 using 1
        all_goals try with_reducible_and_instances rfl
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hYhalf hη]
  have h16 : 16 ≤ (η / 2) * Real.log P := by
    have hl := Real.log_nonneg hQ
    linarith
  have hsize0 := mrt_band_support_separation (show 0 ≤ η / 2 by positivity)
    (j + 1) (by omega) hP0 hQ h16
  simp only [Nat.add_assoc, show (1 : ℕ) + 1 = 2 by decide,
    Nat.cast_add, Nat.cast_one] at hsize0
  have hsize : 8 * ((j : ℝ) + 2) ^ 2 * (Real.log Y + Real.log 2) ≤
      η * Real.log u := by
    calc
      _ ≤ 8 * ((j : ℝ) + 2) ^ 2 *
          (Real.log (mrtBandUpper Q (j + 1)) + Real.log 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hlogYhi le_rfl) (by positivity)
      _ ≤ (η / 2) * Real.log (mrtBandLower P Q (j + 2)) := by
        convert hsize0 using 1
        all_goals try with_reducible_and_instances rfl
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left huhalf hη]
  have hc := mrt_real_prime_bin_ceil hY1
  have hYu : Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log u := by
    have hmult : 1 ≤ 8 * ((j : ℝ) + 2) ^ 2 := by
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith [sq_nonneg (j : ℝ)]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hh := le_mul_of_one_le_left
      (show 0 ≤ Real.log Y + Real.log 2 by linarith) hmult
    have he : η * Real.log u ≤ Real.log u :=
      mul_le_of_le_one_left (by linarith) (by linarith)
    exact hc.2.2.2.trans (hh.trans (hsize.trans he))
  exact mrt_mixed_real_bin_separation hη hη' j hY1 hlogY hYu hu0 hτ hsep hsize

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTGeometricBins
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exponential sum over the first MRT prime band. Its constant is
independent of the number of coarse bins. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_exp_geometric_sum {β H : ℝ} (hβ : 0 < β) (hH : 0 < H) (m n : ℕ) :
    (∑ k ∈ Icc m n, Real.exp (-β * (k : ℝ) / H)) ≤
      Real.exp (-β * (m : ℝ) / H) / (1 - Real.exp (-β / H)) := by
  let q := Real.exp (-β / H)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by linarith : -β < 0) hH
  have he (k : ℕ) : Real.exp (-β * (k : ℝ) / H) = q ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hs : Icc m n = Ico m (n + 1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  simp_rw [he]
  rw [hs]
  exact geom_sum_Ico_le_of_lt_one hq0 hq1

lemma mrt_geometric_denominator_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    1 / (1 - Real.exp (-x)) ≤ 2 / x := by
  have hex : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hinv : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hex
  have hgap : x / 2 ≤ 1 - Real.exp (-x) := by
    calc
      _ ≤ x / (1 + x) := div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)
      _ = 1 - 1 / (1 + x) := by
        field_simp [show (1 : ℝ) + x ≠ 0 by positivity]
        ring
      _ ≤ _ := sub_le_sub_left hinv 1
  calc
    _ ≤ 1 / (x / 2) := one_div_le_one_div_of_le (by positivity) hgap
    _ = _ := by ring

theorem mrt_first_band_exponential_sum {β H P : ℝ}
    (hβ : 0 < β) (hH : 0 < H) (hβH : β ≤ H) (hP : 1 ≤ P) (n : ℕ) :
    (∑ k ∈ Icc ⌊H * Real.log P⌋₊ n, Real.exp (-β * (k : ℝ) / H)) ≤
      (2 * Real.exp 1 * H / β) * P ^ (-β) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  let m : ℕ := ⌊H * Real.log P⌋₊
  have hfloor : H * Real.log P < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbase : -β * (m : ℝ) / H ≤ -β * Real.log P + β / H := by
    apply (div_le_iff₀ hH).mpr
    have hh := mul_le_mul_of_nonneg_left hfloor.le hβ.le
    field_simp [hH.ne']
    nlinarith
  have hpower : Real.exp (-β * (m : ℝ) / H) ≤ Real.exp 1 * P ^ (-β) := by
    calc
      _ ≤ Real.exp (-β * Real.log P + β / H) := Real.exp_le_exp.mpr hbase
      _ = Real.exp (β / H) * P ^ (-β) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hP0]
        rw [show -β * Real.log P = Real.log P * (-β) by ring, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ((div_le_one hH).mpr hβH)) (Real.rpow_nonneg hP0.le _)
  have hgap : 0 < 1 - Real.exp (-β / H) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith : -β < 0) hH))
  have hden : 1 / (1 - Real.exp (-β / H)) ≤ 2 / (β / H) := by
    simpa only [neg_div] using mrt_geometric_denominator_bound (div_pos hβ hH)
      ((div_le_one hH).mpr hβH)
  calc
    _ ≤ Real.exp (-β * (m : ℝ) / H) / (1 - Real.exp (-β / H)) :=
      mrt_exp_geometric_sum hβ hH m n
    _ ≤ (Real.exp 1 * P ^ (-β)) * (2 / (β / H)) := by
      rw [div_eq_mul_inv, ← one_div]
      exact mul_le_mul hpower hden (le_of_lt (one_div_pos.mpr hgap)) (by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

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

/-- The complete first-band scalar sum; the number of coarse bins does
not appear in the geometric part of the bound. -/
theorem mrt_log_bin_weighted_sum {β H P Q N T : ℝ}
    (hβ : 0 < β) (hH : 0 < H) (hβH : β ≤ H)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hN : 0 < N) (hT : 0 ≤ T) :
    (∑ k ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊,
      Real.exp (-β * (k : ℝ) / H) * (T * mrtPrimeLogLower H k / N + 1)) ≤
      ((2 * Real.exp 1 * H / β) * P ^ (-β)) * (T * Q / N + 1) := by
  calc
    _ ≤ ∑ k ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊,
        Real.exp (-β * (k : ℝ) / H) * (T * Q / N + 1) := by
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mrt_prime_log_lower_le_upper hH hQ (mem_Icc.mp hk).2) hT)
        hN.le
    _ = (∑ k ∈ Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊,
        Real.exp (-β * (k : ℝ) / H)) * (T * Q / N + 1) := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mrt_first_band_exponential_sum hβ hH hβH hP _) (by positivity)

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

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBandCostSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual amplified cofactor cost over the preceding
witness bins and current small-polynomial bins. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_mixed_bin_cost_bound {η P Q Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hYlo : Real.exp (-1) * mrtBandLower P Q (j + 1) ≤ Y)
    (hYhi : Y ≤ mrtBandUpper Q (j + 1))
    (hulo : Real.exp (-1) * mrtBandLower P Q (j + 2) ≤ u)
    (huhi : u ≤ mrtBandUpper Q (j + 2)) (hτ : 0 ≤ τ) :
    mrtMixedBinCost η j τ Y u ≤ 16 * Real.exp 10 * (τ + 1) *
      Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have he : Real.exp (-mrtFrequencyExponent η (j + 1) * Real.log u) ^ 2 =
      Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hb := mul_le_mul_of_nonneg_left
    (mrt_actual_band_mixed_bound hη hη' j hP hQ hbudget hYlo hYhi hulo huhi hτ)
    (show 0 ≤ 16 * Real.exp 10 by positivity)
  unfold mrtMixedBinCost
  rw [he]
  first | (convert hb using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hb.trans (le_of_eq (by ring)))

theorem mrt_mixed_bin_cost_sum {β κ : Type*} (B : Finset β) (K : Finset κ)
    (Y : β → ℝ) (u : κ → ℝ) {η P Q τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hY : ∀ b ∈ B, Real.exp (-1) * mrtBandLower P Q (j + 1) ≤ Y b ∧
      Y b ≤ mrtBandUpper Q (j + 1))
    (hu : ∀ k ∈ K, Real.exp (-1) * mrtBandLower P Q (j + 2) ≤ u k ∧
      u k ≤ mrtBandUpper Q (j + 2)) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, mrtMixedBinCost η j τ (Y b) (u k) ≤
      32 * Real.exp 10 * (τ + 1) * B.card * K.card *
        ∑ k ∈ K, Real.exp (-η * Real.log (u k) / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hb (b : β) (hmem : b ∈ B) :
      (K.card : ℝ) * ∑ k ∈ K, mrtMixedBinCost η j τ (Y b) (u k) ≤
      (K.card : ℝ) * (16 * Real.exp 10 * (τ + 1) *
        ∑ k ∈ K, Real.exp (-η * Real.log (u k) / (2 * ((j : ℝ) + 2) ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact mrt_mixed_bin_cost_bound hη hη' j hP hQ hbudget
      (hY b hmem).1 (hY b hmem).2 (hu k hk).1 (hu k hk).2 hτ
  calc
    _ ≤ 2 * ∑ b ∈ B, (K.card : ℝ) * (16 * Real.exp 10 * (τ + 1) *
        ∑ k ∈ K, Real.exp (-η * Real.log (u k) / (2 * ((j : ℝ) + 2) ^ 2))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hb) (by norm_num)
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBinMomentSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite witness-bin sum. Both bin cardinalities and the
remaining exponential sum are bounded using their actual endpoints. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem mrt_actual_bin_moment_sum {η P Q τ H₀ H₁ : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH₀ : 2 ≤ H₀) (hH₁ : 2 ≤ H₁) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ mrtLogBins H₀ (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1)),
      ((mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))).card : ℝ) *
        ∑ k ∈ mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2)),
          mrtMixedBinCost η j τ (mrtPrimeLogLower H₀ b) (mrtPrimeLogLower H₁ k) ≤
      64 * Real.exp 11 * (τ + 1) *
        (H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1) *
        (H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1) *
        (H₁ / (η / (2 * ((j : ℝ) + 2) ^ 2))) *
        (mrtBandLower P Q (j + 2)) ^ (-(η / (2 * ((j : ℝ) + 2) ^ 2))) := by
  let B := mrtLogBins H₀ (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1))
  let K := mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))
  let β : ℝ := η / (2 * ((j : ℝ) + 2) ^ 2)
  have hβ : 0 < β := by dsimp [β] <;> positivity
  have hβH : β ≤ H₁ := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hd : 1 ≤ 2 * ((j : ℝ) + 2) ^ 2 := by nlinarith [sq_nonneg (j : ℝ)]
    have hh := div_le_self hη.le hd
    dsimp [β]
    linarith
  have hUpper (k : ℕ) : 1 ≤ mrtBandUpper Q (k + 1) := by
    apply Real.one_le_exp
    have hk : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg _
    exact mul_nonneg (pow_nonneg hk _) (pow_nonneg (by linarith : 0 ≤ Real.log Q) _)
  have hLower (k : ℕ) : 1 ≤ mrtBandLower P Q (k + 1) := by
    apply Real.one_le_exp
    positivity
  have hU₂ : 1 ≤ mrtBandUpper Q (j + 2) := by
    simpa only [Nat.add_assoc] using hUpper (j + 1)
  have hL₂ : 1 ≤ mrtBandLower P Q (j + 2) := by
    simpa only [Nat.add_assoc] using hLower (j + 1)
  have hcB := mrt_log_bin_card (P := mrtBandLower P Q (j + 1))
    (by linarith : 0 ≤ H₀) (hUpper j)
  have hcK := mrt_log_bin_card (P := mrtBandLower P Q (j + 2))
    (by linarith : 0 ≤ H₁) hU₂
  have hh := mrt_mixed_bin_cost_sum B K (mrtPrimeLogLower H₀) (mrtPrimeLogLower H₁)
    hη.le hη' j hP hQ hbudget
    (fun b hb => mrt_log_bin_endpoints (by linarith) (Real.exp_pos _) (hUpper j) hb)
    (fun k hk => mrt_log_bin_endpoints (by linarith) (Real.exp_pos _) hU₂ hk) hτ
  have hs := mrt_first_band_exponential_sum hβ (by linarith : 0 < H₁)
    hβH hL₂ ⌊H₁ * Real.log (mrtBandUpper Q (j + 2))⌋₊
  have he (k : ℕ) :
      -η * Real.log (mrtPrimeLogLower H₁ k) / (2 * ((j : ℝ) + 2) ^ 2) =
        -β * (k : ℝ) / H₁ := by
    simp only [mrtPrimeLogLower, Real.log_exp]
    dsimp [β]
    ring
  simp_rw [he] at hh
  apply hh.trans
  have hnB : 0 ≤ H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1 :=
    (Nat.cast_nonneg B.card).trans hcB
  have hnK : 0 ≤ H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1 :=
    (Nat.cast_nonneg K.card).trans hcK
  calc
    _ ≤ 32 * Real.exp 10 * (τ + 1) *
        (H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1) *
        (H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1) *
        ((2 * Real.exp 1 * H₁ / β) * (mrtBandLower P Q (j + 2)) ^ (-β)) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hcB (by positivity)
        · exact hcK
        · exact Nat.cast_nonneg K.card
        · positivity
      · exact hs
      · exact sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      · positivity
    _ = _ := by
      rw [show Real.exp 11 = Real.exp 10 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      dsimp [β]
      ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTResolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

lemma mrtResolution_one (P Q η : ℝ) : mrtResolution P Q η 1 = mrtBaseResolution P Q η := by
  simp [mrtResolution]

lemma mrtResolution_pos (P Q η : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    0 < mrtResolution P Q η j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  exact mul_pos (sq_pos_of_pos hj0) (mrtBaseResolution_pos P Q η)

lemma mrt_base_resolution_le {P Q η : ℝ} (hP : 1 ≤ P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) : mrtBaseResolution P Q η ≤ P := by
  have hp0 : 0 < P := by linarith
  have hlp := Real.log_nonneg hP
  have hlq := Real.log_nonneg hQ
  have he : (1 / 6 - η) * Real.log P - (1 / 3) * Real.log (Real.log Q) ≤
      Real.log P := by nlinarith [mul_nonneg hη hlp]
  exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_log hp0)

lemma mrt_resolution_le {P Q η : ℝ} (hP : 1 ≤ P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) (j : ℕ) :
    mrtResolution P Q η j ≤ (j : ℝ) ^ 2 * P :=
  mul_le_mul_of_nonneg_left (mrt_base_resolution_le hP hQ hη) (sq_nonneg _)

lemma mrt_base_resolution_balance (P Q η : ℝ) (hQ : 1 < Q) :
    mrtBaseResolution P Q η ^ 3 * Real.log Q *
        Real.exp (-2 * mrtFrequencyExponent η 0 * Real.log P) = 1 := by
  have hq : 0 < Real.log Q := Real.log_pos hQ
  unfold mrtBaseResolution
  rw [← Real.exp_nat_mul]
  have he : (3 : ℝ) * ((1 / 6 - η) * Real.log P -
      (1 / 3) * Real.log (Real.log Q)) + Real.log (Real.log Q) +
      (-2 * mrtFrequencyExponent η 0 * Real.log P) = 0 := by
    rw [mrtFrequencyExponent_zero]
    ring
  calc
    _ = Real.exp (3 * ((1 / 6 - η) * Real.log P -
          (1 / 3) * Real.log (Real.log Q))) * Real.exp (Real.log (Real.log Q)) *
        Real.exp (-2 * mrtFrequencyExponent η 0 * Real.log P) := by
      rw [Real.exp_log hq]
      norm_num
    _ = Real.exp (3 * ((1 / 6 - η) * Real.log P -
          (1 / 3) * Real.log (Real.log Q)) + Real.log (Real.log Q) +
          (-2 * mrtFrequencyExponent η 0 * Real.log P)) := by
      rw [Real.exp_add, Real.exp_add]
    _ = 1 := by rw [he, Real.exp_zero]

lemma mrt_base_resolution_first_cost (P Q η : ℝ) (hQ : 1 < Q) :
    mrtBaseResolution P Q η ^ 2 * Real.log Q *
        Real.exp (-2 * mrtFrequencyExponent η 0 * Real.log P) =
      (mrtBaseResolution P Q η)⁻¹ := by
  have hh := mrt_base_resolution_balance P Q η hQ
  have hH := mrtBaseResolution_pos P Q η
  rw [← one_div]
  apply (eq_div_iff hH.ne').mpr
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTFirstBinSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first small-prime frequency class has exactly the reciprocal
resolution saving dictated by the cubic balance. -/

namespace TwoPointCorrelations

open Finset

theorem mrt_first_bin_moment_sum {η P Q N T : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 12) (hP : 1 ≤ P) (hQ0 : 0 < Q) (hQ : 1 ≤ Real.log Q)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < N) (hT : 0 ≤ T) :
    64 * Real.exp 1 * ((mrtLogBins (mrtBaseResolution P Q η) P Q).card : ℝ) *
        ∑ k ∈ mrtLogBins (mrtBaseResolution P Q η) P Q,
          (Real.exp (-mrtFrequencyExponent η 0 *
              Real.log (mrtPrimeLogLower (mrtBaseResolution P Q η) k))) ^ 2 *
            (T * mrtPrimeLogLower (mrtBaseResolution P Q η) k / N + 1) ≤
      1024 * Real.exp 2 * (T * Q / N + 1) * (mrtBaseResolution P Q η)⁻¹ := by
  let H := mrtBaseResolution P Q η
  let β := 2 * mrtFrequencyExponent η 0
  have hβ : 1 / 4 ≤ β := by
    dsimp [β]
    rw [mrtFrequencyExponent_zero]
    linarith
  have hβ' : β ≤ 1 / 2 := by
    dsimp [β]
    rw [mrtFrequencyExponent_zero]
    linarith
  have hH0 : 0 < H := mrtBaseResolution_pos P Q η
  have hQ1 : 1 < Q := by
    have hh : 1 < Real.exp (Real.log Q) := Real.one_lt_exp_iff.mpr (by linarith)
    simpa only [Real.exp_log hQ0] using hh
  have he (k : ℕ) :
      (Real.exp (-mrtFrequencyExponent η 0 * Real.log (mrtPrimeLogLower H k))) ^ 2 =
        Real.exp (-β * (k : ℝ) / H) := by
    rw [← Real.exp_nat_mul]
    simp only [mrtPrimeLogLower, Real.log_exp]
    dsimp [β]
    congr 1
    ring
  dsimp only [H] at he
  simp_rw [he]
  have hs := mrt_log_bin_weighted_sum (by linarith : 0 < β) hH0
    (by dsimp [H]; linarith : β ≤ H) hP hQ1.le hN hT
  have hc := mrt_log_bin_card (P := P) hH0.le hQ1.le
  have hc' : ((mrtLogBins H P Q).card : ℝ) ≤ 2 * H * Real.log Q := by
    have hh : 1 ≤ H * Real.log Q := by dsimp [H] <;> nlinarith
    change ((Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card : ℝ) ≤ _
    linarith
  have hi : 1 / β ≤ 4 := (div_le_iff₀ (by linarith : 0 < β)).mpr (by linarith)
  have hbalance : H ^ 2 * Real.log Q * P ^ (-β) = H⁻¹ := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < P)]
    dsimp [β, H]
    rw [show Real.log P * -(2 * mrtFrequencyExponent η 0) =
      -2 * mrtFrequencyExponent η 0 * Real.log P by ring]
    exact mrt_base_resolution_first_cost P Q η hQ1
  calc
    _ ≤ 64 * Real.exp 1 * (2 * H * Real.log Q) *
        (((2 * Real.exp 1 * H / β) * P ^ (-β)) * (T * Q / N + 1)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hc' (by positivity)
      · exact hs
      · exact sum_nonneg (fun _ _ => mul_nonneg (Real.exp_pos _).le
          (by unfold mrtPrimeLogLower; positivity))
      · positivity
    _ = 256 * Real.exp 2 * (T * Q / N + 1) *
        (H ^ 2 * Real.log Q * P ^ (-β)) * (1 / β) := by
      rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      ring
    _ ≤ 256 * Real.exp 2 * (T * Q / N + 1) * H⁻¹ * 4 := by
      rw [hbalance]
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [H] <;> ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBandPowerSaving
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The later-band exponential is much smaller than the remaining
polynomial bin factors, uniformly in the band index. -/

namespace TwoPointCorrelations

lemma mrt_log_later_band_lower (P Q : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) :
    (k : ℝ) ^ 8 * Real.log Q * Real.log P ≤
      Real.log (mrtBandLower P Q k) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hpow : (k : ℝ) ^ 8 ≤ (k : ℝ) ^ (4 * k) :=
    pow_le_pow_right₀ hk1 (by omega)
  have hq : Real.log Q ≤ Real.log Q ^ (k - 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hQ (show 1 ≤ k - 1 by omega)
  simp only [mrtBandLower, Real.log_exp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hpow hq (by linarith) (by positivity)) hP

theorem mrt_later_band_exponential_budget {η P Q : ℝ} (hη : 0 ≤ η)
    (k : ℕ) (hk : 2 ≤ k) (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 ≤ η * Real.log Q) :
    2048 * (k : ℝ) ^ 6 * Real.log P ≤
      η * Real.log (mrtBandLower P Q k) / (4 * (k : ℝ) ^ 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h1 := mul_le_mul_of_nonneg_left (mrt_log_later_band_lower P Q k hk hP hQ) hη
  have h2 := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ (k : ℝ) ^ 8 * Real.log P by positivity)
  apply (le_div_iff₀ (by positivity : 0 < 4 * (k : ℝ) ^ 2)).mpr
  have he : (2048 * (k : ℝ) ^ 6 * Real.log P) * (4 * (k : ℝ) ^ 2) =
      8192 * (k : ℝ) ^ 8 * Real.log P := by ring
  rw [he]
  nlinarith

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTBinPrefactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

lemma mrt_bin_prefactor_exponential {P L η k : ℝ}
    (hk : 2 ≤ k) (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hL : 1 ≤ L) (hη : 0 < η)
    (hlogL : Real.log L ≤ 8 * k ^ 2 * Real.log P)
    (hinv : η⁻¹ ≤ Real.log P) :
    512 * Real.exp 11 * k ^ 8 * P ^ 3 * L ^ 2 / η ≤
      Real.exp (1024 * k ^ 2 * Real.log P) := by
  have hk0 : 0 ≤ k := by linarith
  have hc : (512 : ℝ) ≤ Real.exp 512 := by
    linarith [Real.add_one_le_exp (512 : ℝ)]
  have hkexp : k ^ 8 ≤ Real.exp (8 * k) := by
    have hh : k ≤ Real.exp k := by linarith [Real.add_one_le_exp k]
    exact (pow_le_pow_left₀ hk0 hh 8).trans_eq (Real.exp_nat_mul k 8).symm
  have hpexp : P ^ 3 = Real.exp (3 * Real.log P) := by
    rw [show Real.exp (3 * Real.log P) = (Real.exp (Real.log P)) ^ 3 by
      simpa using Real.exp_nat_mul (Real.log P) 3, Real.exp_log hP0]
  have hLexp : L ^ 2 ≤ Real.exp (16 * k ^ 2 * Real.log P) := by
    calc
      L ^ 2 = Real.exp (2 * Real.log L) := by
        rw [show Real.exp (2 * Real.log L) = (Real.exp (Real.log L)) ^ 2 by
          simpa using Real.exp_nat_mul (Real.log L) 2, Real.exp_log (by linarith : 0 < L)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hPexp := hpexp.le
  have hηexp : η⁻¹ ≤ Real.exp (Real.log P) :=
    hinv.trans (by linarith [Real.add_one_le_exp (Real.log P)])
  have hk2 : k ≤ k ^ 2 := by nlinarith
  have hk2p : k ≤ k ^ 2 * Real.log P := by nlinarith
  have hpp : Real.log P ≤ k ^ 2 * Real.log P := by
    nlinarith [mul_nonneg (show 0 ≤ k ^ 2 - 1 by nlinarith) (by linarith : 0 ≤ Real.log P)]
  have hbase : 8 ≤ k ^ 2 * Real.log P := by
    nlinarith [mul_nonneg (show 0 ≤ k ^ 2 - 4 by nlinarith) (by linarith : 0 ≤ Real.log P - 2)]
  calc
    _ = 512 * Real.exp 11 * k ^ 8 * P ^ 3 * L ^ 2 * η⁻¹ := by ring
    _ ≤ Real.exp 512 * Real.exp 11 * Real.exp (8 * k) *
        Real.exp (3 * Real.log P) * Real.exp (16 * k ^ 2 * Real.log P) *
        Real.exp (Real.log P) := by gcongr
    _ = Real.exp (523 + 8 * k + 4 * Real.log P + 16 * k ^ 2 * Real.log P) := by
      simp only [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem mrt_actual_bin_prefactor {η P Q : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 6)
    (k : ℕ) (hk : 2 ≤ k) (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P) :
    64 * Real.exp 11 *
        (mrtResolution P Q η (k - 1) * Real.log (mrtBandUpper Q (k - 1)) + 1) *
        (mrtResolution P Q η k * Real.log (mrtBandUpper Q k) + 1) *
        (mrtResolution P Q η k / (η / (2 * (k : ℝ) ^ 2))) ≤
      Real.exp (1024 * (k : ℝ) ^ 2 * Real.log P) := by
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hP1 : 1 ≤ P := (Real.one_lt_exp_iff.mpr (by linarith : 0 < Real.log P)).le.trans_eq
    (Real.exp_log hP0)
  have hy : 1 ≤ Real.log (Real.log Q) + 1 := by linarith [Real.log_nonneg hQ]
  have hpη : 1 ≤ η * Real.log P := by nlinarith
  have hinv : η⁻¹ ≤ Real.log P := by
    rw [← one_div, div_le_iff₀ hη]
    nlinarith
  have hyP : Real.log (Real.log Q) + 1 ≤ Real.log P := by
    nlinarith [mul_le_mul_of_nonneg_right hη' (by linarith : 0 ≤ Real.log P)]
  have hL : 1 ≤ Real.log (mrtBandUpper Q k) :=
    (show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega)).trans
      (mrt_band_index_le_log_upper Q k (by omega) hQ)
  have hlogL : Real.log (Real.log (mrtBandUpper Q k)) ≤
      8 * (k : ℝ) ^ 2 * Real.log P := by
    have hh := mrt_log_log_band_upper Q k (by omega) hQ
    have hh' := mul_le_mul_of_nonneg_left hyP (show 0 ≤ 8 * (k : ℝ) ^ 2 by positivity)
    linarith
  have hH₁ := mrt_resolution_le hP1 hQ hη.le k
  have hH₀ : mrtResolution P Q η (k - 1) ≤ (k : ℝ) ^ 2 * P := by
    apply (mrt_resolution_le hP1 hQ hη.le (k - 1)).trans
    gcongr
    exact_mod_cast Nat.sub_le k 1
  have hU := mrt_log_band_upper_mono hQ (show 1 ≤ k - 1 by omega) (Nat.sub_le k 1)
  have hH₀0 : 0 ≤ mrtResolution P Q η (k - 1) := (mrtResolution_pos P Q η (by omega)).le
  have hH₁0 : 0 ≤ mrtResolution P Q η k := (mrtResolution_pos P Q η (by omega)).le
  have hU₀0 : 0 ≤ Real.log (mrtBandUpper Q (k - 1)) := by
    have hh := mrt_band_index_le_log_upper Q (k - 1) (by omega) hQ
    exact (Nat.cast_nonneg _).trans hh
  have hB : 1 ≤ (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by nlinarith) hP1) hL
  have hF₀ : mrtResolution P Q η (k - 1) * Real.log (mrtBandUpper Q (k - 1)) + 1 ≤
      2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k) := by
    have hh := mul_le_mul hH₀ hU hU₀0 (by positivity : 0 ≤ (k : ℝ) ^ 2 * P)
    nlinarith
  have hF₁ : mrtResolution P Q η k * Real.log (mrtBandUpper Q k) + 1 ≤
      2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k) := by
    have hh := mul_le_mul_of_nonneg_right hH₁ (by linarith : 0 ≤ Real.log (mrtBandUpper Q k))
    nlinarith
  calc
    _ ≤ 64 * Real.exp 11 *
        (2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k)) *
        (2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k)) *
        (((k : ℝ) ^ 2 * P) / (η / (2 * (k : ℝ) ^ 2))) := by gcongr
    _ = 512 * Real.exp 11 * (k : ℝ) ^ 8 * P ^ 3 *
        Real.log (mrtBandUpper Q k) ^ 2 / η := by field_simp <;> ring
    _ ≤ _ := mrt_bin_prefactor_exponential hk1 hP0 hP hL hη hlogL hinv

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTLaterBinSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The later frequency classes have a summable bound, with the true
resolution and all witness-bin choices included. -/

namespace TwoPointCorrelations

open Finset

lemma mrt_later_bin_prefactor_saving {η P Q : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 6)
    (k : ℕ) (hk : 2 ≤ k) (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P) :
    (64 * Real.exp 11 *
        (mrtResolution P Q η (k - 1) * Real.log (mrtBandUpper Q (k - 1)) + 1) *
        (mrtResolution P Q η k * Real.log (mrtBandUpper Q k) + 1) *
        (mrtResolution P Q η k / (η / (2 * (k : ℝ) ^ 2)))) *
        (mrtBandLower P Q k) ^ (-(η / (2 * (k : ℝ) ^ 2))) ≤
      P⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hy : 1 ≤ Real.log (Real.log Q) + 1 := by linarith [Real.log_nonneg hQ]
  have hηQ : 8192 ≤ η * Real.log Q := by
    have hh := mul_le_mul_of_nonneg_left hPQ hη.le
    nlinarith
  have hlarge := mrt_later_band_exponential_budget (P := P) (Q := Q) hη.le k hk
    (by linarith) hQ hηQ
  have hkpow : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 6 := pow_le_pow_right₀ hk1 (by norm_num)
  have hkp : (k : ℝ) ≤ (k : ℝ) ^ 2 * Real.log P := by
    have hh : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hpp : Real.log P ≤ (k : ℝ) ^ 2 * Real.log P := by
    have hh : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
    nlinarith
  have hlogk : Real.log (k : ℝ) ≤ k :=
    (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  have hsave : 1024 * (k : ℝ) ^ 2 * Real.log P + Real.log P + 2 * Real.log (k : ℝ) ≤
      η * Real.log (mrtBandLower P Q k) / (2 * (k : ℝ) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hkpow (by linarith : 0 ≤ Real.log P)
    have he : η * Real.log (mrtBandLower P Q k) / (2 * (k : ℝ) ^ 2) =
        2 * (η * Real.log (mrtBandLower P Q k) / (4 * (k : ℝ) ^ 2)) := by ring
    rw [he]
    nlinarith
  have hL0 : 0 < mrtBandLower P Q k := Real.exp_pos _
  calc
    _ ≤ Real.exp (1024 * (k : ℝ) ^ 2 * Real.log P) *
        (mrtBandLower P Q k) ^ (-(η / (2 * (k : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_right (mrt_actual_bin_prefactor hη hη' k hk hP0 hP hQ hbudget)
        (Real.rpow_nonneg hL0.le _)
    _ = Real.exp (1024 * (k : ℝ) ^ 2 * Real.log P -
        η * Real.log (mrtBandLower P Q k) / (2 * (k : ℝ) ^ 2)) := by
      rw [Real.rpow_def_of_pos hL0, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log P - 2 * Real.log (k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = P⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
      rw [Real.exp_sub, Real.exp_neg, Real.exp_log hP0,
        show Real.exp (2 * Real.log (k : ℝ)) = (Real.exp (Real.log (k : ℝ))) ^ 2 by
          simpa using Real.exp_nat_mul (Real.log (k : ℝ)) 2,
        Real.exp_log hk0]
      ring

theorem mrt_later_bin_moment_sum {η P Q τ : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ mrtLogBins (mrtResolution P Q η (j + 1))
        (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1)),
      ((mrtLogBins (mrtResolution P Q η (j + 2))
        (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))).card : ℝ) *
      ∑ k ∈ mrtLogBins (mrtResolution P Q η (j + 2))
        (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2)),
        mrtMixedBinCost η j τ
          (mrtPrimeLogLower (mrtResolution P Q η (j + 1)) b)
          (mrtPrimeLogLower (mrtResolution P Q η (j + 2)) k) ≤
      (τ + 1) * P⁻¹ * (((j : ℝ) + 2) ^ 2)⁻¹ := by
  have hresolution (k : ℕ) (hk : 1 ≤ k) : 2 ≤ mrtResolution P Q η k := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hpow : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
    dsimp [mrtResolution]
    nlinarith [mrtBaseResolution_pos P Q η]
  have hh := mrt_actual_bin_moment_sum hη hη' j hP hQ hbudget
    (hresolution (j + 1) (by omega)) (hresolution (j + 2) (by omega)) hτ
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_left
    (mrt_later_bin_prefactor_saving hη hη' (j + 2) (by omega) hP0 hP hQ hPQ hbudget)
    (show 0 ≤ τ + 1 by linarith)
  have hj : j + 2 - 1 = j + 1 := by omega
  simp only [hj, Nat.cast_add, Nat.cast_ofNat] at hs
  first | (convert hs using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hs.trans (le_of_eq (by ring)))

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CanonicalMellinBands
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

lemma canonical_band_lower_ge {P Q : ℝ} (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hlogP : 1 < Real.log P) (j : ℕ) : P ≤ mrtBandLower P Q (j+1) := by
  have hh := mrt_band_lower_monotone P Q 1 (j+1) (by omega) (by omega) hP hPQ hlogP
  simpa only [mrtBandLower_one P Q (by linarith)] using hh

/-- The entire finite family satisfies the geometric hypotheses of the
proved Ramaré partition as soon as its upper endpoints lie below `N/2`. -/
theorem canonicalMellinBands_valid {P Q η : ℝ} {J N : ℕ}
    (hP : 2 * Real.exp 1 ≤ P) (hPQ : P ≤ Q)
    (hlogP : 1 < Real.log P) (hH : 2 ≤ mrtBaseResolution P Q η)
    (hN : ∀ j ∈ range J, 2 * mrtBandUpper Q (j+1) ≤ N) :
    (canonicalMellinBands P Q η).Valid J N := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hP2 : 2 ≤ P := by nlinarith
  have hP0 : 0 < P := by linarith
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log hP0 hPQ)
  have hHj (j : ℕ) := canonical_resolution_ge_two hH j
  have hL (j : ℕ) := canonical_band_lower_ge hP2 hPQ hlogP j
  have hU (j : ℕ) : 1 ≤ mrtBandUpper Q (j+1) :=
    (show 1 ≤ (2:ℝ) by norm_num).trans
      ((mrt_band_endpoints P Q (j+1) (by omega) hP2 hPQ hlogQ).1.trans
        (mrt_band_endpoints P Q (j+1) (by omega) hP2 hPQ hlogQ).2)
  constructor
  · intro j _ p hp
    exact mrtPrimeBand_prime hp
  · intro i hi j hj hij
    apply disjoint_left.mpr
    intro p hpi hpj
    have hip := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hpi
    have hjp := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hpj
    change mrtBandLower P Q (i+1) < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q (i+1) at hip
    change mrtBandLower P Q (j+1) < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q (j+1) at hjp
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hh := mrt_band_gap P Q (i+1) (j+1) (by omega) (by omega) hP2 hPQ hlogP
      linarith
    · have hh := mrt_band_gap P Q (j+1) (i+1) (by omega) (by omega) hP2 hPQ hlogP
      linarith
  · intro j _ p hp
    have hb := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp
    exact mrt_prime_log_bin_range (by linarith [hHj j]) (Real.exp_pos _) hb.1.le hb.2
  · intro j _
    exact (mrt_prime_log_width (hHj j)).1
  · intro j _
    exact (mrt_prime_log_width (hHj j)).2.1
  · intro j _ p hp
    exact mrt_prime_log_bin_bounds (by linarith [hHj j]) (mrtPrimeBand_prime hp).one_le
  · intro j _ k hk
    have hh := mrt_log_bin_lower_endpoint (by linarith [hHj j])
      (Real.exp_pos ((j+1 : ℕ) ^ (4*(j+1)) * Real.log Q ^ j * Real.log P))
      (mem_Icc.mp hk).1
    have heq : Real.exp (-1) * (2 * Real.exp 1) = 2 := by
      rw [mul_left_comm, ← Real.exp_add]
      norm_num
    calc
      2 = Real.exp (-1) * (2 * Real.exp 1) := heq.symm
      _ ≤ Real.exp (-1) * mrtBandLower P Q (j+1) :=
        mul_le_mul_of_nonneg_left (hP.trans (hL j)) (Real.exp_pos _).le
      _ ≤ _ := hh
  · intro j hj k hk
    have hh := mrt_prime_log_lower_le_upper (by linarith [hHj j]) (hU j) (mem_Icc.mp hk).2
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans (hN j hj)
  · intro j _ k _
    exact Real.exp_pos _

theorem canonical_initialCost_le {P Q η : ℝ} (N : ℕ) {T : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1/12) (hP : 1 ≤ P) (hQ0 : 0 < Q)
    (hQ : 1 ≤ Real.log Q) (hH : 2 ≤ mrtBaseResolution P Q η)
    (hN : 0 < (N : ℝ)) (hT : 0 ≤ T) :
    (canonicalMellinBands P Q η).initialCost N T ≤
      1024 * Real.exp 2 * (T * Q / N + 1) * (mrtBaseResolution P Q η)⁻¹ := by
  simpa only [MellinPrimeBands.initialCost, canonicalMellinBands,
    Nat.zero_add, mrtResolution_one, mrtBandLower_one P Q (by linarith),
    mrtBandUpper_one Q hQ0] using mrt_first_bin_moment_sum hη hη' hP hQ0 hQ hH hN hT

lemma canonical_laterCost_eq (P Q η : ℝ) (j N : ℕ) (T : ℝ) :
    (canonicalMellinBands P Q η).laterCost (j+1) N T =
      2 * ∑ b ∈ mrtLogBins (mrtResolution P Q η (j+1))
        (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1)),
      ((mrtLogBins (mrtResolution P Q η (j+2))
        (mrtBandLower P Q (j+2)) (mrtBandUpper Q (j+2))).card : ℝ) *
        ∑ k ∈ mrtLogBins (mrtResolution P Q η (j+2))
          (mrtBandLower P Q (j+2)) (mrtBandUpper Q (j+2)),
        mrtMixedBinCost η j (T / N)
          (mrtPrimeLogLower (mrtResolution P Q η (j+1)) b)
          (mrtPrimeLogLower (mrtResolution P Q η (j+2)) k) := by
  dsimp only [MellinPrimeBands.laterCost, canonicalMellinBands]
  simp only [Nat.add_sub_cancel, show j+1+1 = j+2 by omega]
  congr 1

theorem canonical_laterCost_le {P Q η : ℝ} (j N : ℕ) {T : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1/6) (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (hPQ : Real.log P ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hT : 0 ≤ T) :
    (canonicalMellinBands P Q η).laterCost (j+1) N T ≤
      (T / N + 1) * P⁻¹ * (((j : ℝ)+2)^2)⁻¹ := by
  rw [canonical_laterCost_eq]
  exact mrt_later_bin_moment_sum hη hη' j hP0 hP hQ hPQ hbudget hH
    (div_nonneg hT (Nat.cast_nonneg N))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeBandExtractionCost
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summability of all prime-square and width errors in the MRT bands -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma sum_range_succ_eq_Icc (f : ℕ → ℝ) (J : ℕ) :
    (∑ j ∈ range J, f (j+1)) = ∑ j ∈ Icc 1 J, f j := by
  apply sum_bij (fun j _ => j+1)
  · intro j hj
    exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩
  · intro j _ k _ hjk
    omega
  · intro j hj
    refine ⟨j-1, mem_range.mpr (by have := mem_Icc.mp hj; omega), ?_⟩
    have := mem_Icc.mp hj
    omega
  · intro j _
    rfl

lemma sum_range_succ_inv_sq_le (J : ℕ) :
    (∑ j ∈ range J, (((j+1 : ℕ) : ℝ)^2)⁻¹) ≤ 2 := by
  rw [sum_range_succ_eq_Icc (fun j => ((j : ℝ)^2)⁻¹) J]
  have he : Icc 1 J = Ioo 0 (J+1) := by ext j; simp; omega
  rw [he]
  simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (J+1)

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

lemma mrt_band_lower_ge_square {P Q : ℝ} (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (j : ℕ) (hj : 1 ≤ j) :
    P * (j : ℝ)^2 ≤ mrtBandLower P Q j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hp : (j : ℝ)^2 ≤ (j : ℝ)^(4*j) :=
    pow_le_pow_right₀ hj1 (by omega)
  have hq : 1 ≤ Real.log Q^(j-1) := one_le_pow₀ hQ
  have hexp : Real.log P + 2*Real.log (j : ℝ) ≤
      (j : ℝ)^(4*j) * Real.log Q^(j-1) * Real.log P := by
    have hjlog := Real.log_le_sub_one_of_pos hj0
    have hm : (j : ℝ)^2 ≤ (j : ℝ)^(4*j) * Real.log Q^(j-1) := by
      nlinarith [pow_nonneg hj0.le (4*j)]
    have hh := mul_le_mul_of_nonneg_right hm (by linarith : 0 ≤ Real.log P)
    have hz : 0 ≤ ((j : ℝ)^2-1)*(Real.log P-2) :=
      mul_nonneg (by nlinarith) (by linarith)
    nlinarith [sq_nonneg ((j : ℝ)-1)]
  calc
    _ = Real.exp (Real.log P + 2*Real.log (j : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hP0, show Real.exp (2*Real.log (j : ℝ)) =
        (Real.exp (Real.log (j : ℝ)))^2 by simpa using Real.exp_nat_mul (Real.log (j : ℝ)) 2,
        Real.exp_log hj0]
    _ ≤ _ := Real.exp_le_exp.mpr hexp

lemma canonical_square_mass_le {P Q η : ℝ} (hP0 : 0 < P)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) (hPQ : P ≤ Q) (j : ℕ) :
    (∑ p ∈ (canonicalMellinBands P Q η).primes j, 1/(p : ℝ)^2) ≤
      (2/P) * (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
  have he2 : 2 ≤ P := by
    have he := Real.add_one_le_exp (2 : ℝ)
    have hh := Real.exp_le_exp.mpr hP
    rw [Real.exp_log hP0] at hh
    linarith
  have hL := mrt_band_lower_ge_square hP0 hP hQ (j+1) (by omega)
  have hl := mrt_band_endpoints P Q (j+1) (by omega) he2 hPQ hQ
  have hsq : (0 : ℝ) < ((j+1 : ℕ) : ℝ)^2 := by positivity
  apply (primeBand_square_mass_le hl.1 hl.2).trans
  calc
    _ ≤ 2/(P*((j+1 : ℕ) : ℝ)^2) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hP0 hsq) hL
    _ = _ := by ring

lemma canonical_square_mass_le_one {P Q η : ℝ} (hP0 : 0 < P)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) (hPQ : P ≤ Q) (j : ℕ) :
    (∑ p ∈ (canonicalMellinBands P Q η).primes j, 1/(p : ℝ)^2) ≤ 1 := by
  have hh := canonical_square_mass_le (η := η) hP0 hP hQ hPQ j
  have hP2 : 2 ≤ P := by
    have hh := Real.exp_le_exp.mpr hP
    rw [Real.exp_log hP0] at hh
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hj : (1 : ℝ) ≤ ((j+1 : ℕ) : ℝ)^2 := by
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ j+1 by omega))
  have h1 : 2/P ≤ 1 := (div_le_one hP0).mpr hP2
  have h2 : (((j+1 : ℕ) : ℝ)^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj
  exact hh.trans ((mul_le_mul h1 h2 (by positivity) zero_le_one).trans_eq (one_mul 1))

theorem canonical_extraction_sum_le {P Q η : ℝ} (J N : ℕ) {T : ℝ}
    (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) (hPQ : P ≤ Q)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hT : 0 ≤ T) :
    (∑ j ∈ range J, (canonicalMellinBands P Q η).extractionCost j N T) ≤
      2816 * Real.exp 1 * (T/N+1) * (8/P + 4/(mrtBaseResolution P Q η)) := by
  let D := canonicalMellinBands P Q η
  have hterm (j : ℕ) : D.extractionCost j N T ≤
      (2816 * Real.exp 1 * (T/N+1)) *
        ((4/P + 2/(mrtBaseResolution P Q η)) * (((j+1 : ℕ) : ℝ)^2)⁻¹) := by
    have hm0 : 0 ≤ ∑ p ∈ D.primes j, 1/(p : ℝ)^2 := by positivity
    have hm1 := canonical_square_mass_le_one (η := η) hP0 hP hQ hPQ j
    have hm := canonical_square_mass_le (η := η) hP0 hP hQ hPQ j
    have hw := (mrt_prime_log_width (canonical_resolution_ge_two hH j)).2.2
    change D.resolution j - 1 ≤ 2 / mrtResolution P Q η (j+1) at hw
    have he : 2 / mrtResolution P Q η (j+1) =
        (2 / mrtBaseResolution P Q η) * (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
      unfold mrtResolution
      ring
    rw [he] at hw
    unfold MellinPrimeBands.extractionCost
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change 0 ≤ _ at hm0
    change _ ≤ 1 at hm1
    change _ ≤ _ at hm
    dsimp only [D] at *
    have hec : (4/P + 2/(mrtBaseResolution P Q η)) * (((j+1 : ℕ) : ℝ)^2)⁻¹ =
        2 * ((2/P) * (((j+1 : ℕ) : ℝ)^2)⁻¹) +
          (2/(mrtBaseResolution P Q η)) * (((j+1 : ℕ) : ℝ)^2)⁻¹ := by ring
    rw [hec]
    nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm1)]
  calc
    _ ≤ ∑ j ∈ range J, (2816 * Real.exp 1 * (T/N+1)) *
        ((4/P + 2/(mrtBaseResolution P Q η)) * (((j+1 : ℕ) : ℝ)^2)⁻¹) :=
      sum_le_sum (fun j _ => hterm j)
    _ = (2816 * Real.exp 1 * (T/N+1)) * (4/P + 2/(mrtBaseResolution P Q η)) *
        ∑ j ∈ range J, (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ (2816 * Real.exp 1 * (T/N+1)) * (4/P + 2/(mrtBaseResolution P Q η)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_range_succ_inv_sq_le J) (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CanonicalMellinEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A summed bound for every nonexceptional frequency class -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations

theorem canonical_small_cost_sum_le {P Q η : ℝ} (J N : ℕ) (hJ : 0 < J) {T : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1/12) (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (hPQ : P ≤ Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < (N : ℝ)) (hT : 0 ≤ T) :
    (∑ j ∈ range J, if j = 0 then (canonicalMellinBands P Q η).initialCost N T
      else (canonicalMellinBands P Q η).laterCost j N T) ≤
      1024 * Real.exp 2 * (T*Q/N+1) * (mrtBaseResolution P Q η)⁻¹ +
        2*(T/N+1)/P := by
  let D := canonicalMellinBands P Q η
  let C : ℝ := (T/N+1)*P⁻¹
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  have hterm (j : ℕ) : (if j = 0 then D.initialCost N T else D.laterCost j N T) ≤
      (if j = 0 then D.initialCost N T else 0) + C * (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
    by_cases hj : j = 0
    · simp only [hj, ite_true, if_true]
      exact le_add_of_nonneg_right (mul_nonneg hC (by positivity))
    · simp only [hj, ite_false, if_false, zero_add]
      have hh := canonical_laterCost_le (j-1) N hη (by linarith) hP0 hP hQ
        (Real.log_le_log hP0 hPQ) hbudget hH hT
      have hn : j-1+1 = j := by omega
      have he : ((j-1 : ℕ) : ℝ)+2 = (j+1 : ℕ) := by
        have hh : j-1+2 = j+1 := by omega
        exact_mod_cast hh
      simpa only [hn, he, C, D] using hh
  have hP1 : 1 ≤ P := by
    have hh := Real.exp_le_exp.mpr hP
    rw [Real.exp_log hP0] at hh
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hmain := canonical_initialCost_le N hη.le hη' hP1 (hP0.trans_le hPQ)
    hQ hH hN hT
  calc
    _ ≤ ∑ j ∈ range J, ((if j = 0 then D.initialCost N T else 0) +
        C * (((j+1 : ℕ) : ℝ)^2)⁻¹) := sum_le_sum (fun j _ => hterm j)
    _ = D.initialCost N T + C * ∑ j ∈ range J, (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
      rw [sum_add_distrib, ← mul_sum]
      simp only [sum_ite_eq', mem_range, hJ, ite_true, if_true]
    _ ≤ D.initialCost N T + C * 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_range_succ_inv_sq_le J) hC)
    _ ≤ _ := by
      change D.initialCost N T ≤ _ at hmain
      dsimp only [C]
      linarith [show (T/N+1)*P⁻¹*2 = 2*(T/N+1)/P by ring]

/-- This is the actual Dirichlet energy estimate away from the residual
class: all selected-band costs have been summed, independently of their
number. The no-small-band integral is retained verbatim. -/
theorem canonical_mellin_energy_bound {P Q η : ℝ} {J N : ℕ} (hJ : 0 < J)
    (hPbig : 2*Real.exp 1 ≤ P) (hP : 2 ≤ Real.log P) (hPQ : P ≤ Q)
    (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < N)
    (hupper : ∀ j ∈ range J, 2*mrtBandUpper Q (j+1) ≤ N)
    (f : ℕ → ℂ) (hf : Multiplicative f) (hb : OneBounded f)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient (range J) (canonicalMellinBands P Q η).primes f) t‖^2) ≤
    (∫ t in S ∩ mrtNoSmallBand (canonicalMellinBands P Q η).bins
        ((canonicalMellinBands P Q η).polynomial f) (canonicalMellinBands P Q η).threshold J,
      ‖angularMellinPolynomial (Ioc N (2*N))
        (mrtTypicalCoefficient (range J) (canonicalMellinBands P Q η).primes f) t‖^2) +
    2816*Real.exp 1*(T/N+1)*(8/P+4/(mrtBaseResolution P Q η)) +
    1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ + 2*(T/N+1)/P := by
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hPbig
  have hQ : 1 ≤ Real.log Q :=
    (show 1 ≤ Real.log P by linarith).trans (Real.log_le_log hP0 hPQ)
  have hd := canonicalMellinBands_valid hPbig hPQ (by linarith) hH hupper
  have hh := (canonicalMellinBands P Q η).partition_energy_le hd hN f hf hb hT hSm hS
  rw [sum_add_distrib] at hh
  have he := canonical_extraction_sum_le (η := η) J N hP0 hP hQ hPQ hH hT.le
  have hc := canonical_small_cost_sum_le J N hJ hη hη' hP0 hP hQ hPQ hbudget hH
    (by exact_mod_cast hN) hT.le
  linarith

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

/-- The cutoff costs its ordinary density, uniformly on every frequency
subset of a fixed polynomial-length interval. -/
theorem angularMellin_restriction_energy (E : ℕ → Prop) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T)
    {S : Set ℝ} (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
      (fun n => if E n then f n else 0) t‖^2) ≤
      2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2)+
        16*Real.exp 1*(T/N+2)*(((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N := by
  classical
  have hs := mrt_restricted_energy_split
    (angularMellinPolynomial (Ioc N (2*N)) (fun n => if E n then f n else 0))
    (angularMellinPolynomial (Ioc N (2*N)) f)
    (angularMellinPolynomial_continuous _ _) (angularMellinPolynomial_continuous _ _) hT.le hS
  simp_rw [← angularMellinPolynomial_sub] at hs
  have he := angularMellin_restriction_error_energy E f hf hN hT
  calc
    _ ≤ _ := hs
    _ ≤ 2*(8*Real.exp 1*(T/N+2)*
        (((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N)+
        2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) := by
      gcongr
    _ = _ := by ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CanonicalFullEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoring the full coefficient in the canonical frequency partition -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

theorem canonical_full_energy_jd_oai {P Q η : ℝ} {J N : ℕ} (hJ : 0 < J)
    (hPbig : 2*Real.exp 1 ≤ P) (hP : 2 ≤ Real.log P) (hPQ : P ≤ Q)
    (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < N)
    (hupper : ∀ j ∈ range J, 2*mrtBandUpper Q (j+1) ≤ N)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hb : ∀ n, ‖F n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
      4*(∫ t in S ∩ mrtNoSmallBand (canonicalMellinBands P Q η).bins
        ((canonicalMellinBands P Q η).polynomial F) (canonicalMellinBands P Q η).threshold J,
        ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2)+
      2*(2816*Real.exp 1*(T/N+1)*(8/P+4/(mrtBaseResolution P Q η))+
        1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹+2*(T/N+1)/P)+
      48*Real.exp 1*(T/N+2)*
        (((Ioc N (2*N)).filter fun n =>
          ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n).card:ℝ)/N := by
  classical
  let E := mrtTypical (range J) (canonicalMellinBands P Q η).primes
  let R := S ∩ mrtNoSmallBand (canonicalMellinBands P Q η).bins
    ((canonicalMellinBands P Q η).polynomial F) (canonicalMellinBands P Q η).threshold J
  have hr := angularMellin_energy_of_restriction E F hb hN hT hS
  have hm := angularMellin_restriction_energy E F hb hN hT
    (Set.inter_subset_left.trans hS : R ⊆ Set.Ioc (-T) T)
  have hc := canonical_mellin_energy_bound hJ hPbig hP hPQ hη hη' hbudget hH hN hupper
    F hF (fun n _ => hb n) hT hSm hS
  change (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
    2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient (range J) (canonicalMellinBands P Q η).primes F) t‖^2)+_ at hr
  change (∫ t in R, ‖angularMellinPolynomial (Ioc N (2*N))
    (mrtTypicalCoefficient (range J) (canonicalMellinBands P Q η).primes F) t‖^2) ≤ _ at hm
  dsimp only [E,R] at hr hm
  linear_combination hr + 2*hm + 2*hc

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.canonical_full_energy_jd_oai := @OAI.JointDickman.canonical_full_energy_jd_oai
