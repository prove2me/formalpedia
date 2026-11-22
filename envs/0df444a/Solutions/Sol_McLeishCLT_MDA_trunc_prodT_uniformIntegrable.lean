-- Prove2me | solution 1 for McLeishCLT.MDA.trunc_prodT_uniformIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:10:23.941768+00:00
-- url     : https://prove2.me/submissions/f390c89a-b17a-4b2f-8549-73179b7039c5

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

set_option autoImplicit false

namespace McLeishCLT.MDA.TruncUIProof

open MeasureTheory Finset McLeishCLT.MDA
open scoped ENNReal NNReal

theorem psum_mono (x : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ i ∈ range a, x i ^ 2 ≤ ∑ i ∈ range b, x i ^ 2 :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h) fun _ _ _ => sq_nonneg _

theorem prod_le (K : ℕ) (x : ℕ → ℝ) (t : ℝ) (J : ℕ) (hJK : K = 0 ∨ J < K)
    (hle : ∀ j ≤ J, ∑ i ∈ range j, x i ^ 2 ≤ 2)
    (hgt : ∀ j, J < j → j < K → 2 < ∑ i ∈ range j, x i ^ 2) :
    ∏ j ∈ range K, (1 + t ^ 2 * (x j * (if ∑ i ∈ range j, x i ^ 2 ≤ 2 then 1 else 0)) ^ 2)
      ≤ Real.exp (2 * t ^ 2) * (1 + t ^ 2 * x J ^ 2) := by
  have hexp1 : 1 ≤ Real.exp (2 * t ^ 2) := Real.one_le_exp (by positivity)
  have hfac1 : 1 ≤ 1 + t ^ 2 * x J ^ 2 := by nlinarith [sq_nonneg t, sq_nonneg (x J)]
  rcases hJK with hK | hJK
  · subst hK
    simp only [range_zero, prod_empty]
    nlinarith
  rw [← prod_range_mul_prod_Ico _ (Nat.succ_le_of_lt hJK)]
  have htail : ∏ j ∈ Ico (J + 1) K,
      (1 + t ^ 2 * (x j * (if ∑ i ∈ range j, x i ^ 2 ≤ 2 then 1 else 0)) ^ 2) = 1 := by
    refine prod_eq_one fun j hj => ?_
    rw [mem_Ico] at hj
    have h2 := hgt j (by omega) hj.2
    rw [if_neg (not_le.mpr h2)]
    ring
  have hhead : ∀ j ∈ range (J + 1),
      (1 + t ^ 2 * (x j * (if ∑ i ∈ range j, x i ^ 2 ≤ 2 then 1 else 0)) ^ 2)
        = 1 + t ^ 2 * x j ^ 2 := by
    intro j hj
    rw [mem_range] at hj
    rw [if_pos (hle j (by omega))]
    ring
  rw [htail, mul_one, prod_congr rfl hhead, prod_range_succ]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc ∏ j ∈ range J, (1 + t ^ 2 * x j ^ 2)
      ≤ ∏ j ∈ range J, Real.exp (t ^ 2 * x j ^ 2) :=
        prod_le_prod (fun j _ => by positivity) fun j _ => by
          have := Real.add_one_le_exp (t ^ 2 * x j ^ 2)
          linarith
    _ = Real.exp (t ^ 2 * ∑ j ∈ range J, x j ^ 2) := by
        rw [← Real.exp_sum, mul_sum]
    _ ≤ Real.exp (2 * t ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        have := hle J le_rfl
        nlinarith [sq_nonneg t]

theorem stopJ_spec {Ω : Type*} (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (k n = 0 ∨ stopJ k X n ω < k n) ∧
    (∀ j ≤ stopJ k X n ω, ∑ i ∈ range j, X n i ω ^ 2 ≤ 2) ∧
    (∀ j, stopJ k X n ω < j → j < k n → 2 < ∑ i ∈ range j, X n i ω ^ 2) := by
  classical
  unfold stopJ
  split_ifs with h
  · have hspec := Nat.find_spec h
    refine ⟨Or.inr hspec.1, fun j hj => ?_, fun j hj _ => ?_⟩
    · rcases j with _ | j
      · simp
      · have hmin := Nat.find_min h (show j < Nat.find h by omega)
        push Not at hmin
        exact hmin (by omega)
    · exact lt_of_lt_of_le hspec.2 (psum_mono (fun i => X n i ω) (by omega))
  · push Not at h
    refine ⟨by omega, fun j hj => ?_, fun j hj hjK => by omega⟩
    rcases j with _ | j
    · simp
    · exact h j (by omega)

/-- Pointwise: `|T_n(Z)|² ≤ e^{2t²}(1 + t² (max_j |X_{n,j}|)²)`. -/
theorem pt_bound {Ω : Type*} (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ‖prodT k (trunc X) t n ω‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * t ^ 2)) *
        (1 + ENNReal.ofReal (t ^ 2) * ‖maxAbs k X n ω‖ₑ ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := stopJ_spec k X n ω
  have hcore := prod_le (k n) (fun i => X n i ω) t (stopJ k X n ω) h1 h2 h3
  -- Replace `x_J²` by `(max_j |x_j|)²` (trivially when the row is empty).
  have hJmax : Real.exp (2 * t ^ 2) * (1 + t ^ 2 * X n (stopJ k X n ω) ω ^ 2)
      ≤ Real.exp (2 * t ^ 2) * (1 + t ^ 2 * maxAbs k X n ω ^ 2) ∨ k n = 0 := by
    rcases h1 with h1 | h1
    · exact Or.inr h1
    · left
      have hle : |X n (stopJ k X n ω) ω| ≤ maxAbs k X n ω :=
        le_ciSup (f := fun j : Fin (k n) => |X n j ω|) (Finite.bddAbove_range _)
          ⟨stopJ k X n ω, h1⟩
      have hsq : X n (stopJ k X n ω) ω ^ 2 ≤ maxAbs k X n ω ^ 2 := by
        rw [← sq_abs (X n (stopJ k X n ω) ω)]
        exact pow_le_pow_left₀ (abs_nonneg _) hle 2
      have := Real.exp_pos (2 * t ^ 2)
      refine mul_le_mul_of_nonneg_left ?_ this.le
      have := mul_le_mul_of_nonneg_left hsq (sq_nonneg t)
      linarith
  have hnorm : ‖prodT k (trunc X) t n ω‖ ^ 2 = ∏ j ∈ range (k n),
      (1 + t ^ 2 * (X n j ω * (if ∑ i ∈ range j, X n i ω ^ 2 ≤ 2 then 1 else 0)) ^ 2) := by
    unfold prodT
    rw [norm_prod, ← prod_pow]
    refine prod_congr rfl fun j _ => ?_
    rw [← Complex.normSq_eq_norm_sq]
    unfold trunc
    push_cast
    rw [Complex.normSq_apply]
    simp
    split_ifs <;> ring
  have hreal : ‖prodT k (trunc X) t n ω‖ ^ 2
      ≤ Real.exp (2 * t ^ 2) * (1 + t ^ 2 * maxAbs k X n ω ^ 2) := by
    rcases hJmax with hJ | hK
    · rw [hnorm]; exact hcore.trans hJ
    · rw [hnorm]
      have hK' : range (k n) = ∅ := by rw [hK]; rfl
      rw [hK', prod_empty]
      have he := Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * t ^ 2)
      have h1' : 1 ≤ 1 + t ^ 2 * maxAbs k X n ω ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (maxAbs k X n ω))]
      exact le_trans he (le_mul_of_one_le_right (by positivity) h1')
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs,
    ← ENNReal.ofReal_mul (sq_nonneg t), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (by positivity),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal hreal

end McLeishCLT.MDA.TruncUIProof

open MeasureTheory Finset McLeishCLT.MDA McLeishCLT.MDA.TruncUIProof
open scoped ENNReal NNReal

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ m0) (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hmda : IsMDA P ℱ k X)
    (ha : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, eLpNorm (maxAbs k X n) 2 P ≤ C) :
    ∀ t : ℝ, UniformIntegrable (fun n => prodT k (trunc X) t n) 1 P := by
  intro t
  obtain ⟨C₀, hC₀, hC⟩ := ha
  -- Uniform second-moment bound.
  set M : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * t ^ 2)) * (1 + ENNReal.ofReal (t ^ 2) * C₀ ^ 2)
    with hMdef
  have hMtop : M ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hC₀)⟩)
  have hL2 : ∀ n, ∫⁻ ω, ‖prodT k (trunc X) t n ω‖ₑ ^ 2 ∂P ≤ M := by
    intro n
    have hmax : ∫⁻ ω, ‖maxAbs k X n ω‖ₑ ^ 2 ∂P ≤ C₀ ^ 2 := by
      have h := hC n
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)] at h
      simp only [ENNReal.toReal_ofNat] at h
      have heq : ∫⁻ ω, ‖maxAbs k X n ω‖ₑ ^ 2 ∂P = eLpNorm' (maxAbs k X n) 2 P ^ (2 : ℝ) := by
        rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 2)]
        simp_rw [ENNReal.rpow_two]
      rw [heq, ENNReal.rpow_two]
      exact pow_le_pow_left₀ (by simp) h 2
    calc ∫⁻ ω, ‖prodT k (trunc X) t n ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * t ^ 2)) *
            (1 + ENNReal.ofReal (t ^ 2) * ‖maxAbs k X n ω‖ₑ ^ 2) ∂P :=
          lintegral_mono fun ω => pt_bound k X t n ω
      _ = ENNReal.ofReal (Real.exp (2 * t ^ 2)) *
            (1 + ENNReal.ofReal (t ^ 2) * ∫⁻ ω, ‖maxAbs k X n ω‖ₑ ^ 2 ∂P) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ M := by
          rw [hMdef]
          gcongr
  -- Measurability of `T_n(Z)`.
  have hXm : ∀ n j, j < k n → Measurable (X n j) := fun n j hj =>
    ((hmda n j hj).1.mono ((ℱ n).le (j + 1))).measurable
  have hTm : ∀ n, AEStronglyMeasurable (prodT k (trunc X) t n) P := by
    intro n
    refine Measurable.aestronglyMeasurable ?_
    unfold prodT
    refine Finset.measurable_prod _ fun j hj => ?_
    rw [mem_range] at hj
    have hs : Measurable fun ω => ∑ i ∈ range j, X n i ω ^ 2 :=
      Finset.measurable_sum _ fun i hi => (hXm n i (by rw [mem_range] at hi; omega)).pow_const 2
    have hZ : Measurable (trunc X n j) := by
      have : trunc X n j = fun ω => X n j ω * (if ∑ i ∈ range j, X n i ω ^ 2 ≤ 2 then 1 else 0) :=
        rfl
      rw [this]
      exact (hXm n j hj).mul (Measurable.ite (measurableSet_le hs measurable_const)
        measurable_const measurable_const)
    exact measurable_const.add (measurable_const.mul (Complex.measurable_ofReal.comp hZ))
  -- Tail bound: on `{c ≤ ‖T‖}`, `‖T‖ ≤ c⁻¹ ‖T‖²`.
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top hTm fun ε hε => ?_
  set c : ℝ≥0 := ⟨M.toReal / ε + 1, by positivity⟩ with hcdef
  have hc0 : (c : ℝ) = M.toReal / ε + 1 := rfl
  have hcpos : 0 < (c : ℝ) := by rw [hc0]; positivity
  have hcne : (c : ℝ≥0∞) ≠ 0 := by
    simpa using (NNReal.coe_pos.mp hcpos).ne'
  refine ⟨c, fun n => ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hpt : ∀ ω, ‖({ x | c ≤ ‖prodT k (trunc X) t n x‖₊ }.indicator
      (prodT k (trunc X) t n) ω)‖ₑ ≤ (c : ℝ≥0∞)⁻¹ * ‖prodT k (trunc X) t n ω‖ₑ ^ 2 := by
    intro ω
    by_cases hω : c ≤ ‖prodT k (trunc X) t n ω‖₊
    · rw [Set.indicator_of_mem (by exact hω)]
      have hge : (c : ℝ≥0∞) ≤ ‖prodT k (trunc X) t n ω‖ₑ := by
        rw [enorm_eq_nnnorm]
        exact_mod_cast hω
      calc ‖prodT k (trunc X) t n ω‖ₑ
          = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ‖prodT k (trunc X) t n ω‖ₑ) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hcne ENNReal.coe_ne_top, one_mul]
        _ ≤ (c : ℝ≥0∞)⁻¹ * ‖prodT k (trunc X) t n ω‖ₑ ^ 2 := by
            rw [sq]
            exact mul_le_mul' le_rfl (mul_le_mul' hge le_rfl)
    · rw [Set.indicator_of_notMem (by exact hω)]
      simp
  calc ∫⁻ ω, ‖({ x | c ≤ ‖prodT k (trunc X) t n x‖₊ }.indicator
        (prodT k (trunc X) t n) ω)‖ₑ ∂P
      ≤ ∫⁻ ω, (c : ℝ≥0∞)⁻¹ * ‖prodT k (trunc X) t n ω‖ₑ ^ 2 ∂P := lintegral_mono hpt
    _ = (c : ℝ≥0∞)⁻¹ * ∫⁻ ω, ‖prodT k (trunc X) t n ω‖ₑ ^ 2 ∂P :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hcne)
    _ ≤ (c : ℝ≥0∞)⁻¹ * M := mul_le_mul' le_rfl (hL2 n)
    _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_toReal hMtop, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_inv_of_pos hcpos, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hc0]
        have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
        rw [inv_mul_le_iff₀ (by positivity)]
        rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul]
        linarith
