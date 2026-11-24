-- Prove2me | solution 1 for HermitekLEAN.phi_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:51.234842+00:00
-- url     : https://prove2.me/submissions/4059f70e-bb54-4e43-9391-dbcf810a061e

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.qkn_real
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private lemma integral_norm_pow_exp_gaussian (a : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ (2 * a) * Real.exp (-‖z‖ ^ 2) = π * (Nat.factorial a : ℝ) := by
  have h_rpow : ∀ z : ℂ, (‖z‖ : ℝ) ^ (2 * a) = ‖z‖ ^ ((2 * a : ℕ) : ℝ) := by
    intro z; exact (rpow_natCast ‖z‖ (2 * a)).symm
  have h_exp : ∀ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.exp (-‖z‖ ^ (2 : ℝ)) := by intro z; norm_num
  simp_rw [h_rpow, h_exp]
  rw [Complex.integral_rpow_mul_exp_neg_rpow (show (1 : ℝ) ≤ 2 from by linarith only [])
    (show (-2 : ℝ) < ((2 * a : ℕ) : ℝ) from by
      have : (0 : ℝ) ≤ ((2 * a : ℕ) : ℝ) := Nat.cast_nonneg _; linarith only [])]
  rw [show ((2 * a : ℕ) : ℝ) + 2 = 2 * ((a : ℝ) + 1) from by push_cast; ring,
    show 2 * ((a : ℝ) + 1) / 2 = (a : ℝ) + 1 from by ring,
    show 2 * π / 2 = π from by ring,
    Real.Gamma_nat_eq_factorial]
private lemma circle_pow_factor (ω : _root_.Circle) {j k p : ℕ} (hjk : j ≤ k) (hjp : j ≤ p) :
    (ω : ℂ) ^ (p - j) * star (ω : ℂ) ^ (k - j) =
      (ω : ℂ) ^ p * star (ω : ℂ) ^ k := by
  have hωconj : (ω : ℂ) * star (ω : ℂ) = 1 := by
    rw [star_def]
    rw [show (starRingEnd ℂ) (ω : ℂ) = ↑(ω⁻¹ : _root_.Circle) from
      (_root_.Circle.coe_inv_eq_conj ω).symm]
    rw [← _root_.Circle.coe_mul, mul_inv_cancel, _root_.Circle.coe_one]
  have key : ((ω : ℂ) * star (ω : ℂ)) ^ j = 1 := by rw [hωconj]; simp
  rw [mul_pow] at key
  conv_rhs => rw [← Nat.sub_add_cancel hjp, ← Nat.sub_add_cancel hjk, pow_add, pow_add]
  rw [show (ω : ℂ) ^ (p - j) * (ω : ℂ) ^ j * (star (ω : ℂ) ^ (k - j) * star (ω : ℂ) ^ j) =
    (ω : ℂ) ^ (p - j) * star (ω : ℂ) ^ (k - j) * ((ω : ℂ) ^ j * star (ω : ℂ) ^ j) from by ring]
  rw [key, mul_one]
private lemma Phi_rotation_equivariant (ω : _root_.Circle) (z : ℂ) (k p : ℕ) :
    Phi k p ((ω : ℂ) * z) = (ω : ℂ) ^ p * star (ω : ℂ) ^ k * Phi k p z := by
  simp only [Phi, mul_pow, star_mul]
  -- Both sides have the same structure. We convert to a termwise equality.
  -- Reduce to termwise equality: for each j, the j-th LHS summand = j-th RHS summand
  -- after pulling ω^p * star(ω)^k through the normalization constant and sum.
  -- Strategy: multiply both sides by √(k!p!) to cancel the denominator, then compare termwise.
  -- Actually, just show the two sides are equal directly:
  suffices h : ∀ j ∈ Finset.range (min k p + 1),
      (-1 : ℂ) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
        ((ω : ℂ) ^ (p - j) * z ^ (p - j)) * (star z ^ (k - j) * star (ω : ℂ) ^ (k - j)) =
      (ω : ℂ) ^ p * star (ω : ℂ) ^ k *
        ((-1) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
          z ^ (p - j) * star z ^ (k - j)) by
    have hsum := Finset.sum_congr rfl h
    rw [← Finset.mul_sum] at hsum
    -- hsum: ∑ LHS_terms = ω^p * star(ω)^k * ∑ RHS_terms
    -- Goal: C * ∑ LHS = ω^p * star(ω)^k * (C * ∑ RHS)
    linear_combination (1 / ↑(Real.sqrt (↑k.factorial * ↑p.factorial))) * hsum
  intro j hj
  have hjk : j ≤ k := by simp [Finset.mem_range] at hj; omega
  have hjp : j ≤ p := by simp [Finset.mem_range] at hj; omega
  have key := circle_pow_factor ω hjk hjp
  -- Replace ω^{p-j} * star(ω)^{k-j} by ω^p * star(ω)^k, then ring
  calc (-1 : ℂ) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
        ((ω : ℂ) ^ (p - j) * z ^ (p - j)) * (star z ^ (k - j) * star (ω : ℂ) ^ (k - j))
      = ((ω : ℂ) ^ (p - j) * star (ω : ℂ) ^ (k - j)) *
        ((-1) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
          z ^ (p - j) * star z ^ (k - j)) := by ring
    _ = ((ω : ℂ) ^ p * star (ω : ℂ) ^ k) *
        ((-1) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
          z ^ (p - j) * star z ^ (k - j)) := by rw [key]
private lemma alternating_vandermonde_coeff_poly (k s N : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
      ((((Polynomial.C (1 : ℤ)) + Polynomial.X) ^ s * Polynomial.X ^ k).coeff N) := by
  let A : Polynomial ℤ := (Polynomial.C (1 : ℤ)) + Polynomial.X
  have hinner :
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k - j))) =
        Polynomial.X ^ k := by
    let f : ℕ → Polynomial ℤ := fun j =>
      A ^ j * (-1 : Polynomial ℤ) ^ (k - j) * Polynomial.C (k.choose j : ℤ)
    calc
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k - j))) =
          ∑ j ∈ Finset.range (k + 1), f ((k + 1) - 1 - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjk : j ≤ k := by simpa [Finset.mem_range] using hj
            have hsub : k - (k - j) = j := by omega
            simp [f, A, hsub, Nat.choose_symm hjk, mul_assoc, mul_comm]
      _ = ∑ j ∈ Finset.range (k + 1), f j := Finset.sum_range_reflect f (k + 1)
      _ = (A + (-1 : Polynomial ℤ)) ^ k := by
            symm
            simpa [f, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
              (add_pow A (-1 : Polynomial ℤ) k)
      _ = Polynomial.X ^ k := by simp [A, add_left_comm, add_comm]
  have hpoly :
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k + s - j))) =
        A ^ s * Polynomial.X ^ k := by
    calc
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k + s - j))) =
          ∑ j ∈ Finset.range (k + 1),
            A ^ s * ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k - j))) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : j ≤ k := by simpa [Finset.mem_range] using hj
              have hsub : k + s - j = s + (k - j) := by omega
              calc
                ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k + s - j))) =
                    ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (s + (k - j)))) := by simp [hsub]
                _ = ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ s * A ^ (k - j))) := by
                      simp [pow_add]
                _ = A ^ s * ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k - j))) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
      _ = A ^ s * ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k - j))) := by
            rw [Finset.mul_sum]
      _ = A ^ s * Polynomial.X ^ k := by rw [hinner]
  have hpolycoeff :
      ∑ j ∈ Finset.range (k + 1),
          (((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k + s - j))).coeff N) =
        (A ^ s * Polynomial.X ^ k).coeff N := by
    simpa only [Polynomial.finsetSum_coeff] using
      congrArg (fun p : Polynomial ℤ => p.coeff N) hpoly
  have hsum :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
      (A ^ s * Polynomial.X ^ k).coeff N := by
    refine Eq.trans ?_ hpolycoeff
    apply Finset.sum_congr rfl
    intro j hj
    rw [zsmul_eq_mul]
    simp only [A, Polynomial.C_1, Polynomial.coeff_intCast_mul, Int.cast_id,
      Polynomial.coeff_one_add_X_pow]
  exact hsum
private lemma alternating_vandermonde_coeff (k s N : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
      if k ≤ N then ↑(s.choose (N - k)) else 0 := by
  rw [alternating_vandermonde_coeff_poly, Polynomial.coeff_mul_X_pow']
  simp only [Polynomial.C_1, Polynomial.coeff_one_add_X_pow]
private theorem alternating_vandermonde_zero (k s : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑((k + s - j).choose k) = 1 := by
  simpa only [Int.reduceNeg, Std.le_refl, ↓reduceIte, tsub_self, Nat.choose_zero_right,
    Nat.cast_one, if_pos (Nat.le_refl k)] using alternating_vandermonde_coeff k s k
private theorem alternating_vandermonde_vanish (k s r : ℕ) (hr : r < k) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑((k + s - j).choose r) = 0 := by
  simpa only [Int.reduceNeg, if_neg (Nat.not_le_of_lt hr)] using
    alternating_vandermonde_coeff k s r
private lemma desc_fact_mul_fact (k m i j : ℕ) (hi : i ≤ k) (hj : j ≤ m) :
    Nat.descFactorial m j * Nat.factorial (m + k - i - j) =
    Nat.factorial m * Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i) := by
  have hki : k - i ≤ m + k - i - j := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hki
  have hsubt : m + k - i - j - (k - i) = m - j := by omega
  rw [hsubt] at h1
  have h2 := Nat.factorial_mul_descFactorial hj
  calc Nat.descFactorial m j * Nat.factorial (m + k - i - j)
      = Nat.descFactorial m j * (Nat.choose (m + k - i - j) (k - i) *
          Nat.factorial (k - i) * Nat.factorial (m - j)) := by rw [h1]
    _ = (Nat.factorial (m - j) * Nat.descFactorial m j) *
          (Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i)) := by ring
    _ = Nat.factorial m *
          (Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i)) := by rw [h2]
    _ = Nat.factorial m * Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i) := by ring
private lemma inner_sum_factor (k m i : ℕ) (hi : i ≤ k) (him : i ≤ m) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j)) =
    ↑(Nat.factorial m) * ↑(Nat.factorial (k - i)) *
      ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
        ↑(Nat.choose (m + k - i - j) (k - i)) := by
  -- Split into j ≤ m and j > m
  -- For j > m: descFact(m,j) = 0 so LHS term = 0.
  --            Also C(m+k-i-j, k-i) = 0 when i < k
  --            (since m+k-i-j < k-i).
  --            When i = k, k-i = 0, C(anything, 0) = 1,
  --            but j > m and j ≤ k = i ≤ m, contradiction!
  -- So actually j > m can't happen when i ≤ m and j ≤ k
  -- (since j ≤ k ≤ ... wait, j can be > m if k > m).
  -- But i ≤ m, so this is fine. When j > m: descFact = 0 makes LHS terms 0.
  -- For RHS: when j > m and i < k: C(m+k-i-j, k-i) = 0, so RHS term = 0. ✓
  -- When j > m and i = k: j > m ≥ i = k, but j ∈ range(k+1) means j ≤ k,
  -- contradicting j > m ≥ k. So impossible.
  -- So for j > m with j ≤ k: need i < k. Since i ≤ m < j ≤ k, we get
  -- i ≤ m < k, so i < k. ✓
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simp [Finset.mem_range] at hj; omega
  by_cases hjm : j ≤ m
  · have h := desc_fact_mul_fact k m i j hi hjm
    have hcast : (↑(Nat.descFactorial m j) : ℤ) * ↑(Nat.factorial (m + k - i - j)) =
        ↑(Nat.factorial m) * ↑(Nat.choose (m + k - i - j) (k - i)) *
        ↑(Nat.factorial (k - i)) := by exact_mod_cast h
    calc (-1 : ℤ) ^ j * ↑(k.choose j) * ↑(Nat.descFactorial m j) *
          ↑(Nat.factorial (m + k - i - j))
        = (-1 : ℤ) ^ j * ↑(k.choose j) *
          (↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j))) := by ring
      _ = (-1 : ℤ) ^ j * ↑(k.choose j) *
          (↑(Nat.factorial m) * ↑(Nat.choose (m + k - i - j) (k - i)) *
          ↑(Nat.factorial (k - i))) := by rw [hcast]
      _ = ↑(Nat.factorial m) * ↑(Nat.factorial (k - i)) *
          ((-1 : ℤ) ^ j * ↑(k.choose j) *
          ↑(Nat.choose (m + k - i - j) (k - i))) := by ring
  · push Not at hjm
    -- j > m and j ≤ k, so i ≤ m < j ≤ k, hence i < k
    have hik : i < k := by omega
    have hdesc : Nat.descFactorial m j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hjm
    have hchoose : Nat.choose (m + k - i - j) (k - i) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hdesc, hchoose]
private lemma inner_sum_at_zero (k m : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - j)) =
    ↑(Nat.factorial m) * ↑(Nat.factorial k) := by
  have hrw : ∀ j, Nat.factorial (m + k - j) = Nat.factorial (m + k - 0 - j) := by intro j; simp
  simp_rw [hrw]
  rw [inner_sum_factor k m 0 (Nat.zero_le k) (Nat.zero_le m)]
  simp only [Nat.sub_zero]
  have hrw2 : ∀ j, Nat.choose (m + k - j) k = Nat.choose (k + m - j) k := by intro j; congr 1; omega
  simp_rw [hrw2]
  rw [alternating_vandermonde_zero k m]; ring
private lemma inner_sum_vanish_pos (k m i : ℕ)
    (hi_pos : 1 ≤ i) (hi : i ≤ k) (him : i ≤ m) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j)) = 0 := by
  rw [inner_sum_factor k m i hi him]
  have hrw : ∀ j, Nat.choose (m + k - i - j) (k - i) =
      Nat.choose (k + (m - i) - j) (k - i) := by intro j; congr 1; omega
  simp_rw [hrw]
  rw [alternating_vandermonde_vanish k (m - i) (k - i) (by omega)]
  ac_rfl
private theorem double_sum_vandermonde (k m : ℕ) :
    ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
      ↑(Nat.descFactorial m i) * ↑(Nat.descFactorial m j) *
      ↑(Nat.factorial (m + k - i - j)) =
    ↑(Nat.factorial k) * ↑(Nat.factorial m) := by
  have hfactor : ∀ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℤ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
        ↑(Nat.descFactorial m i) * ↑(Nat.descFactorial m j) *
        ↑(Nat.factorial (m + k - i - j)) =
      (-1 : ℤ) ^ i * ↑(k.choose i) * ↑(Nat.descFactorial m i) *
        (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
          ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j))) := by
    intro i _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; rw [pow_add]; ring
  rw [Finset.sum_congr rfl hfactor, Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one,
      Nat.descFactorial_zero, Nat.sub_zero, mul_one]
    rw [inner_sum_at_zero k m]; ring
  · intro i hi hi_ne
    have hik : i ≤ k := by simp [Finset.mem_range] at hi; omega
    by_cases him : i ≤ m
    · rw [inner_sum_vanish_pos k m i (by omega) hik him]; ring
    · simp_all only [mem_range, Order.lt_add_one_iff, Int.reduceNeg, ne_eq, not_le, mul_eq_zero,
        not_false_eq_true, pow_eq_zero_iff, neg_eq_zero, one_ne_zero, Int.natCast_eq_zero, false_or,
        Nat.descFactorial_eq_zero_iff_lt, or_true, true_or]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (Nat.zero_lt_succ k))
private lemma integrable_norm_pow_exp (a : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ (2 * a) * Real.exp (-‖z‖ ^ 2)) := by
  by_contra h
  have hint := integral_norm_pow_exp_gaussian a
  rw [MeasureTheory.integral_undef h] at hint
  linarith only [hint, show (0 : ℝ) < π * (Nat.factorial a : ℝ) from by positivity]
private theorem norm_sq_phi_integral._proof_1_10 (k m i : ℕ)
    (hi : i < k + 1)
    (hi' : @LE.le ℕ (@Preorder.toLE ℕ
      (@PartialOrder.toPreorder ℕ (@LinearOrder.toPartialOrder ℕ Nat.instLinearOrder)))
      (min k m + 1) i) : ¬ m < i → False := by
  omega
private theorem norm_sq_phi_integral (k m : ℕ) :
    ∫ z : ℂ, ‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) = Real.pi := by
  -- Step 1: Express ‖Phi‖² * exp as a double sum * exp pointwise
  -- ‖Phi k m z‖² = (1/(k!*m!)) * Σ_{i,j} (-1)^{i+j} C(k,i) C(k,j)
  --   * descFact(m,i) descFact(m,j) ‖z‖^{2(m+k-i-j)}
  have hnsq : ∀ z : ℂ, ‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      (1 / ((Nat.factorial k : ℝ) * (Nat.factorial m : ℝ))) *
      ∑ i ∈ Finset.range (min k m + 1), ∑ j ∈ Finset.range (min k m + 1),
        (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
        (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
        (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) := by
    intro z
    suffices h : ‖Phi k m z‖ ^ 2 =
        (1 / ((↑k.factorial : ℝ) * ↑m.factorial)) *
        ∑ i ∈ Finset.range (min k m + 1), ∑ j ∈ Finset.range (min k m + 1),
          (-1 : ℝ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
          ↑(m.descFactorial i) * ↑(m.descFactorial j) *
          ‖z‖ ^ (2 * (m + k - i - j)) by
      rw [h, mul_assoc, Finset.sum_mul]
      congr 1; apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    simp only [Phi]
    rw [norm_mul, mul_pow]
    have hpre : ‖(1 : ℂ) / ↑√(↑k.factorial * ↑m.factorial)‖ ^ 2 =
        1 / ((↑k.factorial : ℝ) * ↑m.factorial) := by
      rw [norm_div, norm_one, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
        one_div, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _), one_div]
    rw [hpre]; congr 1
    set S := Finset.range (min k m + 1)
    set g : ℕ → ℂ := fun j =>
        (-1 : ℂ) ^ j * ↑(k.choose j) * (↑m.factorial / ↑(m - j).factorial) *
        z ^ (m - j) * star z ^ (k - j)
    change ‖∑ j ∈ S, g j‖ ^ 2 = _
    have hnorm_re : ‖∑ j ∈ S, g j‖ ^ 2 =
        ((∑ i ∈ S, g i) * (starRingEnd ℂ) (∑ j ∈ S, g j)).re := by
      rw [mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hnorm_re, map_sum, Finset.sum_mul_sum]
    simp_rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    have him : i ≤ m := by rw [Finset.mem_range] at hi; omega
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hjm : j ≤ m := by rw [Finset.mem_range] at hj; omega
    have hjk : j ≤ k := by rw [Finset.mem_range] at hj; omega
    -- Cross-term: (g i * conj(g j)).re = coeff * ‖z‖^{2(m+k-i-j)}
    -- Step 1: Expand conj(g j) - coefficients are real, conj swaps z and star z
    have hconj_g : (starRingEnd ℂ) (g j) =
        (-1 : ℂ) ^ j * ↑(k.choose j) * (↑m.factorial / ↑(m - j).factorial) *
        star z ^ (m - j) * z ^ (k - j) := by
      simp only [g, map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀]
      congr 1; congr 1; exact star_star z
    rw [hconj_g]; simp only [g]
    -- Step 2: Rearrange z-power product
    have hzpow : z ^ (m - i) * star z ^ (k - i) * (star z ^ (m - j) * z ^ (k - j)) =
        ↑(‖z‖ ^ (2 * (m + k - i - j)) : ℝ) := by
      have h1 : z ^ (m - i) * z ^ (k - j) = z ^ (m + k - i - j) := by rw [← pow_add]; congr 1; omega
      have h2 : star z ^ (k - i) * star z ^ (m - j) = star z ^ (m + k - i - j) := by
        rw [← pow_add]; congr 1; omega
      calc z ^ (m - i) * star z ^ (k - i) * (star z ^ (m - j) * z ^ (k - j))
        = (z ^ (m - i) * z ^ (k - j)) * (star z ^ (k - i) * star z ^ (m - j)) := by ring
        _ = z ^ (m + k - i - j) * star z ^ (m + k - i - j) := by rw [h1, h2]
        _ = ↑(‖z‖ ^ (2 * (m + k - i - j)) : ℝ) := by
            rw [← mul_pow, show z * star z = ↑(‖z‖ ^ 2 : ℝ) from by
              rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj']
              push_cast; rfl]
            push_cast; rw [← pow_mul]
    -- Step 3: Rearrange the full product into coeff * ↑(‖z‖^{2a})
    have hprod : (-1 : ℂ) ^ i * ↑(k.choose i) * (↑m.factorial / ↑(m - i).factorial) *
        z ^ (m - i) * star z ^ (k - i) *
        ((-1) ^ j * ↑(k.choose j) * (↑m.factorial / ↑(m - j).factorial) *
        star z ^ (m - j) * z ^ (k - j)) =
        ((-1 : ℂ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
        (↑m.factorial / ↑(m - i).factorial) * (↑m.factorial / ↑(m - j).factorial)) *
        ↑(‖z‖ ^ (2 * (m + k - i - j)) : ℝ) := by rw [← hzpow, pow_add]; ring
    rw [hprod]
    -- Step 4: Replace m!/(m-j)! with descFactorial
    have hfact_desc_i : (↑m.factorial : ℂ) / ↑(m - i).factorial = ↑(m.descFactorial i : ℕ) := by
      have hdvd : (m - i).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (Nat.sub_le m i)
      rw [Nat.descFactorial_eq_div him,
        Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    have hfact_desc_j : (↑m.factorial : ℂ) / ↑(m - j).factorial = ↑(m.descFactorial j : ℕ) := by
      have hdvd : (m - j).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (Nat.sub_le m j)
      rw [Nat.descFactorial_eq_div hjm,
        Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    rw [hfact_desc_i, hfact_desc_j]
    -- Step 5: Everything is now ↑(real), so .re = the real value
    rw [show (-1 : ℂ) ^ (i + j) * ↑↑(k.choose i) * ↑↑(k.choose j) *
        ↑↑(m.descFactorial i) * ↑↑(m.descFactorial j) =
        ↑((-1 : ℝ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
        ↑(m.descFactorial i) * ↑(m.descFactorial j)) from by push_cast; ring]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hnsq]
  rw [integral_const_mul]
  -- Step 2: Swap sum and integral (finite sums, each term is integrable)
  have hint_each : ∀ (i j : ℕ),
      Integrable (fun z : ℂ =>
        (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
        (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
        (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2))) := by
    intro i j
    exact (integrable_norm_pow_exp (m + k - i - j)).const_mul _
  have hswap_outer : ∀ i ∈ Finset.range (min k m + 1),
      Integrable (fun z : ℂ =>
        ∑ j ∈ Finset.range (min k m + 1),
          (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
          (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
          (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2))) := by
    intro i _; exact integrable_finsetSum _ (fun j _ => hint_each i j)
  rw [integral_finsetSum _ hswap_outer]
  have hswap_inner : ∀ i, ∫ z : ℂ, ∑ j ∈ Finset.range (min k m + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) =
      ∑ j ∈ Finset.range (min k m + 1), ∫ z : ℂ,
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) := by
    intro i; exact integral_finsetSum _ (fun j _ => hint_each i j)
  simp_rw [hswap_inner]
  -- Step 3: Compute each monomial integral
  have hcompute : ∀ (i j : ℕ),
      ∫ z : ℂ, (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) =
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (π * (Nat.factorial (m + k - i - j) : ℝ)) := by
    intro i j
    rw [integral_const_mul, integral_norm_pow_exp_gaussian]
  simp_rw [hcompute]
  -- Step 4: Extend sum range from (min k m + 1) to (k + 1)
  -- Extra terms have descFactorial m j = 0 (when j > m and k > m) or choose k j = 0 (when j > k)
  -- Actually, we can fold everything into the double_sum_vandermonde directly.
  -- First, factor out π and get the double sum matching double_sum_vandermonde
  have hfold : ∀ (i j : ℕ),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (π * (Nat.factorial (m + k - i - j) : ℝ)) =
      π * ((-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ)) := by intro i j; ring
  simp_rw [hfold]
  -- Pull π out of sums: Σ (π * g(i,j)) = π * Σ g(i,j)
  simp_rw [← Finset.mul_sum]
  -- Now goal: (1/(k!*m!)) * (π * Σ_i (π * Σ_j (...))) = π
  -- After pulling π out of both sums: (1/(k!*m!)) * π * Σ_{i,j} (...) = π
  -- But actually after simp_rw [← Finset.mul_sum], the inner sum already pulled π out.
  -- Let me check what the goal looks like and adjust.
  -- Goal should be: (1/(k!*m!)) * π * (Σ_i Σ_j coeff) = π
  -- Extend sum from range(min k m + 1) to range(k + 1)
  -- Extra terms have descFactorial m i = 0 (when i > m and k > m)
  -- or choose k i = 0 (when i > k, which doesn't happen since range stops at min k m ≤ k)
  -- When k ≤ m: min k m = k, so range(min k m + 1) = range(k + 1), no extension needed
  -- When k > m: min k m = m, extra terms for m < i ≤ k have descFactorial m i = 0
  have hext_j : ∀ i, ∑ j ∈ Finset.range (min k m + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) =
      ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) := by
    intro i
    apply Finset.sum_subset (Finset.range_mono (by omega : min k m + 1 ≤ k + 1))
    intro j hj hj'
    have hmj : m < j := by
      by_contra hnot
      exact norm_sq_phi_integral._proof_1_10 k m j (Finset.mem_range.mp hj)
        (Nat.le_of_not_gt (fun h => hj' (Finset.mem_range.mpr h))) hnot
    simp only [Nat.descFactorial_eq_zero_iff_lt.mpr hmj, Nat.cast_zero, mul_zero, zero_mul]
  simp_rw [hext_j]
  have hext_i : ∑ i ∈ Finset.range (min k m + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega : min k m + 1 ≤ k + 1))
    intro i hi hi'
    rw [Finset.mem_range] at hi hi'
    push Not at hi'
    have him : m < i := by omega
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr him]
  rw [hext_i]
  -- Now apply double_sum_vandermonde (cast from ℤ to ℝ)
  have hvand := double_sum_vandermonde k m
  -- Cast hvand from ℤ to ℝ
  have hvand_real : ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) =
      (Nat.factorial k : ℝ) * (Nat.factorial m : ℝ) := by
    have := congr_arg (fun x : ℤ => (x : ℝ)) hvand
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast] at this
    convert this using 1
  rw [hvand_real]
  -- Now: (1/(k!*m!)) * π * (k! * m!) = π
  have hpos : (0 : ℝ) < (Nat.factorial k : ℝ) * (Nat.factorial m : ℝ) := by positivity
  field_simp
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
theorem _root_.solution :
    ∀ {k m n : ℕ},
      weightedInner (Phi k m) (Phi k n) = if m = n then 1 else 0 := by
  intro k m n
  by_cases hmn : m = n
  · -- Diagonal case: m = n
    subst hmn
    rw [if_pos rfl]
    unfold weightedInner HermiteLEAN.weightedInner
    have hint : ∫ (z : ℂ), Phi k m z * (starRingEnd ℂ) (Phi k m z) *
        ↑(rexp (-‖z‖ ^ 2)) = ↑Real.pi := by
      have hreal : ∀ z : ℂ, Phi k m z * (starRingEnd ℂ) (Phi k m z) *
          ↑(rexp (-‖z‖ ^ 2)) = ↑(‖Phi k m z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
        intro z; rw [mul_conj]; push_cast; rw [Complex.normSq_eq_norm_sq]
        ring_nf; simp [mul_comm]
      simp_rw [hreal, integral_complex_ofReal]
      congr 1
      exact norm_sq_phi_integral k m
    rw [hint]; field_simp [Real.pi_ne_zero]
  · -- Off-diagonal case: m ≠ n. Use rotation trick on ℂ-valued integrand.
    rw [if_neg hmn]
    -- The ℂ-valued integrand
    set f : ℂ → ℂ := fun z =>
      Phi k m z * star (Phi k n z) * (↑(Real.exp (-‖z‖ ^ 2)) : ℂ) with hf_def
    -- Pick ω on the unit circle with ω^{m-n} = -1
    set d : ℤ := (m : ℤ) - (n : ℤ)
    have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (by exact_mod_cast hmn)
    set ω : _root_.Circle := _root_.Circle.exp (Real.pi / (d : ℝ))
    set rot : ℂ ≃ₗᵢ[ℝ] ℂ := rotation ω
    -- f(ω z) = -f(z) because each monomial z^{p-j} conj(z)^{k-j} picks up
    -- ω^{p-j} conj(ω)^{k-j} = ω^{p-k} (independent of j, since |ω|=1),
    -- so Phi k p (ωz) = ω^{p-k} Phi k p z, and the inner product factor is ω^{m-n} = -1.
    -- ω^m * star(ω)^n = -1 (same proof as gaussian_monomial_moments_off_diag)
    have hωmn : (ω : ℂ) ^ m * star (ω : ℂ) ^ n = -1 := by
      rw [star_def, ← _root_.Circle.coe_inv_eq_conj,
        ← _root_.Circle.coe_pow, ← _root_.Circle.coe_pow, ← _root_.Circle.coe_mul]
      rw [show ω ^ m * ω⁻¹ ^ n = ω ^ d from by
        rw [show ω ^ m * ω⁻¹ ^ n = ω ^ m * (ω ^ n)⁻¹ from by rw [inv_pow],
          ← zpow_natCast ω m, ← zpow_natCast ω n, ← zpow_sub]]
      rw [show ω = _root_.Circle.exp (Real.pi / (d : ℝ)) from rfl,
        ← _root_.Circle.exp_intCast_mul (Real.pi / (d : ℝ)) d,
        show (d : ℝ) * (Real.pi / (d : ℝ)) = Real.pi from by field_simp]
      simp only [_root_.Circle.coe_exp, Complex.exp_pi_mul_I,
        ]
    -- |ω|^{2k} = 1
    have hωmod : (ω : ℂ) ^ k * star (ω : ℂ) ^ k = 1 := by
      rw [← mul_pow]
      rw [show (ω : ℂ) * star (ω : ℂ) = 1 from by
        rw [star_def, ← _root_.Circle.coe_inv_eq_conj, ← _root_.Circle.coe_mul,
          mul_inv_cancel, _root_.Circle.coe_one]]
      simp
    have hrot_f : ∀ z, f (rot z) = -f z := by
      intro z
      simp only [hf_def, rot, rotation_apply, norm_mul, _root_.Circle.norm_coe, one_mul]
      rw [Phi_rotation_equivariant ω z k m, Phi_rotation_equivariant ω z k n]
      simp only [star_mul, star_star, star_pow]
      -- After simplification: star(star ↑ω ^ k) becomes ↑ω ^ k (via star_pow + star_star)
      -- star(↑ω ^ n) becomes star(↑ω) ^ n (via star_pow)
      calc (ω : ℂ) ^ m * star (ω : ℂ) ^ k * Phi k m z *
            (star (Phi k n z) * ((ω : ℂ) ^ k * star (ω : ℂ) ^ n)) *
            ↑(rexp (-‖z‖ ^ 2))
          = ((ω : ℂ) ^ m * star (ω : ℂ) ^ n) * ((ω : ℂ) ^ k * star (ω : ℂ) ^ k) *
            (Phi k m z * star (Phi k n z) * ↑(rexp (-‖z‖ ^ 2))) := by ring
        _ = -1 * 1 * (Phi k m z * star (Phi k n z) * ↑(rexp (-‖z‖ ^ 2))) := by rw [hωmn, hωmod]
        _ = _ := by ring
    -- From ∫ f(rot z) = ∫ f(z) and f(rot z) = -f(z), get ∫ f = 0
    have hmp := rot.measurePreserving
    have hemb := rot.toHomeomorph.measurableEmbedding
    have hint_eq : ∫ z, f (rot z) = ∫ z, f z := hmp.integral_comp hemb f
    simp_rw [hrot_f, integral_neg] at hint_eq
    -- hint_eq : -(∫ f) = ∫ f, so ∫ f = 0
    have hfzero : ∫ z, f z = 0 := by
      set I := ∫ z, f z
      have h : -I = I := hint_eq
      have h2 : I + I = 0 := by nth_rw 1 [← neg_neg I, h]; exact neg_add_cancel I
      simp_all only [RCLike.star_def, ofReal_exp, ofReal_neg, ofReal_pow, ne_eq, Int.cast_eq_zero,
        norm_map, LinearIsometryEquiv.coe_toHomeomorph, add_self_eq_zero]
    -- Connect to weightedInner
    unfold weightedInner HermiteLEAN.weightedInner
    simp_all only [RCLike.star_def, ofReal_exp, ofReal_neg, ofReal_pow, ne_eq, Int.cast_eq_zero,
      norm_map, LinearIsometryEquiv.coe_toHomeomorph, one_div, mul_zero]
end HermitekLEAN
