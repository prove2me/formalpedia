-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:38:04.959632+00:00
-- url     : https://prove2.me/submissions/b34d11c7-e536-4f2f-8ece-96e6c8e55089

-- Adapted from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

open scoped BigOperators
noncomputable section
namespace OAI.PiExponent
theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

theorem mem_strictWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ strictWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) < H := by
  classical
  simp only [strictWeightedSimplex, Finset.mem_filter, mem_realWeightedSimplex hw,
    and_iff_right_iff_imp]
  exact fun h => h.le

namespace InterpolationMatrix
@[simp] theorem exponentVector_apply {m : ℕ} (a : Fin m → ℕ) (i : Fin m) :
    exponentVector a i = a i := by
  simp [exponentVector]

theorem column_mem_iff {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (a : Fin (m + 1) → ℕ) :
    a ∈ PiExponent.realWeightedSimplex (columnWeights w0 w) H ↔
      w0 * (a 0 : ℝ) + ∑ i, w i * (a i.succ : ℝ) ≤ H := by
  have hp : ∀ i, 0 < columnWeights w0 w i := by
    intro i
    refine Fin.cases hw0 (fun j => hw j) i
  rw [PiExponent.mem_realWeightedSimplex hp, Fin.sum_univ_succ]
  rfl

theorem row_mem_iff {m : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (b : Fin (m + 1) → ℕ) :
    b ∈ PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H ↔
      v0 * (b 0 : ℝ) + (∑ i, w i * (b i.succ : ℝ)) / θ < H := by
  have hp : ∀ i, 0 < rowWeights v0 θ w i := by
    intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
  rw [PiExponent.mem_strictWeightedSimplex hp, Fin.sum_univ_succ]
  simp only [rowWeights, Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div,
    Finset.sum_div]

theorem column_weight_le {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (c : Column w0 w H) :
    w0 * (c.1 0 : ℝ) + ∑ i, w i * (c.1 i.succ : ℝ) ≤ H :=
  (column_mem_iff hw0 hw c.1).mp c.2

theorem row_weight_lt {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (ρ : Row K v0 θ w H) :
    v0 * (ρ.2.1 0 : ℝ) + (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ < H :=
  (row_mem_iff hv0 hθ hw ρ.2.1).mp ρ.2.2

end InterpolationMatrix
namespace RowTranslation


open scoped BigOperators
open MvPolynomial

section PolynomialShift
variable {σ R : Type*} [CommSemiring R]

noncomputable def shift (c : σ → R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => X i + C (c i))

@[simp] theorem shift_C (c : σ → R) (r : R) : shift c (C r) = C r := by
  simp [shift]

@[simp] theorem shift_X (c : σ → R) (i : σ) : shift c (X i) = X i + C (c i) := by
  simp [shift]

theorem shift_add (c d : σ → R) (p : MvPolynomial σ R) :
    shift c (shift d p) = shift (fun i => c i + d i) p := by
  have h : (shift c).comp (shift d) = shift (fun i => c i + d i) := by
    ext r i <;> simp [add_assoc]
  exact DFunLike.congr_fun h p

@[simp] theorem shift_zero (p : MvPolynomial σ R) : shift (fun _ => 0) p = p := by
  have h : shift (fun _ : σ => (0 : R)) = RingHom.id _ := by
    ext r i <;> simp
  exact DFunLike.congr_fun h p

noncomputable def shiftCoefficient (c : σ → R) (β a : σ →₀ ℕ) : R :=
  (shift c (monomial a 1)).coeff β

theorem coeff_shift (c : σ → R) (p : MvPolynomial σ R) (β : σ →₀ ℕ) :
    (shift c p).coeff β =
      ∑ a ∈ p.support, p.coeff a * shiftCoefficient c β a := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [show monomial a (p.coeff a) = C (p.coeff a) * monomial a 1 by simp [C_mul_monomial]]
  simp [shiftCoefficient, coeff_C_mul]

theorem coeff_shift_over (c : σ → R) (p : MvPolynomial σ R) (β : σ →₀ ℕ)
    (S : Finset (σ →₀ ℕ)) (hp : p.support ⊆ S) :
    (shift c p).coeff β = ∑ a ∈ S, p.coeff a * shiftCoefficient c β a := by
  classical
  rw [coeff_shift]
  apply Finset.sum_subset hp
  intro a ha hnot
  simp [MvPolynomial.notMem_support_iff.mp hnot]

theorem shift_three (z ε τ : σ → R) (p : MvPolynomial σ R) :
    shift (fun i => z i + ε i + τ i) p = shift τ (shift ε (shift z p)) := by
  simp only [shift_add]
  apply congrArg (fun c => shift c p)
  funext i
  ac_rfl

end PolynomialShift

section FiniteExpansion
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

noncomputable def multiIndex (a : σ → ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm a

omit [DecidableEq σ] in
@[simp] theorem multiIndex_apply (a : σ → ℕ) (i : σ) : multiIndex a i = a i := by
  simp [multiIndex]

omit [Fintype σ] [DecidableEq σ] in
theorem shifted_X_pow (c : σ → R) (i : σ) (n : ℕ) :
    (X i + C (c i)) ^ n =
      ∑ b : Fin (n + 1), C ((n.choose b : R) * c i ^ (n - b)) * X i ^ (b : ℕ) := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem shifted_product_expansion (c : σ → R) (a : σ → ℕ) :
    (∏ i, (X i + C (c i)) ^ a i) =
      ∑ b : (∀ i, Fin (a i + 1)),
        C (∏ i, ((a i).choose (b i) : R) * c i ^ (a i - b i)) *
          monomial (multiIndex (fun i => (b i : ℕ))) 1 := by
  simp_rw [shifted_X_pow]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.prod_mul_distrib, ← map_prod, prod_X_pow]
  have hidx : Finsupp.indicator Finset.univ (fun i _ => (b i : ℕ)) =
      multiIndex (fun i => (b i : ℕ)) := by
    ext i
    simp [Finsupp.indicator]
  rw [hidx]

omit [DecidableEq σ] in
theorem shift_monomial_one (c : σ → R) (a : σ →₀ ℕ) :
    shift c (monomial a 1) = ∏ i, (X i + C (c i)) ^ a i := by
  simp only [shift, eval₂Hom_monomial, map_one, one_mul]
  exact a.prod_fintype _ (fun i => pow_zero _)

theorem shiftCoefficient_eq (c : σ → R) (β a : σ →₀ ℕ) :
    shiftCoefficient c β a = ∏ i, ((a i).choose (β i) : R) * c i ^ (a i - β i) := by
  classical
  rw [shiftCoefficient, shift_monomial_one, shifted_product_expansion, coeff_sum]
  simp only [coeff_C_mul, coeff_monomial]
  by_cases h : ∀ i, β i ≤ a i
  · let b₀ : ∀ i, Fin (a i + 1) := fun i => ⟨β i, Nat.lt_succ_of_le (h i)⟩
    have hidx : multiIndex (fun i => (b₀ i : ℕ)) = β := by ext i; simp [b₀]
    rw [Finset.sum_eq_single b₀]
    · simp [hidx, b₀]
    · intro b hb hne
      have hidx' : multiIndex (fun i => (b i : ℕ)) ≠ β := by
        intro he
        apply hne
        funext i
        apply Fin.ext
        have hi := congrArg (fun d : σ →₀ ℕ => d i) he
        simpa [b₀] using hi
      simp [hidx']
    · simp
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hright : (∏ j, ((a j).choose (β j) : R) * c j ^ (a j - β j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Nat.choose_eq_zero_of_lt hi]
    rw [hright]
    apply Finset.sum_eq_zero
    intro b hb
    have hidx : multiIndex (fun j => (b j : ℕ)) ≠ β := by
      intro he
      have hi' := congrArg (fun d : σ →₀ ℕ => d i) he
      have hbi : (b i : ℕ) = β i := by simpa using hi'
      have hlt := (b i).isLt
      omega
    simp [hidx]


end FiniteExpansion
end RowTranslation
namespace Arithmetic
theorem lcmConstant_pos : 0 < lcmConstant := by
  have h : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  dsimp [lcmConstant]
  linarith

theorem log_lcmUpto_le (n : ℕ) :
    Real.log (Nat.lcmUpto n : ℝ) ≤ lcmConstant * n := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  exact Chebyshev.psi_le_const_mul_self (by positivity)

theorem gaussian_norm_one_le (z : GaussianInt) (hz : z ≠ 0) :
    1 ≤ ‖(z : ℂ)‖ := by
  have hi : (1 : ℤ) ≤ z.norm := (GaussianInt.norm_pos.mpr hz)
  have hr : (1 : ℝ) ≤ (z.norm : ℝ) := by exact_mod_cast hi
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq] at hr
  have hn : 0 ≤ ‖(z : ℂ)‖ := norm_nonneg _
  nlinarith

theorem gaussian_det_norm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι GaussianInt) (hA : A.det ≠ 0) :
    1 ≤ ‖(A.map GaussianInt.toComplex).det‖ := by
  change 1 ≤ ‖(GaussianInt.toComplex.mapMatrix A).det‖
  rw [← RingHom.map_det]
  exact gaussian_norm_one_le A.det hA

theorem det_row_column_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℂ) :
    Matrix.det (fun i j => r i * (c j * A i j)) =
      (∏ i, r i) * (∏ j, c j) * A.det := by
  calc
    _ = (∏ i, r i) * (Matrix.of fun i j => c j * A i j).det :=
      Matrix.det_mul_column r (Matrix.of fun i j => c j * A i j)
    _ = _ := by rw [Matrix.det_mul_row c A]; ring

theorem cleared_det_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (B : Matrix ι ι GaussianInt)
    (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hB : B.map GaussianInt.toComplex = fun i j => (r i : ℂ) * ((c j : ℂ) * A i j)) :
    1 ≤ (∏ i, r i) * (∏ j, c j) * ‖A.det‖ := by
  have hd : (B.map GaussianInt.toComplex).det =
      (∏ i, (r i : ℂ)) * (∏ j, (c j : ℂ)) * A.det := by
    rw [hB, det_row_column_scale]
  have hn : B.det ≠ 0 := by
    intro he
    have hz : (B.map GaussianInt.toComplex).det = 0 := by
      change (GaussianInt.toComplex.mapMatrix B).det = 0
      rw [← RingHom.map_det, he, map_zero]
    rw [hd] at hz
    have hr' : (∏ i, (r i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact_mod_cast (hr i).ne')
    have hc' : (∏ j, (c j : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
      intro j hj
      exact_mod_cast (hc j).ne')
    exact mul_ne_zero (mul_ne_zero hr' hc') hA hz
  have h := gaussian_det_norm_one_le B hn
  rw [hd, norm_mul, norm_mul, norm_prod, norm_prod] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr _),
    abs_of_pos (hc _)] using h

theorem cleared_det_log_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (B : Matrix ι ι GaussianInt)
    (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hB : B.map GaussianInt.toComplex = fun i j => (r i : ℂ) * ((c j : ℂ) * A i j)) :
    -(∑ i, Real.log (r i)) - ∑ j, Real.log (c j) ≤ Real.log ‖A.det‖ := by
  have hrp : 0 < ∏ i, r i := Finset.prod_pos (by intro i hi; exact hr i)
  have hcp : 0 < ∏ i, c i := Finset.prod_pos (by intro i hi; exact hc i)
  have hn : 0 < ‖A.det‖ := norm_pos_iff.mpr hA
  have h := Real.log_nonneg (cleared_det_norm_bound A B r c hr hc hA hB)
  rw [Real.log_mul (mul_pos hrp hcp).ne' hn.ne', Real.log_mul hrp.ne' hcp.ne',
    Real.log_prod (by intro i hi; exact (hr i).ne'),
    Real.log_prod (by intro i hi; exact (hc i).ne')] at h
  linarith

theorem log_lcm_power_product_le {ι : Type*} (s : Finset ι) (T e : ι → ℕ) :
    Real.log (∏ i ∈ s, (Nat.lcmUpto (T i) : ℝ) ^ e i) ≤
      lcmConstant * ∑ i ∈ s, (e i : ℝ) * T i := by
  rw [Real.log_prod (by intro i hi; exact pow_ne_zero _ (by exact_mod_cast Nat.lcmUpto_ne_zero (T i)))]
  simp_rw [Real.log_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left (log_lcmUpto_le (T i)) (Nat.cast_nonneg (e i) : (0 : ℝ) ≤ e i)
  nlinarith only [h]

theorem log_lcm_floor_product_le {ι : Type*} (s : Finset ι)
    (T : ι → ℕ) (w : ι → ℝ) (H : ℝ) (hH : 0 ≤ H) (hw : ∀ i ∈ s, 0 < w i) :
    Real.log (∏ i ∈ s, (Nat.lcmUpto (T i) : ℝ) ^ ⌊H / w i⌋₊) ≤
      H * lcmConstant * ∑ i ∈ s, (T i : ℝ) / w i := by
  calc
    _ ≤ lcmConstant * ∑ i ∈ s, (⌊H / w i⌋₊ : ℝ) * T i :=
      log_lcm_power_product_le s T _
    _ ≤ lcmConstant * ∑ i ∈ s, (H / w i) * T i := by
      apply mul_le_mul_of_nonneg_left _ lcmConstant_pos.le
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (T i))
      exact Nat.floor_le (div_nonneg hH (hw i hi).le)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem sum_ceil_truncation_div_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (F v : ℝ) (hF : 0 ≤ F) (hv : 0 < v) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, (⌈F * w i / v⌉₊ : ℝ) / w i) ≤
      F * s.card / v + ∑ i ∈ s, 1 / w i := by
  calc
    _ ≤ ∑ i ∈ s, (F * w i / v + 1) / w i := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (hw i hi).le
      exact (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hF (hw i hi).le) hv.le)).le
    _ = ∑ i ∈ s, (F / v + 1 / w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [(hw i hi).ne', hv.ne']
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const]; simp; ring

theorem truncation_denominator_log_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (F v H : ℝ) (hF : 0 ≤ F) (hv : 0 < v) (hH : 0 < H)
    (hw : ∀ i ∈ s, 0 < w i) :
    Real.log (∏ i ∈ s,
      (Nat.lcmUpto (⌈F * w i / v⌉₊) : ℝ) ^ ⌊H / w i⌋₊) / H ≤
      lcmConstant * F * s.card / v + lcmConstant * ∑ i ∈ s, 1 / w i := by
  apply (div_le_iff₀ hH).mpr
  calc
    _ ≤ H * lcmConstant * ∑ i ∈ s, (⌈F * w i / v⌉₊ : ℝ) / w i :=
      log_lcm_floor_product_le s _ w H hH.le hw
    _ ≤ H * lcmConstant * (F * s.card / v + ∑ i ∈ s, 1 / w i) := by
      exact mul_le_mul_of_nonneg_left (sum_ceil_truncation_div_le s w F v hF hv hw)
        (mul_pos hH lcmConstant_pos).le
    _ = _ := by ring

theorem dvd_lcmUpto_of_pos_le {k T : ℕ} (hk : 0 < k) (hkT : k ≤ T) :
    k ∣ Nat.lcmUpto T := by
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hk, hkT⟩)

theorem lcm_mul_log_coeff_gaussian (T k : ℕ) (hk : k ≤ T) :
    (Nat.lcmUpto T : ℂ) * PowerSeries.coeff k (PowerSeries.log ℂ) ∈
      GaussianInt.toComplex.range := by
  by_cases hk0 : k = 0
  · simp [hk0]
  obtain ⟨m, hm⟩ := dvd_lcmUpto_of_pos_le (Nat.pos_of_ne_zero hk0) hk
  refine ⟨((-1 : GaussianInt) ^ (k + 1)) * (m : GaussianInt), ?_⟩
  rw [PowerSeries.coeff_log, if_neg hk0, hm]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀, Nat.cast_mul]
  field_simp

theorem cleared_log_trunc_mem (T : ℕ) :
    Polynomial.C (Nat.lcmUpto T : ℂ) * PowerSeries.trunc T (PowerSeries.log ℂ) ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  apply (Polynomial.mem_map_range GaussianInt.toComplex).mpr
  intro k
  rw [Polynomial.coeff_C_mul, PowerSeries.coeff_trunc]
  split_ifs with hk
  · exact lcm_mul_log_coeff_gaussian T k hk.le
  · simp

theorem exists_cleared_log_trunc (T : ℕ) :
    ∃ P : Polynomial GaussianInt,
      P.map GaussianInt.toComplex =
        Polynomial.C (Nat.lcmUpto T : ℂ) * PowerSeries.trunc T (PowerSeries.log ℂ) :=
  cleared_log_trunc_mem T

theorem gaussian_C_mem (z : GaussianInt) :
    Polynomial.C (z : ℂ) ∈ (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  exact ⟨Polynomial.C z, by simp⟩

theorem cleared_shifted_log_trunc_mem (T q : ℕ) (z : GaussianInt) :
    Polynomial.C (Nat.lcmUpto T : ℂ) *
      (Polynomial.C (z : ℂ) + Polynomial.C (q : ℂ) *
        PowerSeries.trunc T (PowerSeries.log ℂ)) ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have hL : Polynomial.C (Nat.lcmUpto T : ℂ) ∈ S := by
    simp
  have hq : Polynomial.C (q : ℂ) ∈ S := by
    simp
  have hlog := cleared_log_trunc_mem T
  have h := S.add_mem (S.mul_mem hL (gaussian_C_mem z)) (S.mul_mem hq hlog)
  convert h using 1
  ring

theorem cleared_polynomial_power_mem (L e d : ℕ) (f : Polynomial ℂ) (hd : d ≤ e)
    (hf : Polynomial.C (L : ℂ) * f ∈ (Polynomial.mapRingHom GaussianInt.toComplex).range) :
    Polynomial.C ((L : ℂ) ^ e) * f ^ d ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have hL : Polynomial.C (L : ℂ) ∈ S := by
    simp
  have h := S.mul_mem (S.pow_mem hL (e - d)) (S.pow_mem hf d)
  have he : e = (e - d) + d := (Nat.sub_add_cancel hd).symm
  rw [he, map_pow, pow_add]
  simpa only [mul_pow, mul_assoc] using h

theorem cleared_polynomial_product_mem {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → Polynomial ℂ) (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, Polynomial.C (L i : ℂ) * f i ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range) :
    Polynomial.C (∏ i ∈ s, (L i : ℂ) ^ e i) * (∏ i ∈ s, f i ^ d i) ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have h := S.prod_mem (fun i hi => cleared_polynomial_power_mem (L i) (e i) (d i)
    (f i) (hd i hi) (hf i hi))
  simpa only [← Finset.prod_mul_distrib, map_prod] using h

theorem common_denominator_coeff_gaussian {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → Polynomial ℂ) (P : Polynomial GaussianInt)
    (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, Polynomial.C (L i : ℂ) * f i ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range) (k : ℕ) :
    (∏ i ∈ s, (L i : ℂ) ^ e i) *
      (P.map GaussianInt.toComplex * ∏ i ∈ s, f i ^ d i).coeff k ∈
      GaussianInt.toComplex.range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have hP : P.map GaussianInt.toComplex ∈ S := ⟨P, rfl⟩
  have h := S.mul_mem hP (cleared_polynomial_product_mem s L e d f hd hf)
  have he : P.map GaussianInt.toComplex *
      (Polynomial.C (∏ i ∈ s, (L i : ℂ) ^ e i) * ∏ i ∈ s, f i ^ d i) =
      Polynomial.C (∏ i ∈ s, (L i : ℂ) ^ e i) *
        (P.map GaussianInt.toComplex * ∏ i ∈ s, f i ^ d i) := by ring
  rw [he] at h
  have hc := (Polynomial.mem_map_range GaussianInt.toComplex).mp h k
  simpa only [Polynomial.coeff_C_mul] using hc

theorem cleared_det_log_bound_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hentries : ∀ i j, (r i : ℂ) * ((c j : ℂ) * A i j) ∈ GaussianInt.toComplex.range) :
    -(∑ i, Real.log (r i)) - ∑ j, Real.log (c j) ≤ Real.log ‖A.det‖ := by
  classical
  choose B hB using hentries
  apply cleared_det_log_bound A B r c hr hc hA
  ext i j
  exact hB i j

theorem cleared_det_log_bound_with_denominator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℝ) (D : ℝ)
    (hD : 0 < D) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i) (hA : A.det ≠ 0)
    (hentries : ∀ i j, (D : ℂ) * (r i : ℂ) * ((c j : ℂ) * A i j) ∈
      GaussianInt.toComplex.range) :
    -(Fintype.card ι : ℝ) * Real.log D - (∑ i, Real.log (r i)) -
      ∑ j, Real.log (c j) ≤ Real.log ‖A.det‖ := by
  have h := cleared_det_log_bound_of_entries A (fun i => D * r i) c
    (fun i => mul_pos hD (hr i)) hc hA (by simpa using hentries)
  simp_rw [Real.log_mul hD.ne' (hr _).ne'] at h
  rw [Finset.sum_add_distrib, Finset.sum_const] at h
  simp only [Finset.card_univ, nsmul_eq_mul] at h
  linarith

theorem shifted_truncation_product_coeff_gaussian {ι : Type*} (s : Finset ι)
    (T q e d : ι → ℕ) (z : ι → GaussianInt) (P : Polynomial GaussianInt)
    (hd : ∀ i ∈ s, d i ≤ e i) (k : ℕ) :
    (∏ i ∈ s, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (P.map GaussianInt.toComplex * ∏ i ∈ s,
        (Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
          PowerSeries.trunc (T i) (PowerSeries.log ℂ)) ^ d i).coeff k ∈
      GaussianInt.toComplex.range := by
  exact common_denominator_coeff_gaussian s (fun i => Nat.lcmUpto (T i)) e d _ P hd
    (fun i hi => cleared_shifted_log_trunc_mem (T i) (q i) (z i)) k

theorem column_log_cost_le {ι : Type*} (s : Finset ι) (a q : ι → ℕ) :
    (∑ i ∈ s, (a i : ℝ) * Real.log (q i)) ≤
      ∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)

theorem sum_exponents_le_weight_div {ι : Type*} (s : Finset ι)
    (a : ι → ℕ) (w : ι → ℝ) (wmin : ℝ) (hmin : 0 < wmin)
    (hw : ∀ i ∈ s, wmin ≤ w i) :
    (∑ i ∈ s, (a i : ℝ)) ≤ (∑ i ∈ s, (a i : ℝ) * w i) / wmin := by
  apply (le_div_iff₀ hmin).mpr
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hw i hi) (Nat.cast_nonneg _))

theorem row_log_cost_lower {ι : Type*} (s : Finset ι)
    (a q : ι → ℕ) (wmin U : ℝ) (hmin : 0 < wmin)
    (hw : ∀ i ∈ s, wmin ≤ (⌈Real.log (q i)⌉₊ : ℝ))
    (hbudget : (∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ)) ≤ U) :
    (∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ)) - U / wmin ≤
      ∑ i ∈ s, (a i : ℝ) * Real.log (q i) := by
  have hsum := sum_exponents_le_weight_div s a (fun i => (⌈Real.log (q i)⌉₊ : ℝ))
    wmin hmin hw
  have hsumU : (∑ i ∈ s, (a i : ℝ)) ≤ U / wmin :=
    hsum.trans (div_le_div_of_nonneg_right hbudget hmin.le)
  have hceil : (∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ)) ≤
      (∑ i ∈ s, (a i : ℝ) * Real.log (q i)) + ∑ i ∈ s, (a i : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left
      (Nat.ceil_lt_add_one (Real.log_natCast_nonneg (q i))).le (Nat.cast_nonneg (a i) : (0 : ℝ) ≤ a i)
    nlinarith only [h]
  linarith

theorem normalized_arithmetic_bound (M H b E δ logD columnCost rowCost logAbsDet : ℝ)
    (hM : 0 < M) (hH : 0 < H)
    (hclear : -M * logD - columnCost + rowCost ≤ logAbsDet)
    (hden : logD ≤ H * E)
    (hcol : columnCost ≤ M * H)
    (hrow : M * H * b - M * H * δ ≤ rowCost) :
    -(1 - b) - (E + δ) ≤ logAbsDet / (M * H) := by
  apply (le_div_iff₀ (mul_pos hM hH)).mpr
  have hd := mul_le_mul_of_nonneg_left hden hM.le
  nlinarith only [hclear, hd, hcol, hrow]


end Arithmetic
namespace InterpolationMatrix

theorem entry_eq_binomial_product {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (β : Fin m → ℕ)
    (h : ℕ) (α : Fin m → ℕ) :
    entry r G j s β h α =
      (∏ i, ((α i).choose (β i) : ℂ)) *
        (((1 + Polynomial.X) ^ h * ∏ i,
          (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i)).coeff s) := by
  classical
  have hexp := RowTranslation.shiftCoefficient_eq
    (fun i => Polynomial.C ((j : ℂ) * r i) + G i)
    (exponentVector β) (exponentVector α)
  rw [RowTranslation.shiftCoefficient, RowTranslation.shift_monomial_one] at hexp
  simp only [exponentVector_apply] at hexp
  have hp : (monomialImage r G j h α).coeff (exponentVector β) =
      (1 + Polynomial.X) ^ h * ∏ i,
        ((α i).choose (β i) : Polynomial ℂ) *
          (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i) := by
    rw [monomialImage, MvPolynomial.coeff_C_mul]
    simpa only [add_comm] using congrArg (fun x => (1 + Polynomial.X) ^ h * x) hexp
  rw [entry, hp, Finset.prod_mul_distrib]
  have hc : (∏ i, ((α i).choose (β i) : Polynomial ℂ)) =
      Polynomial.C (∏ i, ((α i).choose (β i) : ℂ)) := by simp
  rw [hc]
  rw [show (1 + Polynomial.X) ^ h *
      (Polynomial.C (∏ i, ((α i).choose (β i) : ℂ)) *
        ∏ i, (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i)) =
      Polynomial.C (∏ i, ((α i).choose (β i) : ℂ)) *
        ((1 + Polynomial.X) ^ h *
          ∏ i, (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i)) by ring]
  rw [Polynomial.coeff_C_mul]

theorem entry_eq_zero_of_not_le {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (β : Fin m → ℕ)
    (h : ℕ) (α : Fin m → ℕ) (hβα : ¬ ∀ i, β i ≤ α i) :
    entry r G j s β h α = 0 := by
  classical
  push Not at hβα
  obtain ⟨i, hi⟩ := hβα
  rw [entry_eq_binomial_product]
  have hprod : (∏ k, ((α k).choose (β k) : ℂ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hi]
  rw [hprod, zero_mul]

theorem scalar_product_mul_coeff {m : ℕ} (q : Fin m → ℂ)
    (d : Fin m → ℕ) (P : Polynomial ℂ) (F : Fin m → Polynomial ℂ) (s : ℕ) :
    (∏ i, q i ^ d i) * (P * ∏ i, F i ^ d i).coeff s =
      (P * ∏ i, (Polynomial.C (q i) * F i) ^ d i).coeff s := by
  have he : P * ∏ i, (Polynomial.C (q i) * F i) ^ d i =
      Polynomial.C (∏ i, q i ^ d i) * (P * ∏ i, F i ^ d i) := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    ring
  rw [he, Polynomial.coeff_C_mul]

theorem gaussian_center_cast (j : ℕ) (p : ℤ) :
    (((⟨0, 2 * (j : ℤ) * p⟩ : GaussianInt) : ℂ)) =
      (j : ℂ) * (2 * Complex.I * (p : ℂ)) := by
  simp only [GaussianInt.toComplex_def', Int.cast_zero, Int.cast_mul,
    Int.cast_ofNat, Int.cast_natCast, zero_add]
  ring

theorem entry_truncatedLog_cleared_gaussian {m : ℕ}
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s h : ℕ) (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      entry (fun i => 2 * Complex.I * (p i : ℂ) / (q i : ℂ))
        (fun i => truncatedLog (T i)) j s β h α ∈ GaussianInt.toComplex.range := by
  classical
  by_cases hβα : ∀ i, β i ≤ α i
  swap
  · rw [entry_eq_zero_of_not_le _ _ _ _ _ _ _ hβα, mul_zero]
    exact GaussianInt.toComplex.range.zero_mem
  have hqC : ∀ i, (q i : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast hq i
  have hratio : (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) =
      ∏ i, (q i : ℂ) ^ (α i - β i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simpa only [div_eq_mul_inv] using (pow_sub₀ (q i : ℂ) (hqC i) (hβα i)).symm
  let z : Fin m → GaussianInt := fun i => ⟨0, 2 * (j : ℤ) * p i⟩
  have hz (i : Fin m) : Polynomial.C (q i : ℂ) *
      (Polynomial.C ((j : ℂ) * (2 * Complex.I * (p i : ℂ) / (q i : ℂ))) +
        truncatedLog (T i)) =
      Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
        PowerSeries.trunc (T i) (PowerSeries.log ℂ) := by
    rw [mul_add, ← map_mul]
    congr 1
    apply congrArg Polynomial.C
    rw [show (z i : ℂ) = (j : ℂ) * (2 * Complex.I * (p i : ℂ)) from
      gaussian_center_cast j (p i)]
    field_simp [hqC i]
  have hclear := Arithmetic.shifted_truncation_product_coeff_gaussian Finset.univ
    T q e (fun i => α i - β i) z ((1 + Polynomial.X) ^ h)
    (fun i hi => (Nat.sub_le (α i) (β i)).trans (hα i)) s
  have hP : (((1 + Polynomial.X) ^ h : Polynomial GaussianInt).map GaussianInt.toComplex) =
      (1 + Polynomial.X) ^ h := by simp
  simp only [hP] at hclear
  have hchoose : (∏ i, ((α i).choose (β i) : ℂ)) ∈ GaussianInt.toComplex.range := by
    apply GaussianInt.toComplex.range.prod_mem
    intro i hi
    exact ⟨((α i).choose (β i) : GaussianInt), by simp⟩
  have hscalar := scalar_product_mul_coeff (fun i => (q i : ℂ)) (fun i => α i - β i)
    ((1 + Polynomial.X) ^ h)
    (fun i => Polynomial.C ((j : ℂ) * (2 * Complex.I * (p i : ℂ) / (q i : ℂ))) +
      truncatedLog (T i)) s
  simp_rw [hz] at hscalar
  rw [mul_div_assoc, hratio, entry_eq_binomial_product]
  have he := GaussianInt.toComplex.range.mul_mem hchoose hclear
  rw [← hscalar] at he
  convert he using 1
  ring

end InterpolationMatrix

namespace MatrixArithmetic

noncomputable def columnScale {m : ℕ} (q : Fin m → ℕ) (a : Fin m → ℕ) : ℝ :=
  ∏ i, (q i : ℝ) ^ a i

noncomputable def rowScale {m : ℕ} (q : Fin m → ℕ) (b : Fin m → ℕ) : ℝ :=
  (columnScale q b)⁻¹

noncomputable def denominator {m : ℕ} (q : Fin m → ℕ) (T : Fin m → ℕ) (H : ℝ) : ℝ :=
  ∏ i, (Nat.lcmUpto (T i) : ℝ) ^ ⌊H / logWeights q i⌋₊

theorem columnScale_pos {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (a : Fin m → ℕ) : 0 < columnScale q a := by
  exact Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast hq i) _)

theorem rowScale_pos {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (b : Fin m → ℕ) : 0 < rowScale q b :=
  inv_pos.mpr (columnScale_pos hq b)

theorem denominator_pos {m : ℕ} (q : Fin m → ℕ) (T : Fin m → ℕ) (H : ℝ) :
    0 < denominator q T H := by
  apply Finset.prod_pos
  intro i hi
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i))

theorem log_columnScale {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (a : Fin m → ℕ) :
    Real.log (columnScale q a) = ∑ i, (a i : ℝ) * Real.log (q i) := by
  rw [columnScale, Real.log_prod (by
    intro i hi
    exact pow_ne_zero _ (by exact_mod_cast (hq i).ne'))]
  simp only [Real.log_pow]

theorem log_rowScale {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (b : Fin m → ℕ) :
    Real.log (rowScale q b) = -(∑ i, (b i : ℝ) * Real.log (q i)) := by
  rw [rowScale, Real.log_inv, log_columnScale hq]

theorem log_denominator_le {m : ℕ} {q : Fin m → ℕ} (F v0 H : ℝ)
    (hF : 0 ≤ F) (hv0 : 0 < v0) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    Real.log (denominator q (truncationOrders q F v0) H) ≤
      H * (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i) := by
  have h := Arithmetic.truncation_denominator_log_le Finset.univ
    (logWeights q) F v0 H hF hv0 hH (fun i _ => hw i)
  rw [div_le_iff₀ hH] at h
  simpa [denominator, truncationOrders, mul_comm H] using h

noncomputable def rowCost {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ∑ i, (ρ.2.1 i.succ : ℝ) * Real.log (q i)

noncomputable def columnCost {m : ℕ} {K : ℕ} {w0 v0 θ : ℝ}
    (q : Fin m → ℕ) {H : ℝ}
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ∑ i, ((selection ρ).1 i.succ : ℝ) * Real.log (q i)

theorem actual_row_card_pos {m K : ℕ} {v0 θ H : ℝ} {q : Fin m → ℕ}
    (hK : 0 < K) (hv0 : 0 < v0) (hθ : 0 < θ) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    0 < Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨0, hK⟩, ⟨fun _ => 0, ?_⟩⟩⟩
  apply (InterpolationMatrix.row_mem_iff hv0 hθ hw _).mpr
  simpa using hH

theorem ceil_log_weight_pos {q : ℕ} (hq : 2 ≤ q) :
    0 < (⌈Real.log (q : ℝ)⌉₊ : ℝ) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  exact lt_of_lt_of_le (Real.log_pos hqR) (Nat.le_ceil _)

theorem column_coordinate_le_floor {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (c : PiExponent.InterpolationMatrix.Column w0 w H) (i : Fin m) :
    c.1 i.succ ≤ ⌊H / w i⌋₊ := by
  apply Nat.le_floor
  apply (le_div_iff₀ (hw i)).mpr
  have hs : w i * (c.1 i.succ : ℝ) ≤
      ∑ j, w j * (c.1 j.succ : ℝ) :=
    Finset.single_le_sum (fun j hj => mul_nonneg (hw j).le (Nat.cast_nonneg (c.1 j.succ)))
      (Finset.mem_univ i)
  have h0 : 0 ≤ w0 * (c.1 0 : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg _)
  have hb := PiExponent.InterpolationMatrix.column_weight_le hw0 hw c
  nlinarith only [hs, h0, hb]

theorem column_log_cost_le_H {m : ℕ} {w0 H : ℝ} (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (c : PiExponent.InterpolationMatrix.Column w0
      (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) :
    (∑ i, (c.1 i.succ : ℝ) * Real.log (q i : ℝ)) ≤ H := by
  have hb := PiExponent.InterpolationMatrix.column_weight_le hw0
    (fun i => ceil_log_weight_pos (hq i)) c
  have hc := PiExponent.Arithmetic.column_log_cost_le Finset.univ
    (fun i => c.1 i.succ) q
  have h0 : 0 ≤ w0 * (c.1 0 : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ i, (c.1 i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉₊ : ℝ) := hc
    _ = ∑ i, (⌈Real.log (q i : ℝ)⌉₊ : ℝ) * (c.1 i.succ : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ ≤ H := by linarith

theorem selected_column_log_cost_le {m K : ℕ} {w0 v0 θ H : ℝ}
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : PiExponent.InterpolationMatrix.Row K v0 θ
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H →
      PiExponent.InterpolationMatrix.Column w0
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) :
    (∑ ρ, ∑ i, ((selection ρ).1 i.succ : ℝ) * Real.log (q i : ℝ)) ≤
      (Fintype.card (PiExponent.InterpolationMatrix.Row K v0 θ
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) : ℝ) * H := by
  calc
    _ ≤ ∑ ρ, H := Finset.sum_le_sum (fun ρ hρ => column_log_cost_le_H q hq hw0 (selection ρ))
    _ = _ := by simp

theorem row_weighted_cost_le {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i)
    (ρ : PiExponent.InterpolationMatrix.Row K v0 θ w H) :
    (∑ i, (ρ.2.1 i.succ : ℝ) * w i) ≤ H * θ := by
  have hb := PiExponent.InterpolationMatrix.row_weight_lt hv0 hθ hw ρ
  have h0 : 0 ≤ v0 * (ρ.2.1 0 : ℝ) := mul_nonneg hv0.le (Nat.cast_nonneg _)
  have hh : (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ ≤ H := by linarith
  have hm := (div_le_iff₀ hθ).mp hh
  simpa only [mul_comm] using hm

theorem all_row_log_cost_lower {m K : ℕ} {v0 θ H wmin : ℝ}
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hv0 : 0 < v0) (hθ : 0 < θ) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) :
    (∑ ρ : PiExponent.InterpolationMatrix.Row K v0 θ
      (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H,
        ∑ i, (ρ.2.1 i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) -
      (Fintype.card (PiExponent.InterpolationMatrix.Row K v0 θ
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) : ℝ) * H * θ / wmin ≤
    ∑ ρ : PiExponent.InterpolationMatrix.Row K v0 θ
      (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H,
        ∑ i, (ρ.2.1 i.succ : ℝ) * Real.log (q i : ℝ) := by
  have hrow (ρ : PiExponent.InterpolationMatrix.Row K v0 θ
      (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) :=
    PiExponent.Arithmetic.row_log_cost_lower Finset.univ (fun i => ρ.2.1 i.succ)
      q wmin (H * θ) hmin (fun i hi => hwmin i)
      (row_weighted_cost_le hv0 hθ (fun i => ceil_log_weight_pos (hq i)) ρ)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun ρ hρ => hrow ρ)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_div_assoc, mul_assoc] using hs

theorem selectedMinor_entries_gaussian {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (ρ σ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :
    (denominator q (truncationOrders q F v0) H : ℂ) *
      (rowScale q (fun i => ρ.2.1 i.succ) : ℂ) *
        ((columnScale q (fun i => (selection σ).1 i.succ) : ℂ) *
          selectedMinor K w0 v0 θ F H p q selection ρ σ) ∈
        GaussianInt.toComplex.range := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have he := InterpolationMatrix.entry_truncatedLog_cleared_gaussian
    (truncationOrders q F v0) q (fun i => ⌊H / logWeights q i⌋₊) p
    (fun i => by have := hq i; omega) ρ.1.val (ρ.2.1 0) ((selection σ).1 0)
    (fun i => ρ.2.1 i.succ) (fun i => (selection σ).1 i.succ)
    (column_coordinate_le_floor hw0 hw (selection σ))
  simp only [denominator, rowScale, columnScale, selectedMinor,
    InterpolationMatrix.truncatedLogMatrix, InterpolationMatrix.matrix,
    Matrix.submatrix_apply, id_eq,
    Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.ofReal_inv]
  have hcenters : rationalCenters p q =
      (fun i => 2 * Complex.I * (p i : ℂ) / (q i : ℂ)) := rfl
  rw [← hcenters] at he
  convert he using 1
  ring

theorem selectedMinor_clearing_bound {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) *
      Real.log (denominator q (truncationOrders q F v0) H) -
      columnCost q selection + rowCost K v0 θ q H ≤
      Real.log ‖(selectedMinor K w0 v0 θ F H p q selection).det‖ := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq i)
  have hc := Arithmetic.cleared_det_log_bound_with_denominator
    (selectedMinor K w0 v0 θ F H p q selection)
    (fun ρ => rowScale q (fun i => ρ.2.1 i.succ))
    (fun σ => columnScale q (fun i => (selection σ).1 i.succ))
    (denominator q (truncationOrders q F v0) H)
    (denominator_pos _ _ _) (fun ρ => rowScale_pos hqpos _)
    (fun σ => columnScale_pos hqpos _) hdet
    (selectedMinor_entries_gaussian p q hq hw0 selection)
  simp only [log_rowScale hqpos, log_columnScale hqpos,
    Finset.sum_neg_distrib, sub_neg_eq_add] at hc
  dsimp [columnCost, rowCost]
  linarith

theorem selectedMinor_arithmetic_lower_bound {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(1 - meanRowWeight K v0 θ q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i + θ / wmin) ≤
      Real.log ‖(selectedMinor K w0 v0 θ F H p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have hM : 0 < (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) := by
    exact_mod_cast actual_row_card_pos hK hv0 hθ hH hw
  apply Arithmetic.normalized_arithmetic_bound _ _ _ _ _ _ _ _ _ hM hH
  · exact selectedMinor_clearing_bound p q hq hw0 selection hdet
  · exact log_denominator_le F v0 H hF hv0 hH hw
  · exact selected_column_log_cost_le q hq hw0 selection
  · have hrow (ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :=
      Arithmetic.row_log_cost_lower Finset.univ (fun i => ρ.2.1 i.succ) q
        wmin (H * θ) hmin (fun i _ => hwmin i)
        (row_weighted_cost_le hv0 hθ hw ρ)
    have hr := Finset.sum_le_sum (s := Finset.univ) (fun ρ _ => hrow ρ)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hr
    have hb :
        (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H *
          meanRowWeight K v0 θ q H = rowWeightedSum K v0 θ q H := by
      unfold meanRowWeight
      field_simp [(mul_pos hM hH).ne']
    rw [hb]
    simpa only [rowWeightedSum, rowCost, logWeights, mul_div_assoc, mul_assoc] using hr

end MatrixArithmetic
namespace DeterminantContradiction
theorem finiteDenominators_two_le {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

theorem logWeights_eq {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

end DeterminantContradiction
end OAI.PiExponent

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) := by
  have hh := MatrixArithmetic.selectedMinor_arithmetic_lower_bound
    (finiteNumerators d) (finiteDenominators d) (finiteDenominators_two_le d)
    (Nat.zero_lt_of_lt d.K_pos) d.w0_pos d.v0_pos d.base.theta_pos d.F0_pos.le hH
    d.wstar_pos (fun i => by rw [logWeights_eq]; exact d.wstar_lower i) selection hdet
  simpa only [actualMinor, actualMean, actualRowCount,
    AdmissibleParameters.arithmeticError, logWeights_eq] using hh
