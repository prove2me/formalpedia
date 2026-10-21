-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.selectedMinor_denominator_clear_v2
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:02:01.996672+00:00
-- url     : https://prove2.me/submissions/0649c52b-f99f-47c3-99d1-9bea282b55c5

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_entry_truncatedLog_cleared_gaussian
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_row_card_pos

open scoped BigOperators

namespace OAI.PiExponent.MatrixArithmetic

/-!
### Elementary facts about log weights, the weighted simplex domains, and the
MvPolynomial expansion of the interpolation matrix entries.
-/

theorem logWeights_pos_local {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 2 ≤ q i) (i : Fin m) :
    0 < logWeights q i := by
  have h1 : (1 : ℝ) < (q i : ℝ) := by exact_mod_cast (by have := hq i; omega : 1 < q i)
  exact lt_of_lt_of_le (Real.log_pos h1) (Nat.le_ceil _)

theorem log_le_logWeights_local {m : ℕ} (q : Fin m → ℕ) (i : Fin m) :
    Real.log (q i : ℝ) ≤ logWeights q i :=
  Nat.le_ceil _

theorem realWeightedSimplex_mem_local {d : ℕ} {w : Fin d → ℝ} {H : ℝ} {a : Fin d → ℕ} :
    a ∈ PiExponent.realWeightedSimplex w H ↔
      (∀ i, a i ≤ ⌊H / w i⌋₊) ∧ (∑ i, w i * (a i : ℝ)) ≤ H := by
  classical
  simp only [PiExponent.realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range, Nat.lt_succ_iff]

theorem Column.exponent_le_local {m : ℕ} {w0 : ℝ} {w : Fin m → ℝ} {H : ℝ}
    (c : InterpolationMatrix.Column w0 w H) (i : Fin m) :
    c.1 i.succ ≤ ⌊H / w i⌋₊ := by
  have h := (realWeightedSimplex_mem_local
    (w := InterpolationMatrix.columnWeights w0 w) (H := H) (a := c.1)).mp c.2
  simpa [InterpolationMatrix.columnWeights] using h.1 i.succ

theorem Column.weighted_sum_le_local {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ} (hw0 : 0 < w0)
    (c : InterpolationMatrix.Column w0 w H) :
    (∑ i, w i * (c.1 i.succ : ℝ)) ≤ H := by
  have h := (realWeightedSimplex_mem_local
    (w := InterpolationMatrix.columnWeights w0 w) (H := H) (a := c.1)).mp c.2
  have hsum := h.2
  rw [Fin.sum_univ_succ] at hsum
  simp only [InterpolationMatrix.columnWeights, Fin.val_zero, Fin.cases_zero,
    Fin.cases_succ] at hsum
  have h0 : 0 ≤ w0 * (c.1 0 : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg _)
  linarith

section MvExpansion

variable {m : ℕ}

/-- Binomial expansion of a single shifted variable. -/
theorem mv_shifted_X_pow_local (c : Fin m → Polynomial ℂ) (i : Fin m) (n : ℕ) :
    (MvPolynomial.X i + MvPolynomial.C (c i) :
        MvPolynomial (Fin m) (Polynomial ℂ)) ^ n =
      ∑ b : Fin (n + 1),
        MvPolynomial.C (((n.choose (b : ℕ) : ℕ) : Polynomial ℂ) *
            c i ^ (n - (b : ℕ))) * MvPolynomial.X i ^ (b : ℕ) := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro b _
  simp only [map_mul, map_pow, map_natCast]
  ring

/-- Expansion of a product of shifted variables as a sum over multi-indices. -/
theorem mv_shifted_product_expansion_local (c : Fin m → Polynomial ℂ) (a : Fin m → ℕ) :
    (∏ i, (MvPolynomial.X i + MvPolynomial.C (c i) :
        MvPolynomial (Fin m) (Polynomial ℂ)) ^ a i) =
      ∑ b : (∀ i, Fin (a i + 1)),
        MvPolynomial.C (∏ i, (((a i).choose (b i : ℕ) : ℕ) : Polynomial ℂ) *
            c i ^ (a i - (b i : ℕ))) *
          MvPolynomial.monomial
            (InterpolationMatrix.exponentVector (fun i => (b i : ℕ))) 1 := by
  simp_rw [mv_shifted_X_pow_local]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.prod_X_pow]
  have hidx : Finsupp.indicator Finset.univ (fun i _ => (b i : ℕ)) =
      InterpolationMatrix.exponentVector (fun i => (b i : ℕ)) := by
    ext i
    simp [Finsupp.indicator, InterpolationMatrix.exponentVector]
  rw [hidx]

/-- An entry of the interpolation matrix vanishes unless the row exponent vector is
pointwise bounded by the column exponent vector. -/
theorem entry_eq_zero_of_not_le_local {m : ℕ} (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (j s h : ℕ) (β α : Fin m → ℕ) (hβα : ¬ ∀ i, β i ≤ α i) :
    InterpolationMatrix.entry r G j s β h α = 0 := by
  classical
  push_neg at hβα
  obtain ⟨i₀, hi₀⟩ := hβα
  have hexp := mv_shifted_product_expansion_local
    (c := fun i => Polynomial.C ((j : ℂ) * r i) + G i) (a := α)
  have hexp' : (∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
        MvPolynomial.X i : MvPolynomial (Fin m) (Polynomial ℂ)) ^ α i) =
      ∑ b : (∀ i, Fin (α i + 1)),
        MvPolynomial.C (∏ i, (((α i).choose (b i : ℕ) : ℕ) : Polynomial ℂ) *
            (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - (b i : ℕ))) *
          MvPolynomial.monomial
            (InterpolationMatrix.exponentVector (fun i => (b i : ℕ))) 1 := by
    rw [← hexp]
    apply Finset.prod_congr rfl
    intro i _
    rw [add_comm]
  have hexp'' : InterpolationMatrix.monomialImage r G j h α =
      MvPolynomial.C ((1 + Polynomial.X) ^ h) *
        ∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
          MvPolynomial.X i : MvPolynomial (Fin m) (Polynomial ℂ)) ^ α i := rfl
  have hmv : MvPolynomial.coeff (InterpolationMatrix.exponentVector β)
      (∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
        MvPolynomial.X i : MvPolynomial (Fin m) (Polynomial ℂ)) ^ α i) = 0 := by
    rw [hexp', MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro b _
    have hidx : InterpolationMatrix.exponentVector (fun i => (b i : ℕ)) ≠
        InterpolationMatrix.exponentVector β := by
      intro he
      have hi := congrArg (fun d : Fin m →₀ ℕ => d i₀) he
      simp [InterpolationMatrix.exponentVector] at hi
      have hlt : (b i₀ : ℕ) < α i₀ + 1 := (b i₀).isLt
      omega
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, if_neg hidx, mul_zero]
  rw [InterpolationMatrix.entry, hexp'', MvPolynomial.coeff_C_mul, hmv, mul_zero,
    Polynomial.coeff_zero]

end MvExpansion

end OAI.PiExponent.MatrixArithmetic

namespace OAI.PiExponent.MatrixArithmetic

/-! ### Size estimates for the truncation lcm denominators (inlined from the
original `Arithmetic` module). -/

theorem log_lcmUpto_le_local (n : ℕ) :
    Real.log (Nat.lcmUpto n : ℝ) ≤ Arithmetic.lcmConstant * n := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  exact Chebyshev.psi_le_const_mul_self (by positivity)

theorem log_lcm_power_product_local {ι : Type*} (s : Finset ι) (T e : ι → ℕ) :
    Real.log (∏ i ∈ s, (Nat.lcmUpto (T i) : ℝ) ^ e i) ≤
      Arithmetic.lcmConstant * ∑ i ∈ s, (e i : ℝ) * T i := by
  rw [Real.log_prod (by
    intro i _
    exact pow_ne_zero _ (by exact_mod_cast Nat.lcmUpto_ne_zero (T i)))]
  simp_rw [Real.log_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (log_lcmUpto_le_local (T i))
    (Nat.cast_nonneg (e i) : (0 : ℝ) ≤ e i)
  nlinarith only [h]

theorem log_lcm_floor_product_local {ι : Type*} (s : Finset ι)
    (T : ι → ℕ) (w : ι → ℝ) (H : ℝ) (hH : 0 ≤ H) (hw : ∀ i ∈ s, 0 < w i) :
    Real.log (∏ i ∈ s, (Nat.lcmUpto (T i) : ℝ) ^ ⌊H / w i⌋₊) ≤
      H * Arithmetic.lcmConstant * ∑ i ∈ s, (T i : ℝ) / w i := by
  calc
    _ ≤ Arithmetic.lcmConstant * ∑ i ∈ s, (⌊H / w i⌋₊ : ℝ) * T i :=
      log_lcm_power_product_local s T _
    _ ≤ Arithmetic.lcmConstant * ∑ i ∈ s, (H / w i) * T i := by
      apply mul_le_mul_of_nonneg_left _ Arithmetic.lcmConstant_pos.le
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (T i))
      exact Nat.floor_le (div_nonneg hH (hw i hi).le)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem sum_ceil_truncation_div_local {ι : Type*} (s : Finset ι)
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

theorem truncation_denominator_log_local {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (F v H : ℝ) (hF : 0 ≤ F) (hv : 0 < v) (hH : 0 < H)
    (hw : ∀ i ∈ s, 0 < w i) :
    Real.log (∏ i ∈ s, (Nat.lcmUpto (⌈F * w i / v⌉₊) : ℝ) ^ ⌊H / w i⌋₊) / H ≤
      Arithmetic.lcmConstant * F * s.card / v + Arithmetic.lcmConstant * ∑ i ∈ s, 1 / w i := by
  apply (div_le_iff₀ hH).mpr
  calc
    _ ≤ H * Arithmetic.lcmConstant * ∑ i ∈ s, (⌈F * w i / v⌉₊ : ℝ) / w i :=
      log_lcm_floor_product_local s _ w H hH.le hw
    _ ≤ H * Arithmetic.lcmConstant * (F * s.card / v + ∑ i ∈ s, 1 / w i) :=
      mul_le_mul_of_nonneg_left (sum_ceil_truncation_div_local s w F v hF hv hw)
        (mul_pos hH Arithmetic.lcmConstant_pos).le
    _ = _ := by ring

theorem det_row_column_scale_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℂ) :
    Matrix.det (fun i j => r i * (c j * A i j)) =
      (∏ i, r i) * (∏ j, c j) * A.det := by
  calc
    _ = (∏ i, r i) * (Matrix.of fun i j => c j * A i j).det :=
      Matrix.det_mul_column r (Matrix.of fun i j => c j * A i j)
    _ = _ := by rw [Matrix.det_mul_row c A]; ring

end OAI.PiExponent.MatrixArithmetic

namespace OAI.PiExponent.MatrixArithmetic

theorem solution_aux {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    ∃ D : ℕ, 0 < D ∧
      ∃ g : GaussianInt,
        (D : ℂ) * (selectedMinor K w0 v0 θ F H p q selection).det = (g : ℂ) ∧
        Real.log (D : ℝ) ≤
          ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) *
            ((1 - meanRowWeight K v0 θ q H) +
              (Arithmetic.lcmConstant * F * m / v0 +
                Arithmetic.lcmConstant *
                  (∑ i, 1 / logWeights q i) + θ / wmin)) := by
  classical
  let ι : Type := InterpolationMatrix.Row K v0 θ (logWeights q) H
  let T : Fin m → ℕ := truncationOrders q F v0
  let e : Fin m → ℕ := fun i => ⌊H / logWeights q i⌋₊
  let M : Matrix ι ι ℂ := selectedMinor K w0 v0 θ F H p q selection
  have hqpos : ∀ i, 0 < q i := fun i => by have := hq i; omega
  have hq0 : ∀ i, (q i : ℂ) ≠ 0 := fun i => by
    exact_mod_cast (ne_of_gt (hqpos i))
  have hwpos : ∀ i, 0 < logWeights q i := fun i => logWeights_pos_local hq i
  have hMdet : M.det ≠ 0 := hdet
  have hn : 0 < (Fintype.card ι : ℝ) := by
    have h := selectedMinor_row_card_pos (m := m) (K := K) (v0 := v0) (θ := θ) (H := H)
      q hq hK hv0 hθ hH
    simpa [ι] using h
  let n : ℕ := Fintype.card ι
  have hn' : (0 : ℝ) < (n : ℝ) := by simpa [n] using hn
  have hnH : ((n : ℝ) * H) ≠ 0 := ne_of_gt (mul_pos hn' hH)

  -- Step 1: extract a perfect matching between rows and columns from the nonzero determinant
  have hmatch : ∃ πp : Equiv.Perm ι, ∀ (ρ : ι) (i : Fin m),
      ρ.2.1 i.succ ≤ (selection (πp ρ)).1 i.succ := by
    by_contra hno
    push Not at hno
    have hdet0 : M.det = 0 := by
      rw [Matrix.det_apply]
      apply Finset.sum_eq_zero
      intro τ _
      obtain ⟨ρ, i, hi⟩ := hno τ.symm
      have hz : M ρ (τ.symm ρ) = 0 := by
        have hz0 := entry_eq_zero_of_not_le_local
          (r := rationalCenters p q)
          (G := fun i => InterpolationMatrix.truncatedLog (truncationOrders q F v0 i))
          (j := ρ.1.val) (s := ρ.2.1 0) (h := (selection (τ.symm ρ)).1 0)
          (β := fun i => ρ.2.1 i.succ) (α := fun i => (selection (τ.symm ρ)).1 i.succ)
          (by push Not; exact ⟨i, hi⟩)
        change (selectedMinor K w0 v0 θ F H p q selection) ρ (τ.symm ρ) = 0
        simpa only [selectedMinor, InterpolationMatrix.truncatedLogMatrix,
          InterpolationMatrix.matrix, Matrix.submatrix_apply, id_eq] using hz0
      have hprod : (∏ i, M (τ i) i) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (τ.symm ρ))
        simpa using hz
      rw [hprod, smul_zero]
    exact hMdet hdet0
  obtain ⟨πp, hπp⟩ := hmatch
  have hAB : ∀ i : Fin m, (∑ ρ : ι, ρ.2.1 i.succ) ≤ ∑ σ : ι, (selection σ).1 i.succ := by
    intro i
    calc (∑ ρ : ι, ρ.2.1 i.succ)
        ≤ ∑ ρ : ι, (selection (πp ρ)).1 i.succ := Finset.sum_le_sum (fun ρ _ => hπp ρ i)
      _ = ∑ σ : ι, (selection σ).1 i.succ := Equiv.sum_comp πp (fun σ => (selection σ).1 i.succ)

  -- Step 2: common denominator of the matrix entries via the Gaussian clearing lemma
  let Lc : ℂ := ∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i
  let Mr : ι → ℂ := fun ρ => ∏ i, (q i : ℂ) ^ (ρ.2.1 i.succ)
  let Mc : ι → ℂ := fun σ => ∏ i, (q i : ℂ) ^ ((selection σ).1 i.succ)
  have hclear : ∀ (ρ σ : ι), ∃ g : GaussianInt, (g : ℂ) = Lc * Mc σ / Mr ρ * M ρ σ := by
    intro ρ σ
    have h := InterpolationMatrix.entry_truncatedLog_cleared_gaussian (m := m)
      (T := truncationOrders q F v0) (q := q) (e := fun i => ⌊H / logWeights q i⌋₊) (p := p)
      (hq := fun i => ne_of_gt (hqpos i))
      (j := ρ.1.val) (s := ρ.2.1 0) (h := (selection σ).1 0)
      (β := fun i => ρ.2.1 i.succ) (α := fun i => (selection σ).1 i.succ)
      (fun i => Column.exponent_le_local (w := logWeights q) (selection σ) i)
    rw [RingHom.mem_range] at h
    obtain ⟨g, hg⟩ := h
    refine ⟨g, ?_⟩
    dsimp only [Lc, Mr, Mc, M, e, T]
    simp only [selectedMinor, InterpolationMatrix.truncatedLogMatrix,
      InterpolationMatrix.matrix, Matrix.submatrix_apply, id_eq]
    rw [show rationalCenters p q = fun i => 2 * Complex.I * (p i : ℂ) / (q i : ℂ) from rfl,
      ← hg]
  let Cn : ι → ι → GaussianInt := fun ρ σ => Classical.choose (hclear ρ σ)
  have hCn : ∀ ρ σ, (Cn ρ σ : ℂ) = Lc * Mc σ / Mr ρ * M ρ σ :=
    fun ρ σ => Classical.choose_spec (hclear ρ σ)
  have hCnmat : (fun ρ σ : ι => (Cn ρ σ : ℂ)) =
      fun ρ σ : ι => (Lc / Mr ρ) * (Mc σ * M ρ σ) := by
    funext ρ σ
    rw [hCn ρ σ, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hdetC : ((Matrix.det Cn : GaussianInt) : ℂ) = (∏ ρ : ι, Lc / Mr ρ) * (∏ σ : ι, Mc σ) * M.det := by
    have hmap : ((Matrix.det Cn : GaussianInt) : ℂ) =
        Matrix.det (fun ρ σ : ι => (Cn ρ σ : ℂ)) :=
      RingHom.map_det GaussianInt.toComplex Cn
    rw [hmap, hCnmat]
    exact det_row_column_scale_local M (fun ρ : ι => Lc / Mr ρ) (fun σ : ι => Mc σ)

  -- Step 3: the integer denominator
  let A : Fin m → ℕ := fun i => ∑ σ : ι, (selection σ).1 i.succ
  let B : Fin m → ℕ := fun i => ∑ ρ : ι, ρ.2.1 i.succ
  let D : ℕ := ∏ i, (q i ^ (A i - B i) * Nat.lcmUpto (T i) ^ (e i * n))
  have hDpos : 0 < D := by
    apply Finset.prod_pos
    intro i _
    exact Nat.mul_pos (pow_pos (hqpos i) _) (pow_pos (Nat.lcmUpto_pos (T i)) _)
  have hprod_div : (∏ ρ : ι, Lc / Mr ρ) = Lc ^ n / (∏ ρ : ι, Mr ρ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
    simp [n, Finset.card_univ]
  have hDcast : (D : ℂ) = Lc ^ n * (∏ σ : ι, Mc σ) / (∏ ρ : ι, Mr ρ) := by
    have hqAB : (∏ i, (q i : ℂ) ^ (A i - B i)) =
        (∏ i, (q i : ℂ) ^ (A i)) / (∏ i, (q i : ℂ) ^ (B i)) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [pow_sub₀ _ (hq0 i) (hAB i)]
      rfl
    have hAeq : (∏ i, (q i : ℂ) ^ (A i)) = ∏ σ : ι, Mc σ := by
      calc (∏ i, (q i : ℂ) ^ (A i))
          = ∏ i, ∏ σ : ι, (q i : ℂ) ^ ((selection σ).1 i.succ) := by
            apply Finset.prod_congr rfl
            intro i _
            change (q i : ℂ) ^ (∑ σ : ι, (selection σ).1 i.succ) = _
            rw [← Finset.prod_pow_eq_pow_sum]
        _ = ∏ σ : ι, ∏ i, (q i : ℂ) ^ ((selection σ).1 i.succ) := Finset.prod_comm
        _ = ∏ σ : ι, Mc σ := rfl
    have hBeq : (∏ i, (q i : ℂ) ^ (B i)) = ∏ ρ : ι, Mr ρ := by
      calc (∏ i, (q i : ℂ) ^ (B i))
          = ∏ i, ∏ ρ : ι, (q i : ℂ) ^ (ρ.2.1 i.succ) := by
            apply Finset.prod_congr rfl
            intro i _
            change (q i : ℂ) ^ (∑ ρ : ι, ρ.2.1 i.succ) = _
            rw [← Finset.prod_pow_eq_pow_sum]
        _ = ∏ ρ : ι, ∏ i, (q i : ℂ) ^ (ρ.2.1 i.succ) := Finset.prod_comm
        _ = ∏ ρ : ι, Mr ρ := rfl
    have hLpow : Lc ^ n = ∏ i, (Nat.lcmUpto (T i) : ℂ) ^ (e i * n) := by
      change (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) ^ n = _
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_mul]
    have hDval : (D : ℂ) = (∏ i, (q i : ℂ) ^ (A i - B i)) *
        (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ (e i * n)) := by
      dsimp only [D]
      push_cast
      rw [Finset.prod_mul_distrib]
    rw [hDval, hqAB, hAeq, hBeq, hLpow]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hDrew : (D : ℂ) = (∏ ρ : ι, Lc / Mr ρ) * (∏ σ : ι, Mc σ) := by
    rw [hDcast, hprod_div]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hDdet : (D : ℂ) * M.det = ((Matrix.det Cn : GaussianInt) : ℂ) := by
    rw [hDrew, mul_assoc, hdetC]
    ring

  -- Step 4: logarithmic bound for D
  have hlogD : Real.log (D : ℝ) =
      (∑ i, ((A i - B i : ℕ) : ℝ) * Real.log (q i : ℝ)) +
        n * (∑ i, (e i : ℝ) * Real.log (Nat.lcmUpto (T i) : ℝ)) := by
    have hDform : (D : ℝ) =
        ∏ i, ((q i : ℝ) ^ (A i - B i) * (Nat.lcmUpto (T i) : ℝ) ^ (e i * n)) := by
      dsimp only [D]
      push_cast
      rfl
    rw [hDform, Real.log_prod (fun i _ => by
      have h1 : (0 : ℝ) < (q i : ℝ) := by exact_mod_cast hqpos i
      have h2 : (0 : ℝ) < (Nat.lcmUpto (T i) : ℝ) := by
        exact_mod_cast Nat.lcmUpto_pos (T i)
      exact ne_of_gt (mul_pos (pow_pos h1 _) (pow_pos h2 _)))]
    have hterm : ∀ i, Real.log ((q i : ℝ) ^ (A i - B i) *
        (Nat.lcmUpto (T i) : ℝ) ^ (e i * n)) =
        ((A i - B i : ℕ) : ℝ) * Real.log (q i : ℝ) +
          ((e i * n : ℕ) : ℝ) * Real.log (Nat.lcmUpto (T i) : ℝ) := by
      intro i
      have h1 : (0 : ℝ) < (q i : ℝ) := by exact_mod_cast hqpos i
      have h2 : (0 : ℝ) < (Nat.lcmUpto (T i) : ℝ) := by
        exact_mod_cast Nat.lcmUpto_pos (T i)
      rw [Real.log_mul (ne_of_gt (pow_pos h1 _)) (ne_of_gt (pow_pos h2 _)),
        Real.log_pow, Real.log_pow]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have hpart1 : (∑ i, ((A i - B i : ℕ) : ℝ) * Real.log (q i : ℝ)) ≤
      (n : ℝ) * H - rowWeightedSum K v0 θ q H := by
    have h1 : (∑ i, ((A i - B i : ℕ) : ℝ) * Real.log (q i : ℝ)) ≤
        ∑ i, ((A i - B i : ℕ) : ℝ) * logWeights q i :=
      Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (log_le_logWeights_local q i) (Nat.cast_nonneg _))
    have h2 : (∑ i, ((A i - B i : ℕ) : ℝ) * logWeights q i) =
        (∑ i, (A i : ℝ) * logWeights q i) - (∑ i, (B i : ℝ) * logWeights q i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.cast_sub (hAB i)]
      ring
    have hAexp : ∀ i, (A i : ℝ) = ∑ σ : ι, ((selection σ).1 i.succ : ℝ) := by
      intro i
      change ((∑ σ : ι, (selection σ).1 i.succ : ℕ) : ℝ) = _
      push_cast
      rfl
    have hBexp : ∀ i, (B i : ℝ) = ∑ ρ : ι, (ρ.2.1 i.succ : ℝ) := by
      intro i
      change ((∑ ρ : ι, ρ.2.1 i.succ : ℕ) : ℝ) = _
      push_cast
      rfl
    have h3 : (∑ i, (A i : ℝ) * logWeights q i) =
        ∑ σ : ι, ∑ i, ((selection σ).1 i.succ : ℝ) * logWeights q i := by
      simp_rw [hAexp, Finset.sum_mul]
      rw [Finset.sum_comm]
    have h4 : (∑ σ : ι, ∑ i, ((selection σ).1 i.succ : ℝ) * logWeights q i) ≤
        (n : ℝ) * H := by
      calc (∑ σ : ι, ∑ i, ((selection σ).1 i.succ : ℝ) * logWeights q i)
          ≤ ∑ σ : ι, H := Finset.sum_le_sum (fun σ _ => by
              calc (∑ i, ((selection σ).1 i.succ : ℝ) * logWeights q i)
                  = ∑ i, logWeights q i * ((selection σ).1 i.succ : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
                _ ≤ H := Column.weighted_sum_le_local (w := logWeights q) hw0 (selection σ))
        _ = (n : ℝ) * H := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h5 : (∑ i, (B i : ℝ) * logWeights q i) = rowWeightedSum K v0 θ q H := by
      simp_rw [hBexp, Finset.sum_mul]
      rw [Finset.sum_comm]
      rfl
    calc (∑ i, ((A i - B i : ℕ) : ℝ) * Real.log (q i : ℝ))
        ≤ ∑ i, ((A i - B i : ℕ) : ℝ) * logWeights q i := h1
      _ = (∑ i, (A i : ℝ) * logWeights q i) - (∑ i, (B i : ℝ) * logWeights q i) := h2
      _ = (∑ σ : ι, ∑ i, ((selection σ).1 i.succ : ℝ) * logWeights q i) -
            rowWeightedSum K v0 θ q H := by rw [h3, h5]
      _ ≤ (n : ℝ) * H - rowWeightedSum K v0 θ q H := by linarith only [h4]
  have hlogprod : Real.log (∏ i, (Nat.lcmUpto (T i) : ℝ) ^ e i) =
      ∑ i, (e i : ℝ) * Real.log (Nat.lcmUpto (T i) : ℝ) := by
    rw [Real.log_prod (fun i _ => by
      exact ne_of_gt (pow_pos (by exact_mod_cast Nat.lcmUpto_pos (T i)) _))]
    simp only [Real.log_pow]
  have hpart2 : (∑ i, (e i : ℝ) * Real.log (Nat.lcmUpto (T i) : ℝ)) ≤
      H * (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * (∑ i, 1 / logWeights q i)) := by
    have hprodeq : (∏ i, (Nat.lcmUpto (T i) : ℝ) ^ e i) =
        ∏ i, (Nat.lcmUpto (⌈F * logWeights q i / v0⌉₊) : ℝ) ^ ⌊H / logWeights q i⌋₊ := by
      apply Finset.prod_congr rfl
      intro i _
      dsimp only [T, e]
      simp only [truncationOrders]
    have hden' : Real.log (∏ i, (Nat.lcmUpto (T i) : ℝ) ^ e i) ≤
        H * (Arithmetic.lcmConstant * F * m / v0 +
          Arithmetic.lcmConstant * (∑ i, 1 / logWeights q i)) := by
      have h := truncation_denominator_log_local (s := Finset.univ) (w := logWeights q)
        (F := F) (v := v0) (H := H) hF hv0 hH (fun i _ => hwpos i)
      rw [div_le_iff₀ hH] at h
      rw [← hprodeq, Finset.card_univ, Fintype.card_fin] at h
      rw [mul_comm] at h
      exact h
    rw [← hlogprod]
    exact hden'

  -- Step 5: assemble
  have hmain : Real.log (D : ℝ) ≤
      ((n : ℝ) * H) * ((1 - meanRowWeight K v0 θ q H) +
        (Arithmetic.lcmConstant * F * m / v0 +
          Arithmetic.lcmConstant * (∑ i, 1 / logWeights q i) + θ / wmin)) := by
    have hmean : (n : ℝ) * H * meanRowWeight K v0 θ q H = rowWeightedSum K v0 θ q H := by
      change (n : ℝ) * H *
        (rowWeightedSum K v0 θ q H / ((n : ℝ) * H)) = rowWeightedSum K v0 θ q H
      field_simp [hnH]
    have hstep : Real.log (D : ℝ) ≤
        ((n : ℝ) * H - rowWeightedSum K v0 θ q H) +
          (n : ℝ) * (H * (Arithmetic.lcmConstant * F * m / v0 +
            Arithmetic.lcmConstant * (∑ i, 1 / logWeights q i))) := by
      rw [hlogD]
      exact add_le_add hpart1 (mul_le_mul_of_nonneg_left hpart2 (Nat.cast_nonneg n))
    refine hstep.trans ?_
    have hfac : ((n : ℝ) * H - rowWeightedSum K v0 θ q H) +
        (n : ℝ) * (H * (Arithmetic.lcmConstant * F * m / v0 +
          Arithmetic.lcmConstant * (∑ i, 1 / logWeights q i))) =
        ((n : ℝ) * H) * ((1 - meanRowWeight K v0 θ q H) +
          (Arithmetic.lcmConstant * F * m / v0 +
            Arithmetic.lcmConstant * (∑ i, 1 / logWeights q i))) := by
      rw [← hmean]
      ring
    rw [hfac]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (mul_pos hn' hH))
    linarith only [div_pos hθ hmin]

  refine ⟨D, hDpos, Matrix.det Cn, ?_, ?_⟩
  · simpa only [M] using hDdet
  · simpa only [n] using hmain

end OAI.PiExponent.MatrixArithmetic

open scoped BigOperators

/-- Clearing denominators of a nonzero selected minor: there is a positive integer `D` and a
Gaussian integer `g` with `D * det = g`, and `log D` is bounded by the arithmetic budget. -/
theorem solution {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (selection : OAI.PiExponent.InterpolationMatrix.Row K v0 θ
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
      OAI.PiExponent.InterpolationMatrix.Column w0
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H)
    (hdet : (OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    ∃ D : ℕ, 0 < D ∧
      ∃ g : GaussianInt,
        (D : ℂ) * (OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection).det = (g : ℂ) ∧
        Real.log (D : ℝ) ≤
          ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 θ
            (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) *
            ((1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 θ q H) +
              (OAI.PiExponent.Arithmetic.lcmConstant * F * m / v0 +
                OAI.PiExponent.Arithmetic.lcmConstant *
                  (∑ i, 1 / OAI.PiExponent.MatrixArithmetic.logWeights q i) + θ / wmin)) :=
  OAI.PiExponent.MatrixArithmetic.solution_aux p q hq hK hw0 hv0 hθ hF hH hmin hwmin
    selection hdet
