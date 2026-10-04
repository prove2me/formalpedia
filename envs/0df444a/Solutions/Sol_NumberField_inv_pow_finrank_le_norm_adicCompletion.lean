-- Prove2me | solution 1 for NumberField.inv_pow_finrank_le_norm_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:30:35.474974+00:00
-- url     : https://prove2.me/submissions/5c7c4044-e584-46d9-a69d-7b3c04998133

import Mathlib

open NumberField

namespace NumberField.SizeAux

/-- For a nonzero algebraic integer `y`, the `v`-adic norm of `y` is at least the inverse of
`|N(y)|`. -/
theorem inv_natAbs_norm_le_norm_embedding {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (y : 𝓞 L) (hy : y ≠ 0) :
    (((Algebra.norm ℤ y).natAbs : ℕ) : ℝ)⁻¹ ≤
      ‖FinitePlace.embedding v (algebraMap (𝓞 L) L y)‖ := by
  have h1 := HeightOneSpectrum.embedding_mul_absNorm L v hy
  set a := Ideal.absNorm (v.maxPowDividing (Ideal.span {y})) with ha
  have hle : Ideal.span {y} ≤ v.maxPowDividing (Ideal.span {y}) := by
    have hne : Ideal.span {y} ≠ 0 := by
      simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hy
    conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hne]
    exact iInf_le _ v
  have hdvd : a ∣ (Algebra.norm ℤ y).natAbs := by
    rw [← Ideal.absNorm_span_singleton]
    exact Ideal.absNorm_dvd_absNorm_of_le hle
  have hn0 : (Algebra.norm ℤ y).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton]
    simpa [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] using hy
  have hale : a ≤ (Algebra.norm ℤ y).natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have ha0 : (a : ℝ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hapos : (0 : ℝ) < a := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm ha0)
  have heq : ‖FinitePlace.embedding v (algebraMap (𝓞 L) L y)‖ = (a : ℝ)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1
  rw [heq]
  exact inv_anti₀ hapos (by exact_mod_cast hale)

/-- The absolute value of the norm of `y` is bounded by `B ^ d` when every complex embedding
of `y` has size at most `B`. -/
theorem abs_norm_le_pow {L : Type*} [Field L] [NumberField L] (y : L) (B : ℝ)
    (hB : ∀ σ : L →+* ℂ, ‖σ y‖ ≤ B) :
    |(Algebra.norm ℚ y : ℝ)| ≤ B ^ Module.finrank ℚ L := by
  have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ y)
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
    norm_prod] at h
  rw [h, ← AlgHom.card ℚ L ℂ, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun σ _ => norm_nonneg _) (fun σ _ => hB (σ : L →+* ℂ))

end NumberField.SizeAux

theorem solution {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (x : L) (hx : x ≠ 0) (D : ℕ) (hD : 0 < D)
    (hint : IsIntegral ℤ ((D : L) * x)) (M : ℝ) (hM : ∀ σ : L →+* ℂ, ‖σ x‖ ≤ M) :
    (((D : ℝ) * M) ^ Module.finrank ℚ L)⁻¹ ≤ ‖algebraMap L (v.adicCompletion L) x‖ := by
  set y : 𝓞 L := ⟨(D : L) * x, hint⟩ with hydef
  have hyL : algebraMap (𝓞 L) L y = (D : L) * x := rfl
  have hD0 : (D : L) ≠ 0 := by exact_mod_cast hD.ne'
  have hy : y ≠ 0 := by
    intro h
    have : algebraMap (𝓞 L) L y = 0 := by rw [h, map_zero]
    rw [hyL] at this
    exact mul_ne_zero hD0 hx this
  -- Step 1: the `v`-adic bound for `y`.
  have h1 := NumberField.SizeAux.inv_natAbs_norm_le_norm_embedding v y hy
  -- Step 2: the archimedean bound for `N(y)`.
  have hB : ∀ σ : L →+* ℂ, ‖σ ((D : L) * x)‖ ≤ (D : ℝ) * M := by
    intro σ
    rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hM σ) (Nat.cast_nonneg _)
  have h2 := NumberField.SizeAux.abs_norm_le_pow ((D : L) * x) ((D : ℝ) * M) hB
  have hnorm : (((Algebra.norm ℤ y).natAbs : ℕ) : ℝ) = |(Algebra.norm ℚ ((D : L) * x) : ℝ)| := by
    rw [← hyL, ← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]
    push_cast
    rfl
  have hn0 : (Algebra.norm ℤ y).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton]
    simpa [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] using hy
  have hnpos : (0 : ℝ) < (((Algebra.norm ℤ y).natAbs : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have h12 : (((D : ℝ) * M) ^ Module.finrank ℚ L)⁻¹ ≤
      ‖FinitePlace.embedding v (algebraMap (𝓞 L) L y)‖ := by
    refine le_trans ?_ h1
    exact inv_anti₀ hnpos (hnorm ▸ h2)
  -- Step 3: pass from `y = D * x` to `x`.
  have h3 : ‖FinitePlace.embedding v (algebraMap (𝓞 L) L y)‖ ≤
      ‖algebraMap L (v.adicCompletion L) x‖ := by
    rw [hyL, map_mul, norm_mul]
    have hDle : ‖FinitePlace.embedding v (D : L)‖ ≤ 1 := by
      rw [FinitePlace.norm_embedding]
      exact HeightOneSpectrum.adicAbv_natCast_le_one L v D
    calc ‖FinitePlace.embedding v (D : L)‖ * ‖FinitePlace.embedding v x‖
        ≤ 1 * ‖FinitePlace.embedding v x‖ :=
          mul_le_mul_of_nonneg_right hDle (norm_nonneg _)
      _ = ‖algebraMap L (v.adicCompletion L) x‖ := one_mul _
  exact le_trans h12 h3
