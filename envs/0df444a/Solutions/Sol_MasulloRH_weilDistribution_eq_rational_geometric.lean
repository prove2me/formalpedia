-- Prove2me | solution 1 for MasulloRH.weilDistribution_eq_rational_geometric
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:27:54.495995+00:00
-- url     : https://prove2.me/submissions/6250adf7-07e7-4aaf-af45-180a749a5f37

import Theorems.Thm_MasulloRH_archTerm_eq_neg_realTraceIntegral
import Mathlib
open Set MeasureTheory MasulloRH
private theorem mellin_exp_coordinates (φ : ℝ → ℂ) (w : ℂ) :
    mellin φ w = ∫ u : ℝ, φ (Real.exp u) * Complex.exp (w * (u : ℂ)) := by
  let F (t : ℝ) := (t : ℂ) ^ (w - 1) • φ t
  have he := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ))
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn F
  rw [image_univ, Real.range_exp, setIntegral_univ] at he
  change (∫ t in Ioi 0, F t) = _
  rw [he]
  apply integral_congr_ae
  filter_upwards with u
  have hpos := Real.exp_pos u
  simp only [abs_of_pos hpos, F, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne' : (Real.exp u : ℂ) ≠ 0),
    ← Complex.ofReal_log hpos.le, Real.log_exp, Complex.ofReal_exp, ← mul_assoc,
    ← Complex.exp_add, mul_comm (φ _)]
  congr 2
  ring

private theorem finite_place_change (φ : ℝ → ℂ) :
    ConnesRZ.primeSum (fun u => φ (Real.exp u)) = ∑' i, primePowerTraceTerm φ i := by
  let A (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (φ (Real.exp (Real.log n)) + φ (Real.exp (-Real.log n)))
  change ∑' n, A n = _
  have hs : Function.support A ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra h
    exact hn (by simp [A, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h])
  rw [← tsum_subtype_eq_of_support_subset hs]
  change (∑' n : {n : ℕ // IsPrimePow n}, A n.val) = _
  rw [← Nat.Primes.prodNatEquiv.tsum_eq (fun n => A n.val)]
  apply tsum_congr
  rintro ⟨p,k⟩
  let n : ℕ := p.val^(k+1)
  have hn : 0 < (n : ℝ) := by exact_mod_cast pow_pos p.property.pos (k+1)
  change A n = _
  simp only [A, Real.exp_neg, Real.exp_log hn]
  simp [n, primePowerTraceTerm, ArithmeticFunction.vonMangoldt_apply_pow,
    ArithmeticFunction.vonMangoldt_apply_prime p.property]

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ConnesRZ.weilDistribution (fun u => φ (Real.exp u)) =
      (mellin φ (1/2) + mellin φ (-1/2)) - ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) := by
  have hm (z : ℂ) : ConnesRZ.mellinHat (fun u => φ (Real.exp u)) z = mellin φ (z - 1/2) :=
    (mellin_exp_coordinates φ _).symm
  rw [ConnesRZ.weilDistribution, hm, hm, finite_place_change, archTerm_eq_neg_realTraceIntegral φ hφ]
  norm_num
  <;> abel
