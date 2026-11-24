-- Prove2me | solution 1 for GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:56.389344+00:00
-- url     : https://prove2.me/submissions/257341e0-74e1-4d4a-b396-cda89059288f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqOneOfNormOneValuationSubOneSmall
import Theorems.Thm_GlobalTheory_abs_norm_eq_prod_embeddings_closeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E : Type) [Field E] [NumberField E] (ε : E)
    (w : HeightOneSpectrum (𝓞 E)) (K : ℕ) (hK : Module.finrank ℚ E < K)
    (hint : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ε ≤ 1)
    (habs : ∀ φ : E →+* ℂ, ‖φ ε‖ = 1)
    (hw : w.valuation E (ε - 1) ≤ WithZero.exp (-(K : ℤ))) : ε = 1 := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E ε hint
  by_contra hne
  have hxE : algebraMap (𝓞 E) E (r - 1) = ε - 1 := by simp [hr]
  have hx0 : r - 1 ≠ 0 := by
    intro h
    rw [h, map_zero] at hxE
    exact hne (sub_eq_zero.mp hxE.symm)
  have hmem : r - 1 ∈ w.asIdeal ^ K := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    convert hw using 2
  have hdvd : w.asIdeal ^ K ∣ Ideal.span {r - 1} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hN := map_dvd Ideal.absNorm hdvd
  rw [map_pow, Ideal.absNorm_span_singleton] at hN
  have hnz : (Algebra.norm ℤ (r - 1)).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hx0
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hnz) hN
  have h2 : 2 ≤ Ideal.absNorm w.asIdeal := by
    have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
    omega
  have hlow : 2 ^ K ≤ (Algebra.norm ℤ (r - 1)).natAbs :=
    le_trans (Nat.pow_le_pow_left h2 K) hle
  have hup : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) ≤ 2 ^ Module.finrank ℚ E := by
    have h1 : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) = |((Algebra.norm ℚ (ε - 1) : ℚ) : ℝ)| := by
      rw [← hxE, ← Algebra.coe_norm_int (r - 1), Nat.cast_natAbs]
      push_cast
      rfl
    rw [h1, abs_norm_eq_prod_embeddings_closeOne]
    calc ∏ φ : E →+* ℂ, ‖φ (ε - 1)‖ ≤ ∏ _φ : E →+* ℂ, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun φ _ => ?_)
          rw [map_sub, map_one]
          calc ‖φ ε - 1‖ ≤ ‖φ ε‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [habs φ, norm_one]; norm_num
      _ = 2 ^ Module.finrank ℚ E := by
          rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card]
  have hlowR : (2 : ℝ) ^ K ≤ 2 ^ Module.finrank ℚ E := by
    have : ((2 ^ K : ℕ) : ℝ) ≤ ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) := by exact_mod_cast hlow
    push_cast at this
    linarith
  have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlowR
  omega
end GlobalTheory
