-- Prove2me | solution 1 for GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:35:16.721183+00:00
-- url     : https://prove2.me/submissions/3ed242ba-8f50-4b98-a1db-51e4ffe981d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Theorems.Thm_GlobalTheory_Mem_summable_norm_absNorm_cpow
import Theorems.Thm_GlobalTheory_Mem_tsum_eq_exp_tsum_neg_log_of_primes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (X : Ideal (𝓞 K) → ℂ), X ⊥ = 0 → X ⊤ = 1 → (∀ I J, X (I * J) = X I * X J) → (∀ I, ‖X I‖ ≤ 1) → ∀ s : ℂ, 1 < s.re → ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  intro K _ _ X hbot htop hmul hle s hs
  have hnorm : ∀ P : HeightOneSpectrum (𝓞 K), 1 < Ideal.absNorm P.asIdeal := by
    intro P
    have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
    have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    omega
  refine GlobalTheory.Mem.tsum_eq_exp_tsum_neg_log_of_primes (fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal)
    (fun P => P.prime) ?_ (fun I => X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ?_ ?_ ?_ ?_ ?_
  ·
    intro P Q h
    rw [Ideal.dvd_iff_le] at h
    exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h).symm
  · intro I J
    rw [hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  · simp [Ideal.one_eq_top, htop]
  · intro I hI hfI
    have hbot' : I ≠ ⊥ := by
      rintro rfl; exact hfI (by simp [hbot])
    have htop' : I ≠ ⊤ := by rwa [← Ideal.one_eq_top]
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop'
    have hMbot : M ≠ ⊥ := fun h => hbot' (le_bot_iff.mp (h ▸ hIM))
    exact ⟨⟨M, hM.isPrime, hMbot⟩, (Ideal.dvd_iff_le).mpr hIM⟩
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_)
      (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hle I)
  · intro P hP
    have hlt : ‖X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 := by
      have hn := hnorm P
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hr : ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by simp; linarith)
      calc ‖X P.asIdeal‖ * ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re
          ≤ 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re :=
            mul_le_mul_of_nonneg_right (hle _) (by positivity)
        _ < 1 := by rw [one_mul]; exact hr
    rw [sub_eq_zero] at hP
    rw [← hP, norm_one] at hlt
    exact lt_irrefl _ hlt
end GlobalTheory
