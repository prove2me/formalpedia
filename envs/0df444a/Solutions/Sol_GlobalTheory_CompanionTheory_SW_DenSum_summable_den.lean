-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DenSum.summable_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:05:58.066504+00:00
-- url     : https://prove2.me/submissions/3f74aaaf-5340-4dab-ba73-204e8c156f85

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DenSum_den_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DenSum_dI_add
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DenSum_dI_ne_bot
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DenSum_fibre_bound
import Theorems.Thm_GlobalTheory_countable_ideal_and_summable_absNorm_rpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DenSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.DenSum
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F], ∀ M : ℕ, 3 ≤ M → ∀ N : ℕ, 0 < N → (∀ (b : F) (r : 𝓞 F), den (b + (r : F)) = den b) ∧ (∀ b : F, 0 < den b) ∧ ∀ s : Set F, (∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b') → Summable fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹ := by
  intro F _ _ M hM N hN
  refine ⟨fun b r => by rw [den_eq, den_eq, dI_add], fun b => ?_, fun s hs => ?_⟩
  · rw [den_eq]
    exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact dI_ne_bot b)
  · have hsum2 := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).1
    have hfin : ∀ I : Ideal (𝓞 F), Finite {b : s // dI (b : F) = I} := by
      intro I
      by_cases hI : I = ⊥
      · subst hI
        haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩
        infer_instance
      · exact (fibre_bound N hN s hs I hI).1
    let f : s → ℝ := fun b => ((den (b : F) : ℝ) ^ M)⁻¹
    show Summable f
    rw [← (Equiv.sigmaFiberEquiv (fun b : s => dI (b : F))).summable_iff]
    refine (summable_sigma_of_nonneg (fun _ => by simp only [Function.comp, f]; positivity)).mpr ⟨fun I => ?_, ?_⟩
    · haveI := hfin I
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le (fun I => tsum_nonneg (fun _ => by simp only [Function.comp, f]; positivity)) (fun I => ?_)
        (hsum2.mul_left ((N : ℝ) ^ Module.finrank ℤ (𝓞 F)))
      by_cases hI : I = ⊥
      · subst hI
        haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩
        rw [tsum_empty]
        positivity
      · have hterm : ∀ y : {b : s // dI (b : F) = I},
            (f ∘ ⇑(Equiv.sigmaFiberEquiv fun b : s => dI (b : F))) ⟨I, y⟩ = ((Ideal.absNorm I : ℝ) ^ M)⁻¹ := by
          rintro ⟨b, hb⟩
          simp [f, den_eq, hb]
        rw [tsum_congr hterm, tsum_const, nsmul_eq_mul]
        have hc := (fibre_bound N hN s hs I hI).2
        have hn1 : (1 : ℝ) ≤ Ideal.absNorm I := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
        calc (Nat.card {b : s // dI (b : F) = I} : ℝ) * ((Ideal.absNorm I : ℝ) ^ M)⁻¹
            ≤ ((N : ℝ) ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I) * ((Ideal.absNorm I : ℝ) ^ M)⁻¹ := by
              gcongr
              exact_mod_cast hc
          _ ≤ (N : ℝ) ^ Module.finrank ℤ (𝓞 F) * (Ideal.absNorm I : ℝ) ^ (-(2:ℝ)) := by
              rw [Real.rpow_neg (by positivity), mul_assoc]
              gcongr
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              have ha : (0:ℝ) < Ideal.absNorm I := by linarith
              have hM1 : (Ideal.absNorm I : ℝ) ^ M = (Ideal.absNorm I : ℝ) * (Ideal.absNorm I : ℝ) ^ (M - 1) := by
                rw [← pow_succ']
                congr 1
                omega
              rw [hM1, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
              exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hn1 (by omega))
end GlobalTheory.CompanionTheory.SW.DenSum
