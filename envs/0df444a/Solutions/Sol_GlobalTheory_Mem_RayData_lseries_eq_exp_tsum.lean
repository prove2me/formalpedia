-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.lseries_eq_exp_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:35:10.710005+00:00
-- url     : https://prove2.me/submissions/4579bb2d-351d-4b33-9f0e-a4f32d693ef4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Theorems.Thm_GlobalTheory_Mem_tsum_eq_exp_tsum_neg_log_of_primes
import Theorems.Thm_GlobalTheory_Mem_summable_norm_absNorm_cpow
import Theorems.Thm_GlobalTheory_Mem_RayData_coef_eq_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
namespace GlobalTheory.Mem
namespace RayData
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → LSeriesSummable (D.coef χ) s ∧ Summable (fun v : D.Pr => ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖) ∧ LSeries (D.coef χ) s = Complex.exp (∑' v : D.Pr, -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  classical
  intro K _ _ M _ D χ s hs
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hχ : ∀ c, ‖(χ c : ℂ)‖ = 1 := fun c => by
    refine (norm_eq_one_of_pow_eq_one (n := Fintype.card D.G) ?_ Fintype.card_ne_zero)
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  set f : Ideal (𝓞 K) → ℂ := fun I =>
    (if IsCoprime I (Ideal.span {(M : 𝓞 K)}) then (χ (D.cls I) : ℂ) else 0) *
      ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) with hf
  have hS := summable_norm_absNorm_cpow K hs
  have hsum : Summable fun I => ‖f I‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_) hS
    simp only [hf, norm_mul]
    split_ifs <;> simp [hχ]
  have pinj : Function.Injective fun v : D.Pr => v.1.asIdeal := fun v w h =>
    Subtype.ext (HeightOneSpectrum.ext h)
  have hfp : ∀ v : D.Pr, f v.1.asIdeal =
      (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) := fun v => by
    simp only [hf]
    rw [if_pos v.2]
  have hL : HasSum (LSeries.term (D.coef χ) s) (∑' I, f I) := by
    have h := hsum.of_norm.hasSum
    rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).hasSum_iff] at h
    refine h.sigma fun n => ?_
    have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
        (f ∘ (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ =
          (if IsCoprime I.1 (Ideal.span {(M : 𝓞 K)}) then (χ (D.cls I.1) : ℂ) else 0) *
            (n : ℂ) ^ (-s) := by
      rintro ⟨I, rfl⟩; rfl
    simp only [this]
    have e : LSeries.term (D.coef χ) s n = D.coef χ n * (n : ℂ) ^ (-s) := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp [hs0]
      · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg]
    rw [e, RayData.coef_eq_tsum]
    exact (Summable.of_finite.hasSum).mul_right _
  refine ⟨hL.summable, hS.comp_injective pinj, ?_⟩
  rw [LSeries, hL.tsum_eq]
  simp only [← hfp]
  have hone : D.cls 1 = 1 := by
    have h := D.cls_mul 1 1 isCoprime_one_left isCoprime_one_left
    rw [mul_one] at h
    exact left_eq_mul.1 h
  refine tsum_eq_exp_tsum_neg_log_of_primes (fun v : D.Pr => v.1.asIdeal) (fun v => v.1.prime)
    (fun v w h => pinj ?_) f (fun I J => ?_) ?_ (fun I hI hfI => ?_) hsum (fun v => ?_)
  · exact (w.1.isMaximal.eq_of_le v.1.isPrime.ne_top (Ideal.le_of_dvd h)).symm
  · simp only [hf, IsCoprime.mul_left_iff, map_mul, Nat.cast_mul]
    rw [natCast_mul_natCast_cpow]
    by_cases hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})
    · by_cases hJ : IsCoprime J (Ideal.span {(M : 𝓞 K)})
      · simp only [hI, hJ, and_self, if_true, D.cls_mul I J hI hJ, map_mul, Units.val_mul]
        ring
      · simp [hJ]
    · simp [hI]
  · simp only [hf]
    rw [if_pos isCoprime_one_left, hone]
    simp
  · have hc : IsCoprime I (Ideal.span {(M : 𝓞 K)}) := by
      by_contra hc
      simp [hf, hc] at hfI
    have h0 : I ≠ ⊥ := by
      rintro rfl
      simp [hf, hs0] at hfI
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I (by simpa using hI)
    have hP0 : P ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hIP))
    have hd : P ∣ I := Ideal.dvd_iff_le.2 hIP
    exact ⟨⟨⟨P, hP.isPrime, hP0⟩, hc.of_isCoprime_of_dvd_left hd⟩, hd⟩
  · intro h
    have h1 : ‖f v.1.asIdeal‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
    have hN : 1 < Ideal.absNorm v.1.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v.1
    rw [hfp, norm_mul, hχ, one_mul, norm_natCast_cpow_of_pos (by omega)] at h1
    refine absurd h1 (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) ?_).ne
    simp only [neg_re]
    linarith
end RayData
end GlobalTheory.Mem
