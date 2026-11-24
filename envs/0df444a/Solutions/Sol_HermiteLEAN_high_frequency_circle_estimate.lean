-- Prove2me | solution 1 for HermiteLEAN.high_frequency_circle_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:09.324487+00:00
-- url     : https://prove2.me/submissions/b49ffadb-f5e5-4b5b-9a7f-05b249231e24

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCircleEstimate
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Theorems.Thm_FockSPR_high_freq_band_estimate

section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
namespace HermiteLEAN
private theorem sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
      ∑ m : Fin L, f (N + m.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun m => f (N + m)),
    show Finset.Icc N (N + L - 1)
        = Finset.map ⟨(N + ·), add_right_injective N⟩ (Finset.range L) by
        ext x
        simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Icc,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨_, _⟩
          exact ⟨x - N, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩
          omega,
    Finset.sum_map]
  rfl
end HermiteLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermiteLEAN
namespace HermiteLEAN
theorem _root_.solution
    (N L : ℕ)
    (hN : 1 ≤ N)
    (hL : 1 ≤ L)
    (c : ℕ → ℂ)
    (hband : 1343 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2) :
    circleL2Sq (positiveTrigonometricPolynomial (frequencyBand N L) c)
      ≤ 32 * circleRhoNormSq (positiveTrigonometricPolynomial (frequencyBand N L) c) := by
  have hband_nat : 1343 * L ^ 2 ≤ N ^ 2 := by exact_mod_cast hband
  have hpoly :
      positiveTrigonometricPolynomial (frequencyBand N L) c =
        fun t => ∑ m : Fin L, c (N + m.val) * fourier ((N + m.val : ℕ) : ℤ) t := by
    ext t
    rw [positiveTrigonometricPolynomial, frequencyBand, sum_Icc_eq_sum_Fin N L hL]
  have h := FockSPR.high_freq_band_estimate hN hL hband_nat (fun m => c (N + m.val))
      (positiveTrigonometricPolynomial (frequencyBand N L) c) hpoly
  simp only [T, FockSPR.T, circleL2Sq, circleRhoNormSq, positiveTrigonometricPolynomial,
    frequencyBand, FockSPR.circleNormSq, rho, FockSPR.rho, sq_abs] at h ⊢
  exact h
end HermiteLEAN
