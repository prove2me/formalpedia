-- Prove2me | solution 1 for GlobalTheory.MvPoly.exists_reduced_basis_integralPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:53.21538+00:00
-- url     : https://prove2.me/submissions/b7afe4f5-4ba7-4463-be42-ae5995ceac31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
import Theorems.Thm_GlobalTheory_MvPoly_span_ringOfIntegers_basis_integralPart
import Theorems.Thm_GlobalTheory_MvPoly_finrank_le_one_add_pow
import Theorems.Thm_GlobalTheory_MvPoly_exists_basis_integralPart_sum_l2Norm_sq_le
import Theorems.Thm_GlobalTheory_MvPoly_choose_add_le_one_add_pow
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_le_sqrt_choose_mul_l2Norm
import Theorems.Thm_GlobalTheory_MvPoly_l2Norm_le_l1Norm
import Theorems.Thm_GlobalTheory_MvPoly_l2Norm_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
open GlobalTheory.MvPoly
variable {K σ : Type*} [Field K]
variable [NumberField K] [Fintype σ]
namespace GlobalTheory.MvPoly
theorem _root_.solution {κ : Type*}
    (W : Submodule K (MvPolynomial σ K)) {D : ℕ} (hD : ∀ P ∈ W, P.totalDegree ≤ D)
    (S : Set (MvPolynomial σ K)) (hSH : S ⊆ integralPart W) (hSW : span K S = W) {B : ℝ}
    (hB : ∀ P ∈ S, ∀ s : K →+* ℂ, l1Norm (map s P) ≤ B)
    (ω : κ → 𝓞 K) (hω : span ℚ (Set.range fun k => (ω k : K)) = ⊤) {A : ℝ}
    (hA : ∀ (s : K →+* ℂ) k, ‖s (ω k)‖ ≤ A) {R : ℕ} (hR : R = finrank ℚ K * finrank K W) :
    R ≤ finrank ℚ K * (1 + D) ^ Fintype.card σ ∧
    ∃ b : Basis (Fin R) ℤ (integralPart W),
      (∀ i (s : K →+* ℂ), l2Norm (map s (b i : MvPolynomial σ K)) ≤
        √((R + 3) / 4) * √(finrank ℚ K) * A * B) ∧
      (∀ i (s : K →+* ℂ), l1Norm (map s (b i : MvPolynomial σ K)) ≤
        (1 + D : ℝ) ^ ((Fintype.card σ : ℝ) / 2) * (√((R + 3) / 4) * √(finrank ℚ K) * A * B)) ∧
      (span (𝓞 K) (Set.range fun i => (b i : MvPolynomial σ K))).restrictScalars ℤ =
        integralPart W := by
  refine ⟨hR ▸ Nat.mul_le_mul_left _ (finrank_le_one_add_pow hD), ?_⟩
  obtain ⟨b, hb⟩ := exists_basis_integralPart_sum_l2Norm_sq_le W hD S hSH hSW
    (fun P hP s => (l2Norm_le_l1Norm _).trans (hB P hP s)) ω hω hA hR
  have h2 : ∀ i (s : K →+* ℂ), l2Norm (map s (b i : MvPolynomial σ K)) ≤
      √((R + 3) / 4) * √(finrank ℚ K) * A * B := fun i s =>
    (Real.le_sqrt_of_sq_le (Finset.single_le_sum
      (f := fun s : K →+* ℂ => l2Norm (map s (b i : MvPolynomial σ K)) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ s))).trans (hb i)
  refine ⟨b, h2, fun i s => ?_, span_ringOfIntegers_basis_integralPart b⟩
  have hdeg : (map s (b i : MvPolynomial σ K)).totalDegree ≤ D :=
    Finset.sup_le fun α hα =>
      (le_totalDegree (support_map_subset s _ hα)).trans (hD _ (b i).2.1)
  refine (l1Norm_le_sqrt_choose_mul_l2Norm hdeg).trans
    (mul_le_mul ?_ (h2 i s) (l2Norm_nonneg _) (by positivity))
  rw [Real.sqrt_le_left (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_cancel₀,
    Real.rpow_natCast]
  exact_mod_cast choose_add_le_one_add_pow _ _
end GlobalTheory.MvPoly
