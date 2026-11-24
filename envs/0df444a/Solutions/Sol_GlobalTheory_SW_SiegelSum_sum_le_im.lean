-- Prove2me | solution 1 for GlobalTheory.SW.SiegelSum.sum_le_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:28:33.022297+00:00
-- url     : https://prove2.me/submissions/b9808a91-063c-4aa9-a208-6d8589b12c94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelSum
namespace GlobalTheory.SW.SiegelSum
theorem _root_.solution {ι : Type} [Fintype ι] {τ : Matrix ι ι ℂ} {c S : ℝ}
    (hc : ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (τ.map Complex.im *ᵥ x)) (ζ : ι → ℂ)
    (hS : ∀ i, |(ζ i).im| ≤ S) (v : ι → ℚ) :
    ∑ i, (c * (v i : ℝ) ^ 2 - 2 * S * |(v i : ℝ)|) ≤
      (qv v ⬝ᵥ τ *ᵥ qv v + 2 * (qv v ⬝ᵥ ζ)).im := by
  have h1 : (qv v ⬝ᵥ τ *ᵥ qv v).im =
      (fun i => (v i : ℝ)) ⬝ᵥ (τ.map Complex.im *ᵥ fun i => (v i : ℝ)) := by
    simp [dotProduct, mulVec, qv, Complex.im_sum, Complex.re_sum]
  have h2 : (2 * (qv v ⬝ᵥ ζ)).im = ∑ i, 2 * ((v i : ℝ) * (ζ i).im) := by
    simp [dotProduct, qv, Complex.im_sum, Finset.mul_sum]
  rw [Complex.add_im, h1, h2, Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  refine add_le_add (le_trans (le_of_eq ?_) (hc _)) (Finset.sum_le_sum fun i _ => ?_)
  · simp [dotProduct, Finset.mul_sum, sq]
  · have h3 := neg_abs_le ((v i : ℝ) * (ζ i).im)
    rw [abs_mul] at h3
    nlinarith [hS i, abs_nonneg (v i : ℝ)]
end GlobalTheory.SW.SiegelSum
