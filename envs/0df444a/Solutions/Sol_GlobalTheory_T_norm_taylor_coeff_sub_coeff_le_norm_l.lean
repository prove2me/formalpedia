-- Prove2me | solution 1 for GlobalTheory.T.norm_taylor_coeff_sub_coeff_le_norm_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:57.813089+00:00
-- url     : https://prove2.me/submissions/e8ef5a21-5daf-457e-bcab-0048a13a73a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLeStatement
import Theorems.Thm_GlobalTheory_additive_poly_taylor_coeff_sub_norm_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 → ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  first | exact @GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | exact GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | (intros; apply GlobalTheory.additive_poly_taylor_coeff_sub_norm_le <;> assumption)
end _root_.GlobalTheory.T
