-- Prove2me | solution 1 for GlobalTheory.T.finite_of_valuation_bounded_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:19:19.087172+00:00
-- url     : https://prove2.me/submissions/fd89c34c-0059-4829-828f-308473275ee2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfValuationBoundedNormLeOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfValuationBoundedNormLeOneStatement
import Theorems.Thm_GlobalTheory_BCT_SuppFin_finite_of_valuation_bounded_of_norm_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (X : Set E), (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) → (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) → (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := by
  first | exact @GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one | exact GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one | (intros; apply GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one <;> assumption)
end _root_.GlobalTheory.T
