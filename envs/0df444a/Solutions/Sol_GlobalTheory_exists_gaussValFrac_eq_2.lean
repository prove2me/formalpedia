-- Prove2me | solution 2 for GlobalTheory.exists_gaussValFrac_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:26.121131+00:00
-- url     : https://prove2.me/submissions/47060da2-5268-4f72-903e-8e5d4c2adcdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_exists_gaussVal_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]
namespace GlobalTheory
theorem _root_.solution (x : F) : ∃ c : K, gaussValFrac v σ F x = v c := by
  obtain ⟨f, g, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) x
  obtain ⟨m, hm⟩ := exists_gaussVal_eq v f
  obtain ⟨n, hn⟩ := exists_gaussVal_eq v g
  exact ⟨coeff m f / coeff n g, by simp [hm, hn]⟩
end GlobalTheory
