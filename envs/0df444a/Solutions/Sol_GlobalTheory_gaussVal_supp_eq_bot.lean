-- Prove2me | solution 1 for GlobalTheory.gaussVal_supp_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:48:38.406485+00:00
-- url     : https://prove2.me/submissions/003ad42d-accf-4c93-b688-512840bf086b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
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
variable [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀] (v : Valuation K Γ₀)
theorem _root_.solution : (gaussVal (σ := σ) v).supp = ⊥ := by
  first
    | (refine GlobalTheory.gaussVal_supp_eq_bot_of_supp v ?_
       rcases Ideal.eq_bot_or_top v.supp with h | h
       · exact h
       · have h1 : (1 : _) ∈ v.supp := h ▸ Submodule.mem_top
         rw [Valuation.mem_supp_iff, map_one] at h1
         exact absurd h1 one_ne_zero)

