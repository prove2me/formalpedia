-- Prove2me | solution 1 for GlobalTheory.exists_gaussAddVal_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:47:13.211148+00:00
-- url     : https://prove2.me/submissions/f9f3facf-14ab-4ee3-a08f-584b9bd32a16

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
variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)

theorem solution (f : MvPolynomial σ R) : ∃ m, gaussAddVal v f = v (coeff m f) := by
  by_cases hf : f = 0
  · refine ⟨0, ?_⟩
    simp [hf, AddValuation.map_zero]
  · have hc : AddMonoidAlgebra.coeff f ≠ 0 :=
      AddMonoidAlgebra.coeff_eq_zero.not.mpr hf
    obtain ⟨m, -, hm⟩ :=
      exists_mem_support_coeffSup_eq (N := AddValuation.toValuation v) hc
    refine ⟨m, ?_⟩
    have hmul :
        gaussVal (AddValuation.toValuation v) f =
          AddValuation.toValuation v (coeff m f) := by
      simpa [gaussVal, gaussValAlg, MvPolynomial.coeff] using hm
    rw [gaussAddVal, AddValuation.ofValuation_apply, hmul, ← AddValuation.ofValuation_apply,
      AddValuation.ofValuation_toValuation]
