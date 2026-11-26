-- Prove2me | solution 1 for GlobalTheory.gaussAddVal_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:23:51.479691+00:00
-- url     : https://prove2.me/submissions/128f21d5-cd59-4697-9cc2-ae52b2795684

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Mathlib


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
theorem _root_.solution (f : MvPolynomial σ R) :
    gaussAddVal v f = f.support.inf fun m => v (coeff m f) := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_24_12"

end 
