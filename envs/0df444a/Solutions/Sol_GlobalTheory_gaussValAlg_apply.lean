-- Prove2me | solution 1 for GlobalTheory.gaussValAlg_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:23:53.042061+00:00
-- url     : https://prove2.me/submissions/e60dbd1c-1677-4843-90f2-ef6555d0b8f4

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
variable {R G Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
variable [AddMonoid G] [UniqueSums G]
theorem _root_.solution (f : AddMonoidAlgebra R G) :
    gaussValAlg v f = f.coeff.support.sup fun m => v (f.coeff m) := by
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
  trace "HIT_24_16"

end 
