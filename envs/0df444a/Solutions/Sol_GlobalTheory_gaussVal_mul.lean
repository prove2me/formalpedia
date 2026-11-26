-- Prove2me | solution 1 for GlobalTheory.gaussVal_mul
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:23:50.63997+00:00
-- url     : https://prove2.me/submissions/57c1e4a6-4721-4769-a69f-2e35e41193bb

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
variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)
theorem _root_.solution (f g : MvPolynomial σ R) :
    gaussVal v (f * g) = gaussVal v f * gaussVal v g := by
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
  trace "HIT_24_8"

end 
