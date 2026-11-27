-- Prove2me | solution 1 for GlobalTheory.tensorAddContent_eq_polyAddContent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:43:27.47063+00:00
-- url     : https://prove2.me/submissions/a2fdb672-4451-406a-bfa9-70e21b1bf49d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_tensorContent_eq_polyContent

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
open MvPolynomial Module
variable {R Γ ι κ σ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
variable {O M : Type*} [CommRing O] [Algebra O R] [AddCommGroup M] [Module O M] (b : Basis ι O M)
namespace GlobalTheory
theorem _root_.solution (x : MvPolynomial σ R ⊗[O] M) :
    tensorAddContent v b x = polyAddContent v (b.baseChange R) (tensorCoeffs x) :=
  tensorContent_eq_polyContent (AddValuation.toValuation v) b x
end GlobalTheory
