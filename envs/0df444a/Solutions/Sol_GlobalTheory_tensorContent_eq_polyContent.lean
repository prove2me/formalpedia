-- Prove2me | solution 1 for GlobalTheory.tensorContent_eq_polyContent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:52.896976+00:00
-- url     : https://prove2.me/submissions/05b6200f-ee3e-4d09-81dd-d074d13cc7d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_polyContent_le_iff_coord
import Theorems.Thm_GlobalTheory_repr_tensorCoeffs

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
variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)
namespace GlobalTheory
theorem _root_.solution (x : MvPolynomial σ R ⊗[O] M) :
    tensorContent v b x = polyContent v (b.baseChange R) (tensorCoeffs x) :=
  eq_of_forall_ge_iff fun γ => by
    simp only [tensorContent, basisVal_le_iff, gaussVal_le_iff, polyContent_le_iff_coord,
      repr_tensorCoeffs]
    exact forall_comm
end GlobalTheory
