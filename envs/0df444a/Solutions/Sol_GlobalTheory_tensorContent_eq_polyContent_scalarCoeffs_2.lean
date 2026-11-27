-- Prove2me | solution 2 for GlobalTheory.tensorContent_eq_polyContent_scalarCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:22.659785+00:00
-- url     : https://prove2.me/submissions/e0cf4113-0851-4c33-96e4-cd335cf92799

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_polyContent_le_iff_coord

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
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module R N]
    (c : Basis ι R N) (x : MvPolynomial σ R ⊗[R] N) :
    tensorContent v c x = polyContent v c (scalarCoeffs x) := by
  have key : ∀ m i, c.repr (scalarCoeffs x m) i =
      coeff m ((c.baseChange (MvPolynomial σ R)).repr x i) := fun m i => by
    induction x with
    | zero => simp
    | tmul f y => simp [mul_comm]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz, coeff_add]
  refine eq_of_forall_ge_iff fun γ => ?_
  simp only [tensorContent, basisVal_le_iff, gaussVal_le_iff, polyContent_le_iff_coord, key]
  exact forall_comm
end GlobalTheory
