-- Prove2me | solution 1 for GlobalTheory.tensorContent_add_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:50:41.195563+00:00
-- url     : https://prove2.me/submissions/336c9fc9-91ea-4304-8ecb-f38a014e4dfc

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
open MvPolynomial Module
variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)

theorem solution (x y : MvPolynomial σ R ⊗[O] M) :
    tensorContent v b (x + y) ≤ max (tensorContent v b x) (tensorContent v b y) := by
  unfold tensorContent
  rw [basisVal_le_iff]
  intro i
  rw [map_add]
  refine ((gaussVal v).map_add _ _).trans ?_
  exact max_le_max ((basisVal_le_iff (gaussVal v) _).mp le_rfl i)
    ((basisVal_le_iff (gaussVal v) _).mp le_rfl i)
