-- Prove2me | solution 1 for GlobalTheory.tensorContent_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:53:47.110895+00:00
-- url     : https://prove2.me/submissions/dea00001-8b1d-4857-9c6c-4012517baa28

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

theorem solution (hv : v.supp = ⊥) {x : MvPolynomial σ R ⊗[O] M} :
    tensorContent v b x = 0 ↔ x = 0 := by
  unfold tensorContent
  constructor
  · intro h
    have hi : ∀ i, (b.baseChange (MvPolynomial σ R)).repr x i = 0 := by
      intro i
      have : gaussVal v ((b.baseChange (MvPolynomial σ R)).repr x i) = 0 := by
        rw [basisVal, coeffSup_eq_zero_iff (gaussVal v).map_zero] at h
        exact h i
      rw [gaussVal_eq_zero_iff_forall] at this
      ext m
      have hm : v (coeff m ((b.baseChange (MvPolynomial σ R)).repr x i)) = 0 := this m
      rwa [← Valuation.mem_supp_iff, hv, Ideal.mem_bot] at hm
    exact (b.baseChange (MvPolynomial σ R)).repr.map_eq_zero_iff.mp (Finsupp.ext hi)
  · intro hx
    subst hx
    exact basisVal_zero _ _
