-- Prove2me | solution 1 for GlobalTheory.tensorContent_tmul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:48:21.744242+00:00
-- url     : https://prove2.me/submissions/3453b53b-4be1-42bf-b2f1-f395744eab1b

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

theorem solution (f : MvPolynomial σ R) (y : M) :
    tensorContent v b (f ⊗ₜ y) = gaussVal v f * basisVal (v.comap (algebraMap O R)) b y := by
  unfold tensorContent basisVal
  refine coeffSup_eq_mul_of_forall (N := v.comap (algebraMap O R)) (N' := gaussVal v)
      (v.comap (algebraMap O R)).map_zero (gaussVal v).map_zero fun i => ?_
  rw [Basis.baseChange_repr_tmul]
  -- gaussVal (r • f) = v (algebraMap O R r) * gaussVal f
  have : b.repr y i • f = C (algebraMap O R (b.repr y i)) * f := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O R (MvPolynomial σ R),
      MvPolynomial.algebraMap_eq]
  rw [this, map_mul, gaussVal_C, mul_comm]
  rfl
