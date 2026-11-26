-- Prove2me | solution 1 for GlobalTheory.isoTransvection.zpow
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:28:20.493242+00:00
-- url     : https://prove2.me/submissions/e9ed52d1-b0a8-430c-b0cf-38e0b47302c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
theorem _root_.solution (b : R) (n : ℤ) :
    isoTransvection h x hx b ^ n = isoTransvection h x hx (n * b) := by
  have e := map_zpow (GlobalTheory.isoTransvectionHom h x hx) (Multiplicative.ofAdd b) n
  rw [← ofAdd_zsmul, zsmul_eq_mul] at e
  exact e.symm

