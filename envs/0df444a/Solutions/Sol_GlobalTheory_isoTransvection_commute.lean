-- Prove2me | solution 1 for GlobalTheory.isoTransvection.commute
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:28:21.130396+00:00
-- url     : https://prove2.me/submissions/32093b91-69e4-4e59-9cf6-492aeecb2d9a

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
theorem _root_.solution (b b' : R) :
    Commute (isoTransvection h x hx b) (isoTransvection h x hx b') := by
  exact (Commute.all (Multiplicative.ofAdd b) (Multiplicative.ofAdd b')).map (GlobalTheory.isoTransvectionHom h x hx)

