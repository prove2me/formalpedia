-- Prove2me | solution 1 for GlobalTheory.isoTransvectionHom_ofAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:44.522797+00:00
-- url     : https://prove2.me/submissions/8f4aaeab-cb41-47fc-b960-d7514d50abda

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
namespace GlobalTheory
theorem _root_.solution (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) :
    isoTransvectionHom h x hx (Multiplicative.ofAdd b) = isoTransvection h x hx b := rfl
end GlobalTheory
