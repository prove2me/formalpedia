-- Prove2me | solution 1 for GlobalTheory.ker_includeRight_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:03.655881+00:00
-- url     : https://prove2.me/submissions/f81d60ba-7615-40fa-b909-b4bb3e189d04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_injective_lTensor_residueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
variable [Module.Flat A B]
namespace GlobalTheory
theorem _root_.solution (p : Ideal A) [p.IsPrime] :
    RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) =
      p.map (algebraMap A B) := by
  ext b
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff _ (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).injective,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
    ← map_eq_zero_iff _ (injective_lTensor_residueField (B := B) (M := B) p),
    ← map_eq_zero_iff _ (Algebra.TensorProduct.comm A p.ResidueField B).injective]
  simp
end GlobalTheory
