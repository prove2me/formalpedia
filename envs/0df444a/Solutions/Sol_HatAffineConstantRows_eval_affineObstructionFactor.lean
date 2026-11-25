-- Prove2me | solution 1 for HatAffineConstantRows.eval_affineObstructionFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:22.194966+00:00
-- url     : https://prove2.me/submissions/6ada4b2a-ee97-4324-920a-122786562206

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_eval_linearForm
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
namespace HatAffineConstantRows
theorem _root_.solution
    {K : Type u} [Field K] {m : Nat} {I : Type v}
    (A : I → Fin m → K) (b x : I → K)
    (F : (Fin m → K) → I → K)
    (hrealize : AffineRealizes A b F)
    (y : Fin m → K) (i : I) :
    MvPolynomial.eval y (affineObstructionFactor A b x i) =
      F y i - x i := by
  calc
    MvPolynomial.eval y (affineObstructionFactor A b x i) =
        (∑ j, A i j * y j) + (b i - x i) := by
      simp [affineObstructionFactor, eval_linearForm]
    _ = F y i - x i := by
      rw [hrealize y i]
      ring
end HatAffineConstantRows
