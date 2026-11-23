-- Prove2me | solution 1 for GlobalTheory.injective_lTensor_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:08.770487+00:00
-- url     : https://prove2.me/submissions/4c749f35-e883-49b1-a056-4c4a8adc441e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul

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
namespace GlobalTheory
theorem _root_.solution (p : Ideal A) [p.IsPrime] :
    Function.Injective (AlgebraTensorModule.lTensor B M
      (IsScalarTower.toAlgHom A (A ⧸ p) p.ResidueField).toLinearMap) :=
  Module.Flat.lTensor_preserves_injective_linearMap _
    (IsFractionRing.injective (A ⧸ p) p.ResidueField)
end GlobalTheory
