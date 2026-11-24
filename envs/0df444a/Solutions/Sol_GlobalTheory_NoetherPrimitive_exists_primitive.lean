-- Prove2me | solution 1 for GlobalTheory.NoetherPrimitive.exists_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:50:12.768271+00:00
-- url     : https://prove2.me/submissions/efd90a2b-c527-474b-8cbc-084aae862a5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsPrimitiveElementDiscriminantMultiple
import Theorems.Thm_GlobalTheory_NoetherPrimitive_exists_primitive_element_discriminant_multiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherPrimitive
open Polynomial
open scoped nonZeroDivisors
namespace GlobalTheory.NoetherPrimitive
theorem _root_.solution (R A : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] :
    ∃ (a : A) (q : R), q ≠ 0 ∧ C q ∈ Ideal.span {minpoly R a, (minpoly R a).derivative} ∧
      ∀ b : A, ∃ r : R[X], algebraMap R A q * b = aeval a r := by
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)
  exact exists_primitive_element_discriminant_multiple R A (FractionRing R) (FractionRing A)
end GlobalTheory.NoetherPrimitive
