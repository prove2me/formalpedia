-- Prove2me | solution 1 for GlobalTheory.NoetherPrimitive.exists_common_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:31.306937+00:00
-- url     : https://prove2.me/submissions/d8888192-8e3b-429f-8954-d07d19c6656b

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsPrimitiveElementDiscriminantMultiple
import Theorems.Thm_GlobalTheory_CommonDenominatorForFinset_exists_common_denominator


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
theorem _root_.solution {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] (a : A)
    (h : ∀ b : A, ∃ s : R, s ≠ 0 ∧ ∃ r : R[X], algebraMap R A s * b = aeval a r) :
    ∃ s : R, s ≠ 0 ∧ ∀ b : A, ∃ r : R[X], algebraMap R A s * b = aeval a r := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator ..)
end GlobalTheory.NoetherPrimitive
