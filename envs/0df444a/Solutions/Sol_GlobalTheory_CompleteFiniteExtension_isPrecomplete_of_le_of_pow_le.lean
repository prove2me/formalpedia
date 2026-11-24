-- Prove2me | solution 1 for GlobalTheory.CompleteFiniteExtension.isPrecomplete_of_le_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:11.301693+00:00
-- url     : https://prove2.me/submissions/e3ab5343-a318-46e2-96d2-2f6828f586d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPrecompleteOfLeOfPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Theorems.Thm_GlobalTheory_PrecompleteOfPowLe_isPrecomplete_of_le_of_pow_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.CompleteFiniteExtension
open IsLocalRing
namespace GlobalTheory.CompleteFiniteExtension
theorem _root_.solution {A : Type*} [CommRing A] {I J : Ideal A} (hJ : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A := by
  first
  | (rename_i h_1 h_7; revert A h_1 I J hJ e he h_7; exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le)
  | exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | (apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le ..)
end GlobalTheory.CompleteFiniteExtension
