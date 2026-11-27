-- Prove2me | solution 1 for GlobalTheory.RowLev.GroupAlgPos.coeff_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:29:26.128844+00:00
-- url     : https://prove2.me/submissions/4b12b98f-2fc0-4692-ad23-9f4da486af12

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_coeff_mul_eq_sum
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.GroupAlgPos
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
variable {Q : Type} [Group Q]
namespace GlobalTheory.RowLev.GroupAlgPos
theorem _root_.solution [Fintype Q] (a : MonoidAlgebra ℂ Q) (h : a * a = a) (hs : IsSA a) (x y : Q) :
    a.coeff (x⁻¹ * y) = ∑ q, star (a.coeff (q⁻¹ * x)) * a.coeff (q⁻¹ * y) := by
  conv_lhs => rw [← h, coeff_mul_eq_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun q => ?_
  simp [hs q, mul_assoc]
end GlobalTheory.RowLev.GroupAlgPos
