-- Prove2me | solution 1 for GlobalTheory.RowLev.GroupAlgPos.eq_zero_of_coeff_mul_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:39:45.538016+00:00
-- url     : https://prove2.me/submissions/e72f6a11-9226-4c85-8357-573de3a1b63c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_coeff_mul_adj_one
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
theorem _root_.solution [Finite Q] (a : MonoidAlgebra ℂ Q) (h : (a * adj a).coeff 1 = 0) : a = 0 := by
  haveI := Fintype.ofFinite Q
  rw [coeff_mul_adj_one] at h
  ext q
  have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_star_self_nonneg (a.coeff x)).1 h q (Finset.mem_univ _)
  simpa using this
end GlobalTheory.RowLev.GroupAlgPos
