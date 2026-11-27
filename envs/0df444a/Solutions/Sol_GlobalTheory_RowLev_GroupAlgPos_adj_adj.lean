-- Prove2me | solution 1 for GlobalTheory.RowLev.GroupAlgPos.adj_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:29:18.9521+00:00
-- url     : https://prove2.me/submissions/1788c5f0-7fae-46a7-972c-cb19c5c2f599

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_adj_coeff
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
theorem _root_.solution [Finite Q] (a : MonoidAlgebra ℂ Q) : adj (adj a) = a := by
  ext q; simp [adj_coeff]
end GlobalTheory.RowLev.GroupAlgPos
