-- Prove2me | solution 1 for GlobalTheory.RowLev.GroupAlgPos.isSA_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:35:57.943676+00:00
-- url     : https://prove2.me/submissions/1853152b-3c73-4b1c-bbbb-760de24c077b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_adj_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.GroupAlgPos
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
variable {Q : Type} [Group Q]
namespace GlobalTheory.RowLev.GroupAlgPos
theorem _root_.solution [Finite Q] (a : MonoidAlgebra ℂ Q) : IsSA a ↔ adj a = a := by
  constructor
  · intro h
    ext q
    rw [adj_coeff, h q, star_star]
  · intro h q
    have := adj_coeff a q⁻¹
    rw [h, inv_inv] at this
    exact this
end GlobalTheory.RowLev.GroupAlgPos
