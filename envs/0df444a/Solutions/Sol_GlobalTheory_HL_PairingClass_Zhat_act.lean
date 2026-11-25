-- Prove2me | solution 1 for GlobalTheory.HL.PairingClass.Zhat_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:51.75616+00:00
-- url     : https://prove2.me/submissions/f5983b2d-b381-40e6-ad8c-8ba428e91796

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverRelationUniqueness
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_CoordExist_h_sum_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PairingClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
namespace GlobalTheory.HL.PairingClass
theorem _root_.solution (H : HermSp M V) (f f' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    H.Zhat (act f A) (act f' A') = cT M.L A * H.Zhat f f' * A' := by
  ext a b
  simp only [HermSp.Zhat, act, Matrix.of_apply, Matrix.mul_apply, cT, CoordExist.h_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [H.h_herm, CoordExist.h_sum_left, map_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← H.h_herm]
end GlobalTheory.HL.PairingClass
