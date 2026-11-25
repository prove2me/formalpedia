-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.D1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:54:04.924025+00:00
-- url     : https://prove2.me/submissions/8d9b7b63-34d0-4a09-87dc-ef8f3a877d80

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable (M) (m : ℕ)
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution : (pair M m).Dm 1 = 1 := by
  simp [FPair.Dm, HermSp.Dl, HermSp.Zhat, pair, frame, h_vec, Matrix.det_fin_one]
end GlobalTheory.NonGenericLocalCheck
