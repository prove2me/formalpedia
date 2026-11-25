-- Prove2me | solution 1 for GlobalTheory.T.hermitianDoubleCosetFrameClass_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:08.903827+00:00
-- url     : https://prove2.me/submissions/b3656e02-fa22-4293-bdc8-d6f07858f37d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassPropertiesStatement
import Theorems.Thm_GlobalTheory_HL_FrameClass_frame_classes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g g' : Fin (r + 1) → S.V, (g, g') ∈ S.frameCls g g' ∧ (∀ p ∈ S.frameCls g g', S.frameCls p.1 p.2 = S.frameCls g g' ∧ S.Mof p.1 p.2 = S.Mof g g') ∧ ∀ h : S.GLV, h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  first | exact @GlobalTheory.HL.FrameClass.frame_classes | exact GlobalTheory.HL.FrameClass.frame_classes | (intros; apply GlobalTheory.HL.FrameClass.frame_classes <;> assumption)
end _root_.GlobalTheory.T
