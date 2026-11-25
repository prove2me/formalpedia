-- Prove2me | solution 1 for GlobalTheory.T.frames_commonStabiliser_eq_pairingMatrix_stabiliser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:08.470821+00:00
-- url     : https://prove2.me/submissions/a566ec25-4457-4188-b07e-377aaadb1f35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliserStatement
import Theorems.Thm_GlobalTheory_HL_FrameStab_stab_eq


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ h ∈ S.St, ∀ w ∈ S.W0, h w = w) ∧ ∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) → (cT L s * S.Zh * s' = S.Zh ↔ ∃ h ∈ S.St, (∀ j, h (S.f j) = ∑ i, s i j • S.f i) ∧ ∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) := by
  first | exact @GlobalTheory.HL.FrameStab.stab_eq | exact GlobalTheory.HL.FrameStab.stab_eq | (intros; apply GlobalTheory.HL.FrameStab.stab_eq <;> assumption)
end _root_.GlobalTheory.T
