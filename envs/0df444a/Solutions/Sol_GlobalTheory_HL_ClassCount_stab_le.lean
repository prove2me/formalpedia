-- Prove2me | solution 1 for GlobalTheory.HL.ClassCount.stab_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:21.202522+00:00
-- url     : https://prove2.me/submissions/d7874664-7ff1-4dab-8cb3-0cc3d083ce6b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumClsLeEncard
import Theorems.Thm_GlobalTheory_HL_ClassCount_smul_span
import Theorems.Thm_GlobalTheory_HL_ClassCount_span_le_of_mem
import Theorems.Thm_GlobalTheory_T_hermitianDoubleCosetFrameClass_properties


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ClassCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
  {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.ClassCount
theorem _root_.solution (g g' : Fin (r + 1) → S.V) :
    MulAction.stabilizer S.GLV (S.frameCls g g') ≤ stabL L (Submodule.span L.O (Set.range g)) := by
  intro h hh
  have h1 : h • S.frameCls g g' = S.frameCls g g' := hh
  rw [(GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).2.2 h] at h1
  change h • Submodule.span L.O (Set.range g) = _
  rw [smul_span]
  refine le_antisymm ?_ ?_
  · exact span_le_of_mem S (p := (_, _)) (h1 ▸ (GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).1)
  · exact span_le_of_mem S (p := (g, g')) (h1.symm ▸ (GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).1)
end GlobalTheory.HL.ClassCount
