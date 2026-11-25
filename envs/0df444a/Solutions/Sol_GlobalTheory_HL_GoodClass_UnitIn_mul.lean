-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.UnitIn.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:25:04.881473+00:00
-- url     : https://prove2.me/submissions/89fb8df9-836a-469e-86d3-62b8c8b419ee

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
open GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]
namespace GlobalTheory.HL.GoodClass
namespace UnitIn
theorem _root_.solution {O : Subring E} {x y : E} (hx : UnitIn O x) (hy : UnitIn O y) : UnitIn O (x * y) := by
  obtain ⟨h1, a, ha, ha1⟩ := hx
  obtain ⟨h2, b, hb, hb1⟩ := hy
  exact ⟨O.mul_mem h1 h2, a * b, O.mul_mem ha hb, by linear_combination (y * b) * ha1 + hb1⟩
end UnitIn
end GlobalTheory.HL.GoodClass
