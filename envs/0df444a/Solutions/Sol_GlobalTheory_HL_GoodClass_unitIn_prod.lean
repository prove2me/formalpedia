-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.unitIn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:21.398664+00:00
-- url     : https://prove2.me/submissions/5c05f82b-d097-4088-b3ba-b87646438017

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
import Theorems.Thm_GlobalTheory_HL_GoodClass_UpU_mul
import Theorems.Thm_GlobalTheory_HL_GoodClass_UnitIn_mul

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
theorem _root_.solution (O : Subring E) {ι : Type} (s : Finset ι) (g : ι → E) (h : ∀ i ∈ s, UnitIn O (g i)) :
    UnitIn O (∏ i ∈ s, g i) :=
  Finset.prod_induction g (UnitIn O) (fun _ _ => UnitIn.mul) ⟨O.one_mem, 1, O.one_mem, one_mul 1⟩ h
end GlobalTheory.HL.GoodClass
