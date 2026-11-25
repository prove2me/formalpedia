-- Prove2me | solution 1 for GlobalTheory.HL.Defect.gram_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:21.436218+00:00
-- url     : https://prove2.me/submissions/e4596bf9-17ca-4c29-9775-a43d9a2cfa31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Theorems.Thm_GlobalTheory_HL_Defect_hf_comb
import Theorems.Thm_GlobalTheory_HL_Defect_hf_comb_r
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Defect
theorem _root_.solution (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    (e e' b b' : ι → Fin n → E) (P P' : Matrix ι ι E) (hb : ∀ i, b i = ∑ k, P k i • e k)
    (hb' : ∀ i, b' i = ∑ k, P' k i • e' k) :
    (Matrix.of fun i j => hf L Hm (b i) (b' j)) =
      Pᵀ * (Matrix.of fun i j => hf L Hm (e i) (e' j)) * P'.map L.cj := by
  ext i j
  simp only [Matrix.of_apply, hb, hb', hf_comb_r, hf_comb, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end GlobalTheory.HL.Defect
