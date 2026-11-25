-- Prove2me | solution 1 for GlobalTheory.HL.TraceRep.frame_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:37.313366+00:00
-- url     : https://prove2.me/submissions/9517c51e-088c-4fcf-9737-2d5e44b55b23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDefectClassMemTraceFirstFrameSpan
import Theorems.Thm_GlobalTheory_HL_TraceRep_hf_add
import Theorems.Thm_GlobalTheory_HL_TraceRep_hf_smul
import Theorems.Thm_GlobalTheory_HL_TraceRep_hf_zero
import Theorems.Thm_GlobalTheory_HL_TraceRep_hf_swap_zero
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TraceRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E}
variable {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.TraceRep
theorem _root_.solution (g : Fin (r + 1) → S.V) (T : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then T else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (b : Fin (r + 1)) :
    n (g b) ∈ perp L S.Hm (S.spanTo g r) := by
  refine (hn.2.1 (g b)).2 ?_
  intro y hy
  apply hf_swap_zero S.herm.1
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [hg, if_neg]
    rintro ⟨rfl, -⟩
    simp at hi
  | zero => exact hf_zero _ _
  | add a c _ _ ha hc => rw [hf_add, ha, hc, add_zero]
  | smul c a _ ha => rw [hf_smul, ha, mul_zero]
end GlobalTheory.HL.TraceRep
