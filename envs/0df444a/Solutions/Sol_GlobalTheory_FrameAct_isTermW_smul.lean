-- Prove2me | solution 1 for GlobalTheory.FrameAct.isTermW_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:55.876846+00:00
-- url     : https://prove2.me/submissions/6653f5fb-4551-429f-a333-02f30ba3bd89

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_GlobalTheory_FrameAct_inTh_iff
import Theorems.Thm_GlobalTheory_FrameAct_graph_smul

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
open GlobalTheory GlobalTheory.FrameAct
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FrameAct
theorem _root_.solution (h : S.GLV) (hh : h ∈ S.St) (d : S.Datum) (Λ : Submodule L.O S.V)
    (n n' : S.GLV) (H : S.IsTermW d Λ n n') : S.IsTermW d (h • Λ) (h * n) (h * n') := by
  obtain ⟨i1, i2, hn, hn', e1, e2, hb, hg⟩ := H
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  have hN' : h ∈ S.N' := (Subgroup.mem_inf.mp hh).2
  refine ⟨i1, i2, S.N.mul_mem hN hn, S.N'.mul_mem hN' hn', ?_, ?_, ?_, ?_⟩
  · rw [e1, mul_smul]
  · rw [e2, mul_smul]
  · intro b
    have h4 := (inTh_iff S h Λ _).2 (hb b)
    rw [map_sub] at h4
    exact h4
  · rw [hg, graph_smul S h hh Λ]
end GlobalTheory.FrameAct
