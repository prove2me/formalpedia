-- Prove2me | solution 1 for GlobalTheory.FrameAct.sup_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:21:16.030674+00:00
-- url     : https://prove2.me/submissions/00ad94c3-e6a8-403f-9da5-c7392cdc3c1b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_GlobalTheory_FrameAct_map_iff_of
import Theorems.Thm_GlobalTheory_FrameAct_spanTo_iff
import Theorems.Thm_P2M_GlobalTheory_FrameAct_spanTo_iff__721488b8eec6

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
theorem _root_.solution (h : S.GLV) (hh : h ∈ S.St) (J : ℕ) (v : S.V) :
    h v ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J ↔ v ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J := by
  have hS : ∀ h' ∈ S.St, ∀ w ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J,
      h' w ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J := by
    intro h' hh' w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    exact Submodule.add_mem_sup ((spanTo_iff S h' hh' J a).2 ha) ((spanTo_iff' S h' hh' J b).2 hb)
  exact map_iff_of S _ S.St hS h hh v
end GlobalTheory.FrameAct
