-- Prove2me | solution 1 for GlobalTheory.FrameAct.spanTo_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:05:28.970801+00:00
-- url     : https://prove2.me/submissions/34f39d33-42b5-4a3d-9b2e-132e58630640

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_GlobalTheory_FrameAct_spanTo_map
import Theorems.Thm_GlobalTheory_FrameAct_map_iff_of

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
    h v ∈ S.spanTo S.f J ↔ v ∈ S.spanTo S.f J := by
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  exact map_iff_of S (S.spanTo S.f J) S.N
    (fun h' hh' w hw => spanTo_map S S.f _ S.gram h' hh' J w hw) h hN v
end GlobalTheory.FrameAct
