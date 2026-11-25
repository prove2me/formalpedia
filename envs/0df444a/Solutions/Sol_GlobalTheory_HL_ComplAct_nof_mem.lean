-- Prove2me | solution 1 for GlobalTheory.HL.ComplAct.nof_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:53:29.675235+00:00
-- url     : https://prove2.me/submissions/2db40c17-0029-43a6-8e72-d9b9d7568085

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Theorems.Thm_GlobalTheory_HL_ComplAct_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_ComplAct_spanTo_le_perp
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_le_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ComplAct
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.ComplAct
theorem _root_.solution {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) {n : S.GLV} (hn : n ∈ S.Nof g)
    {x : S.V} (hx : x ∈ S.spanTo g (r + 1)) : n x ∈ S.spanTo g (r + 1) := by
  have := spanTo_mono S g (hn.2.2 x (spanTo_le_perp S hg hx))
  simpa using Submodule.add_mem _ this hx
end GlobalTheory.HL.ComplAct
