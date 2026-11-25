-- Prove2me | solution 1 for GlobalTheory.HL.ComplAct.spanTo_le_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:40.992706+00:00
-- url     : https://prove2.me/submissions/b0f7020d-f079-4b4b-a57e-2269c6ffb4e2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_StdLat_image_lt
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_perp_span
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
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) :
    S.spanTo g (r + 1) ≤ perp L S.Hm (S.spanTo g r) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, -, rfl⟩
  rw [Frames.spanTo, image_lt, SetLike.mem_coe, mem_perp_span]
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro j; simp [S.gram, Fin.castSucc_ne_last]
  · intro j; simp [S.gram', Fin.castSucc_ne_last]
end GlobalTheory.HL.ComplAct
