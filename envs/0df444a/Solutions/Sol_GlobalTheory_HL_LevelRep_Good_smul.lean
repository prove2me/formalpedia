-- Prove2me | solution 1 for GlobalTheory.HL.LevelRep.Good.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:53:46.794165+00:00
-- url     : https://prove2.me/submissions/9c9b36af-cfe6-4382-a90e-3d917c949328

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentatives
import Theorems.Thm_GlobalTheory_HL_LevelRep_RR_mul
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LevelRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable {S} {g g' : Fin (r + 1) → S.V}
namespace GlobalTheory.HL.LevelRep
namespace Good
theorem _root_.solution {j : ℕ} {b : S.V} {a : E} (ha : a ∈ L.O) (h : Good S g g' j b) :
    Good S g g' j (a • b) := by
  obtain ⟨al, al', e, H⟩ := h
  refine ⟨fun i => a * al i, fun i => a * al' i, ?_, fun i hi => RR_mul S ha (H i hi)⟩
  rw [e]
  simp only [mul_smul, smul_add, Finset.smul_sum]
end Good
end GlobalTheory.HL.LevelRep
