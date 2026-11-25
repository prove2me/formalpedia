-- Prove2me | solution 1 for GlobalTheory.HL.LevelRep.Good.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:45.693859+00:00
-- url     : https://prove2.me/submissions/f30fa703-d3da-4040-929e-4458591ec61e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentatives
import Theorems.Thm_GlobalTheory_HL_LevelRep_RR_add
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
theorem _root_.solution {j : ℕ} {b b' : S.V} (h : Good S g g' j b) (h' : Good S g g' j b') :
    Good S g g' j (b + b') := by
  obtain ⟨al, al', e, H⟩ := h
  obtain ⟨be, be', e', H'⟩ := h'
  refine ⟨fun i => al i + be i, fun i => al' i + be' i, ?_, fun i hi => RR_add S (H i hi) (H' i hi)⟩
  rw [e, e']
  simp only [add_smul, Finset.sum_add_distrib]
  abel
end Good
end GlobalTheory.HL.LevelRep
