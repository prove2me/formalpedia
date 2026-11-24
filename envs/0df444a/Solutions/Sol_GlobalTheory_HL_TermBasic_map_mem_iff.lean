-- Prove2me | solution 1 for GlobalTheory.HL.TermBasic.map_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:41.262047+00:00
-- url     : https://prove2.me/submissions/30b69aa3-ce10-47f2-bdfd-6ad3d89a28e1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Theorems.Thm_GlobalTheory_HL_TermBasic_map_mem

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TermBasic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable {S} {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
include hg
namespace GlobalTheory.HL.TermBasic
theorem _root_.solution {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) (x : S.V) :
    n x ∈ S.spanTo g j ↔ x ∈ S.spanTo g j := by
  refine ⟨fun h => ?_, map_mem hg hn j⟩
  have := map_mem hg ((S.Nof g).inv_mem hn) j h
  have e : n⁻¹ (n x) = x := n.symm_apply_apply x
  rwa [e] at this
end GlobalTheory.HL.TermBasic
