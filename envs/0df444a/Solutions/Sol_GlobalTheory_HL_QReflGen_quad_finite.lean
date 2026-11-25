-- Prove2me | solution 1 for GlobalTheory.HL.QReflGen.quad_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:39:50.457719+00:00
-- url     : https://prove2.me/submissions/72aace4f-bbc6-46d8-a7de-87dc4c35b448

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosure
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QReflGen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.QReflGen
theorem _root_.solution {K : Type} [Field K] (a b c : K) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    {r : K | a * r ^ 2 + b * r + c = 0}.Finite := by
  have hp : (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ≠ 0 := by
    intro h0
    apply h
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrArg (fun p => Polynomial.coeff p 2) h0
    · simpa using congrArg (fun p => Polynomial.coeff p 1) h0
    · simpa using congrArg (fun p => Polynomial.coeff p 0) h0
  have := Polynomial.finite_setOf_isRoot hp
  simpa [Polynomial.IsRoot] using this
end GlobalTheory.HL.QReflGen
