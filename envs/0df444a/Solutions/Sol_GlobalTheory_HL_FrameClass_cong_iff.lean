-- Prove2me | solution 1 for GlobalTheory.HL.FrameClass.cong_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:37:31.304903+00:00
-- url     : https://prove2.me/submissions/73e8bfd5-c11b-4f86-b467-135e0d11909d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameClass
theorem _root_.solution {n : ℕ} (t : E) (A A' : Matrix (Fin n) (Fin n) E) :
    (∀ i j, ∃ c ∈ L.O, A' i j - A i j = t * c) ↔ ∃ C, IsIntM L C ∧ A' - A = t • C := by
  constructor
  · intro h
    choose C hC hC' using h
    exact ⟨C, hC, by ext i j; exact hC' i j⟩
  · rintro ⟨C, hC, h⟩ i j
    exact ⟨C i j, hC i j, congrFun (congrFun h i) j⟩
end GlobalTheory.HL.FrameClass
