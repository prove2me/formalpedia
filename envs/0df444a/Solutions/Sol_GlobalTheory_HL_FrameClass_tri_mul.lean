-- Prove2me | solution 1 for GlobalTheory.HL.FrameClass.tri_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:35:24.888113+00:00
-- url     : https://prove2.me/submissions/9e62cd52-545a-4433-9fa3-eb5230d244a1

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
omit [TopologicalSpace E]
namespace GlobalTheory.HL.FrameClass
theorem _root_.solution {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : ∀ i j, j < i → (A * B) i j = 0 := fun i j h => by
  have hA' : A.BlockTriangular id := fun i j h => hA i j h
  have hB' : B.BlockTriangular id := fun i j h => hB i j h
  exact hA'.mul hB' h
end GlobalTheory.HL.FrameClass
