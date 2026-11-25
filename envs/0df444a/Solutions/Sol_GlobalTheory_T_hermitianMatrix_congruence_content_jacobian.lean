-- Prove2me | solution 1 for GlobalTheory.T.hermitianMatrix_congruence_content_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:37:48.171082+00:00
-- url     : https://prove2.me/submissions/240fc439-a83a-4001-b626-5e14d5ecbeaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobian
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobianStatement
import Theorems.Thm_GlobalTheory_HL_HermJacobian_cont_congr


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) E), IsUnit A.det → (∀ X, X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X) ∧ ∀ B, IsCO (hermLat L m) B → IsCO (hermLat L m) ((fun X => cT L A * X * A) '' B) ∧ cont (hermLat L m) ((fun X => cT L A * X * A) '' B) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * m)) * cont (hermLat L m) B := by
  first | exact @GlobalTheory.HL.HermJacobian.cont_congr | exact GlobalTheory.HL.HermJacobian.cont_congr | (intros; apply GlobalTheory.HL.HermJacobian.cont_congr <;> assumption)
end _root_.GlobalTheory.T
