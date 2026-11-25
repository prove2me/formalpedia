-- Prove2me | solution 1 for GlobalTheory.T.congruentOneMatrices_transitive_near_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:39:31.341263+00:00
-- url     : https://prove2.me/submissions/175c9b1d-e907-4367-89d6-0d56eb9fdf30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Theorems.Thm_GlobalTheory_CongTrans_congK_transitive


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsHerm L Γ → IsUnit Γ.det → ∀ i : ℕ, 1 ≤ i → ∃ j : ℕ, ∀ X ∈ horb L ϖ Γ i, ∀ D : Matrix (Fin m) (Fin m) E, IsHerm L D → IsIntM L D → ∃ A ∈ congK L ϖ m i, X + algebraMap F E ((ϖ : F) ^ j) • D = cT L A * X * A := by
  first | exact @GlobalTheory.CongTrans.congK_transitive | exact GlobalTheory.CongTrans.congK_transitive | (intros; apply GlobalTheory.CongTrans.congK_transitive <;> assumption)
end _root_.GlobalTheory.T
