-- Prove2me | solution 1 for GlobalTheory.T.normalisedContent_thickenedSet_independent_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:27.669087+00:00
-- url     : https://prove2.me/submissions/4811eae7-c8ab-4b6a-96db-1a0c7892dce8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalisedContentThickenedSetIndependentOfLevel
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalisedContentThickenedSetIndependentOfLevelStatement
import Theorems.Thm_GlobalTheory_CardQuotientPow_main
import Theorems.Thm_GlobalTheory_QuotientCardinality_main
import Theorems.Thm_GlobalTheory_ThickLevel_main


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsHerm L Γ → IsUnit Γ.det → ∀ (Ω : Set (Fin m → Fin n → E)), (∀ y ∈ Ω, gramT L Hm y = Γ) → ∀ i i' : ℕ, 1 ≤ i → i ≤ i' → (∀ y ∈ Ω, ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → rmul y A ∈ Ω) → IsCO (tupLat L Λs m) (thick L ϖ Ω i') → cont (tupLat L Λs m) (thick L ϖ Ω i) * cont (hermLat L m) (horb L ϖ Γ i') = cont (tupLat L Λs m) (thick L ϖ Ω i') * cont (hermLat L m) (horb L ϖ Γ i) := by
  first | exact @GlobalTheory.ThickLevel.main | exact GlobalTheory.ThickLevel.main | (intros; apply GlobalTheory.ThickLevel.main <;> assumption)
end _root_.GlobalTheory.T
