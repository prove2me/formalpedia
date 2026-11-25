-- Prove2me | solution 1 for GlobalTheory.HL.encard_uniCosets_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:45.194587+00:00
-- url     : https://prove2.me/submissions/0847c583-45ed-4e7c-8ff0-15117d183987

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Theorems.Thm_GlobalTheory_HL_UniCount_encard_le
import Theorems.Thm_GlobalTheory_HL_UniCount_resQ_ne_zero
import Theorems.Thm_GlobalTheory_UnramCard_card_quot_eq_pow


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
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (δ : E), δ ∈ L.O → IsUnit δ → ∀ N : ℕ, ({C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, δ * u i j ∈ L.O) ∧ C = {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}}.encard : ℝ≥0∞) ≤ (resQ ϖ : ℝ≥0∞) ^ ((vE L ϖ (δ * L.cj δ)).toNat * (N * (N - 1) / 2)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ hu N
  have hc := (GlobalTheory.UnramCard.card_quot_eq_pow L ϖ hϖ ⟨δ, hδ⟩ hu).2
  have hfin : Finite (L.O ⧸ Ideal.span {(⟨δ, hδ⟩ : L.O)}) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (UniCount.resQ_ne_zero ϖ hϖ))
  have h := UniCount.encard_le L ⟨δ, hδ⟩ hu N
  rw [hc, ← pow_mul] at h
  have h2 := ENat.toENNReal_le.2 h
  rw [ENat.toENNReal_coe, Nat.cast_pow] at h2
  exact h2
end GlobalTheory.HL
