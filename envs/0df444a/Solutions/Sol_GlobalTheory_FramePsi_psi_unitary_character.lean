-- Prove2me | solution 1 for GlobalTheory.FramePsi.psi_unitary_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:49.597656+00:00
-- url     : https://prove2.me/submissions/6dc7a6bb-dec6-473c-8d31-8053dbfda389

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Theorems.Thm_GlobalTheory_FramePsi_coef_mul
import Theorems.Thm_GlobalTheory_FramePsi_norm_additiveCharacter_typePrime_eq_one
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FramePsi
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FramePsi
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ a ∈ S.N, ∀ b ∈ S.N, S.psi (a * b) = S.psi a * S.psi b) ∧ (∀ a ∈ S.N', ∀ b ∈ S.N', S.psi' (a * b) = S.psi' a * S.psi' b) ∧ (∀ a, ‖S.psi a‖ = 1 ∧ ‖S.psi' a‖ = 1) ∧ ∀ y : E, ‖L.psi0 y‖ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_,
    fun a => ⟨norm_additiveCharacter_typePrime_eq_one L _, norm_additiveCharacter_typePrime_eq_one L _⟩, norm_additiveCharacter_typePrime_eq_one L⟩
  · simp only [Frames.psi, Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f S.es _ S.gram S.dual a ha b hb]
  · simp only [Frames.psi', Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f' S.es' _ S.gram' S.dual' a ha b hb]
end GlobalTheory.FramePsi
