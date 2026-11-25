-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.gramT_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:29.747809+00:00
-- url     : https://prove2.me/submissions/0bc129eb-4c8c-4e6a-9ef0-2d445836aeaf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Theorems.Thm_GlobalTheory_HL_ContModel_gramT_rmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
open ValuativeRel
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.ContModel
namespace _root_.GlobalTheory.HL.ContModel
theorem _root_.solution (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (ϖ : 𝒪[F]) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (Ω : Set (Fin m → Fin n → E)) (Γ : Matrix (Fin m) (Fin m) E)
    (i : ℕ) (hΩ : ∀ y ∈ Ω, _root_.GlobalTheory.HL.gramT L Hm y = Γ) :
    ∀ x ∈ _root_.GlobalTheory.HL.thick L ϖ Ω i,
      _root_.GlobalTheory.HL.gramT L Hm x ∈ _root_.GlobalTheory.HL.horb L ϖ Γ i := by
  rintro x ⟨y, hy, A, hA, rfl⟩
  exact ⟨A, hA, by rw [_root_.GlobalTheory.HL.ContModel.gramT_rmul, hΩ y hy]⟩
end _root_.GlobalTheory.HL.ContModel
end GlobalTheory.HL.ContModel
