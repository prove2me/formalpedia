-- Prove2me | solution 1 for GlobalTheory.HermOrthBasis.orth_basis_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:47.330279+00:00
-- url     : https://prove2.me/submissions/c3631f53-7916-4b9b-8d04-699ac6a27864

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Theorems.Thm_GlobalTheory_HermOrthBasis_isCompl_perp
import Theorems.Thm_GlobalTheory_HermOrthBasis_le_of_gram
import Theorems.Thm_GlobalTheory_HermOrthBasis_exists_orth

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
open GlobalTheory GlobalTheory.HermOrthBasis
open Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HermOrthBasis
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → m ≤ n ∧ IsCompl (Submodule.span E (Set.range x)) (perp L Hm (Submodule.span E (Set.range x))) ∧ ∃ w : Fin (n - m) → Fin n → E, Submodule.span E (Set.range w) = perp L Hm (Submodule.span E (Set.range x)) ∧ (∀ i, IsUnit (hf L Hm (w i) (w i))) ∧ ∀ i j, i ≠ j → hf L Hm (w i) (w j) = 0 := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx
  have h := le_of_gram L Hm x hx
  exact ⟨h, isCompl_perp L Hm x hx, exists_orth L Hm hH _ m x hx (by omega)⟩
end GlobalTheory.HermOrthBasis
