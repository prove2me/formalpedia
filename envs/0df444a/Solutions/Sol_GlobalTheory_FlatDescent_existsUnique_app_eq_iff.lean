-- Prove2me | solution 1 for GlobalTheory.FlatDescent.existsUnique_app_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:28:19.886716+00:00
-- url     : https://prove2.me/submissions/db6c9441-1bef-4183-aad4-d0910a090c33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Theorems.Thm_GlobalTheory_FlatDescent_existsUnique_appTop_eq_iff
import Theorems.Thm_GlobalTheory_FlatDescent_isPullback_resLE
import Theorems.Thm_GlobalTheory_FlatDescent_appTop_resLE_apply
import Theorems.Thm_GlobalTheory_FlatDescent_appTop_morphismRestrict_apply
import Theorems.Thm_GlobalTheory_FlatDescent_effectiveEpi_morphismRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}
namespace GlobalTheory.FlatDescent
theorem _root_.solution (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens) (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U)
    (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) (s : Γ(Y, p ⁻¹ᵁ U)) :
    (∃! a : Γ(X, U), p.app U a = s) ↔ f.appLE _ W hf s = g.appLE _ W hg s := by
  have := effectiveEpi_morphismRestrict p U
  have hb : ∀ {T : Scheme.{u}} (V : T.Opens), Function.Bijective V.topIso.inv := fun V =>
    ConcreteCategory.bijective_of_isIso _
  rw [← (hb W).1.eq_iff, ← appTop_resLE_apply, ← appTop_resLE_apply,
    ← existsUnique_appTop_eq_iff (p ∣_ U) (isPullback_resLE h U W hW hf hg),
    ← (Equiv.ofBijective _ (hb U)).existsUnique_congr_right]
  simp only [Equiv.ofBijective_apply, appTop_morphismRestrict_apply, (hb _).1.eq_iff]
end GlobalTheory.FlatDescent
