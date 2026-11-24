-- Prove2me | solution 1 for GlobalTheory.FlatDescent.existsUnique_units_appTop_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:49.829923+00:00
-- url     : https://prove2.me/submissions/e23705cb-76a2-4286-b062-f1dd77d14cfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Theorems.Thm_GlobalTheory_FlatDescent_injective_appTop_of_epi
import Theorems.Thm_GlobalTheory_FlatDescent_exists_appTop_eq_of_effectiveEpi
import Theorems.Thm_GlobalTheory_FlatDescent_appTop_appTop_eq
import Theorems.Thm_GlobalTheory_FlatDescent_isUnit_appTop_iff

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
theorem _root_.solution (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)ˣ) :
    (∃! a : Γ(X, ⊤)ˣ, Units.map p.appTop.hom.toMonoidHom a = s) ↔
      Units.map f.appTop.hom.toMonoidHom s = Units.map g.appTop.hom.toMonoidHom s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact Units.ext (appTop_appTop_eq h.w a)
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s (congrArg Units.val hs)
    obtain ⟨a, rfl⟩ := (isUnit_appTop_iff p a).1 (ha ▸ s.isUnit)
    exact ⟨a, Units.ext ha, fun b hb => Units.ext <|
      injective_appTop_of_epi p ((congrArg Units.val hb).trans ha.symm)⟩
end GlobalTheory.FlatDescent
