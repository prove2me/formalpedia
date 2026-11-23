-- Prove2me | solution 1 for GlobalTheory.FlatDescent.appTop_morphismRestrict_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:33.367167+00:00
-- url     : https://prove2.me/submissions/52657fc1-a4f2-4893-8ba6-33fee6c6889c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Theorems.Thm_GlobalTheory_FlatDescent_appTop_resLE_apply

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
theorem _root_.solution (p : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    (p ∣_ U).appTop (U.topIso.inv a) = (p ⁻¹ᵁ U).topIso.inv (p.app U a) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, appTop_resLE_apply, Scheme.Hom.appLE_eq_app]
end GlobalTheory.FlatDescent
