-- Prove2me | solution 1 for GlobalTheory.MulUnramified.comp_appLE_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:41.590273+00:00
-- url     : https://prove2.me/submissions/9e025ce1-a76c-4a31-b2da-cd42c2d39da7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Theorems.Thm_GlobalTheory_MulUnramified_appLE_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulUnramified
namespace GlobalTheory.MulUnramified
theorem _root_.solution {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X) {x : T ⟶ X} (h : a ≫ p = x)
    (V : X.Opens) (V' : P.Opens) (W : T.Opens) (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V')
    (h₃ : W ≤ x ⁻¹ᵁ V) (s : Γ(X, V)) :
    a.appLE V' W h₂ (p.appLE V V' h₁ s) = x.appLE V W h₃ s := by
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr h]
end GlobalTheory.MulUnramified
