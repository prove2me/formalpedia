-- Prove2me | solution 1 for GlobalTheory.MulUnramified.app_sub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:59:24.929797+00:00
-- url     : https://prove2.me/submissions/fe305980-6b30-4c8d-a4d2-a02091cf765a

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
theorem _root_.solution {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) (s : Γ(X, V)) :
    i.app W (f.appLE V W hf s - g.appLE V W hg s) = 0 := by
  rw [map_sub, sub_eq_zero, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr h]
end GlobalTheory.MulUnramified
