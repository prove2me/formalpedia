-- Prove2me | solution 1 for GlobalTheory.MulUnramified.appLE_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:50.961796+00:00
-- url     : https://prove2.me/submissions/69aa914a-ecb9-40fb-8c06-fe43dc6cd7b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN

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
theorem _root_.solution {T X : Scheme.{0}} {f g : T ⟶ X} (h : f = g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) : f.appLE V W hf = g.appLE V W hg := by
  subst h; rfl
end GlobalTheory.MulUnramified
