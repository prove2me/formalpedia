-- Prove2me | solution 1 for GlobalTheory.ChartRig.res_res_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:46.975128+00:00
-- url     : https://prove2.me/submissions/c8b86d3d-c917-4f25-92d1-0027c27d5627

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RigidifiedOfChart
import Theorems.Thm_GlobalTheory_ChartRig_res_pullU_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartRig
variable {X Y : Scheme.{0}}
namespace GlobalTheory.ChartRig
theorem _root_.solution (f : Y ⟶ X) (U : X.Opens) (V W : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ V)
    (x : Γ(X, U)ˣ) : res h' (res h (pullU f U x)) = res (h'.trans h) (pullU f U x) := by
  rw [res_pullU_eq, res_pullU_eq]
  ext
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom x = _
  rw [Scheme.Hom.appLE_map]
  rfl
end GlobalTheory.ChartRig
