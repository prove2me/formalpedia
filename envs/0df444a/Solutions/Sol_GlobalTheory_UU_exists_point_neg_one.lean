-- Prove2me | solution 1 for GlobalTheory.UU.exists_point_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:35:34.244773+00:00
-- url     : https://prove2.me/submissions/db8c01af-8c61-452f-8092-b072a8b664d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_NotExistsEvenTwistSymOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU
theorem _root_.solution : ∃ t : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ splitTorus (Spec (CommRingCat.of ℚ)) ℤ,
    t⁻¹ = t ∧ chV t 1 ≠ 1 := by
  let e := splitTorusPointsEquiv (Spec (CommRingCat.of ℚ)) ℤ (𝟙_ (Over (Spec (CommRingCat.of ℚ))))
  refine ⟨e.symm (zpowersHom _ (-1)), ?_, ?_⟩
  · apply e.injective
    rw [map_inv, MulEquiv.apply_symm_apply]
    ext
    simp
  · intro h1
    have h2 := congrArg Units.val h1
    simp [chV, e] at h2
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom.hom h2
    rw [map_neg, map_one] at h3
    norm_num at h3
end GlobalTheory.UU
