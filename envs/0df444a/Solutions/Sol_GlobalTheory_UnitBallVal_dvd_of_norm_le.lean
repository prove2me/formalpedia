-- Prove2me | solution 1 for GlobalTheory.UnitBallVal.dvd_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:41.36053+00:00
-- url     : https://prove2.me/submissions/00615b78-5f04-4098-bddb-f74bb20a161e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImportsBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.UnitBallVal
namespace GlobalTheory.UnitBallVal
theorem _root_.solution {C O : Type} [NormedField C] [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C))
    (hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x) {a b : O}
    (h : ‖algebraMap O C b‖ ≤ ‖algebraMap O C a‖) : a ∣ b := by
  by_cases ha : algebraMap O C a = 0
  · have hb : algebraMap O C b = 0 := by
      rw [ha, norm_zero] at h
      exact norm_le_zero_iff.mp h
    have hb0 : b = 0 := hinj (by rw [hb, map_zero])
    rw [hb0]
    exact dvd_zero a
  · obtain ⟨y, hy⟩ := hsurj (algebraMap O C b / algebraMap O C a) (by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr ha)).mpr h)
    refine ⟨y, hinj ?_⟩
    rw [map_mul, hy]
    field_simp
end GlobalTheory.UnitBallVal
