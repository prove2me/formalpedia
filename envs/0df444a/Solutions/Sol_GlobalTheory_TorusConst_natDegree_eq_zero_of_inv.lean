-- Prove2me | solution 1 for GlobalTheory.TorusConst.natDegree_eq_zero_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:33:51.227685+00:00
-- url     : https://prove2.me/submissions/e57d20c7-dd72-4adf-b340-c05b7fad4f92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
namespace GlobalTheory.TorusConst
theorem _root_.solution {F : Type} [Field F] (a b : F[X])
    (h : algebraMap F[X] (FractionRing F[X]) a =
      eval₂ (algebraMap F (FractionRing F[X])) (algebraMap F[X] (FractionRing F[X]) X)⁻¹ b) :
    a.natDegree = 0 := by
  set x := algebraMap F[X] (FractionRing F[X]) X with hxd
  have hx : x ≠ 0 := fun h0 => X_ne_zero (IsFractionRing.injective F[X] (FractionRing F[X])
    (h0.trans (map_zero _).symm))
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h1 := eval₂_reflect_mul_pow (algebraMap F (FractionRing F[X])) x⁻¹ b.natDegree b le_rfl
  rw [invOf_eq_inv, inv_inv, ← h] at h1
  have h2 : ∀ p : F[X], eval₂ (algebraMap F (FractionRing F[X])) x p =
      algebraMap F[X] (FractionRing F[X]) p := fun p => by
    rw [← aeval_def, hxd, aeval_algebraMap_apply, aeval_X_left_apply]
  have h3 : reflect b.natDegree b = a * X ^ b.natDegree := by
    apply IsFractionRing.injective F[X] (FractionRing F[X])
    rw [map_mul, map_pow, ← h1, h2, ← hxd, _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hx, one_pow, _root_.mul_one]
  by_cases ha : a = 0
  · simp [ha]
  have h4 : (reflect b.natDegree b).natDegree ≤ b.natDegree := natDegree_reflect_le.trans (by simp)
  rw [h3, natDegree_mul_X_pow _ ha] at h4
  omega
end GlobalTheory.TorusConst
