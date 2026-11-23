-- Prove2me | solution 1 for GlobalTheory.MulUnramified.comp_mulN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:34.879792+00:00
-- url     : https://prove2.me/submissions/6acf58e7-545c-4da7-b21d-3c7c2327972f

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
variable {S : Scheme.{0}}
namespace GlobalTheory.MulUnramified
theorem _root_.solution (G : Over S) [GrpObj G] {T : Over S} (x : T ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [mulN, pow_succ, Hom.mul_def, ← ih, comp_lift_assoc, Category.comp_id]
end GlobalTheory.MulUnramified
