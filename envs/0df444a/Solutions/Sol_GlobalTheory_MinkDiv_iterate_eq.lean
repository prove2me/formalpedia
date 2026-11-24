-- Prove2me | solution 1 for GlobalTheory.MinkDiv.iterate_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:18.072887+00:00
-- url     : https://prove2.me/submissions/46dcb445-cfad-4e0e-a823-94abe8ec01ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MinkowskiDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.MinkDiv
variable {A : Type} [AddCommGroup A]
namespace GlobalTheory.MinkDiv
theorem _root_.solution (f g : A →+ A) (hfg : ∀ z, f z = z + g z) (y : A) (hy : g (g (g y)) = 0)
    (n : ℕ) : f^[n] y = y + n • g y + (n.choose 2) • g (g y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add, map_add, map_nsmul, map_nsmul, hfg y,
      hfg (g y), hfg (g (g y)), hy, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    simp only [add_nsmul, smul_add, one_nsmul, add_zero]
    abel
end GlobalTheory.MinkDiv
