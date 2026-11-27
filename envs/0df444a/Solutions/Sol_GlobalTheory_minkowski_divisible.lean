-- Prove2me | solution 1 for GlobalTheory.minkowski_divisible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:24.735337+00:00
-- url     : https://prove2.me/submissions/5f026aed-5d36-441d-9c67-c5df965c7321

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MinkowskiDivisible
import Theorems.Thm_GlobalTheory_MinkDiv_add_case

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
namespace GlobalTheory
theorem _root_.solution : ∀ (Q : Type) [CommGroup Q] (l : ℕ) (u : Q ≃* Q) (r : ℕ), l.Prime → Odd l → 0 < r → (∀ x : Q, ∃ y : Q, y ^ l = x) → (∀ x, u^[r] x = x) → (∀ x, x ^ l = 1 → u x = x) → ∀ (x : Q) (a : ℕ), x ^ (l ^ a) = 1 → u x = x := by
  intro Q _ l u r hl ho hr hdiv hord hfix x a hx
  exact MinkDiv.add_case (A := Additive Q) l hl ho (fun x => hdiv x.toMul) r hr.ne'
    (MonoidHom.toAdditive u.toMonoidHom) (fun x _ _ => hord x.toMul) (fun x hx => hfix x.toMul hx)
    a (Additive.ofMul x) hx
end GlobalTheory
