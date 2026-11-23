-- Prove2me | solution 1 for GlobalTheory.CoverOpCompat.push_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:20.288162+00:00
-- url     : https://prove2.me/submissions/e9811475-05e1-4cae-8b87-ebb3ff6a610a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GroupLawsOnCoverAgreeOnCommonPoints

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverOpCompat
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
namespace GlobalTheory.CoverOpCompat
theorem _root_.solution (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p q : Over.mk ρ ⟶ G') (x y : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) (hy : y.left = q.left ≫ φ) :
    (x * y).left = (p * q).left ≫ φ := by
  subst e
  exact h.2 (Over.mk ρ) p q x y hx hy
end GlobalTheory.CoverOpCompat
