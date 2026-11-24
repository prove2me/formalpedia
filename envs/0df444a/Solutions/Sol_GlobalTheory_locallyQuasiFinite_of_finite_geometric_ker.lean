-- Prove2me | solution 1 for GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:09.574842+00:00
-- url     : https://prove2.me/submissions/4f13b865-8c4e-4ecb-b163-b6d1cafd197e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints
import Theorems.Thm_GlobalTheory_locallyQuasiFinite_of_finite_geometric_points
import Theorems.Thm_GlobalTheory_finite_fiber_of_finite_ker

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      LocallyOfFiniteType p.left → QuasiCompact p.left →
      (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S),
        Finite {x : Over.mk t ⟶ Ga // x ≫ p = 1}) → LocallyQuasiFinite p.left := by
  intro S Ga G _ _ p hp hft _ h
  refine locallyQuasiFinite_of_finite_geometric_points p.left fun Ω _ _ y ↦ ?_
  let y' : Over.mk (y ≫ G.hom) ⟶ G := Over.homMk y rfl
  have := finite_fiber_of_finite_ker p (h Ω (y ≫ G.hom)) y'
  refine Finite.of_injective (β := {x : Over.mk (y ≫ G.hom) ⟶ Ga // x ≫ p = y'})
    (fun x ↦ ⟨Over.homMk x.1 (by
      change x.1 ≫ Ga.hom = y ≫ G.hom
      rw [← Over.w p, ← Category.assoc, x.2]), Over.OverMorphism.ext x.2⟩) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun z ↦ z.1.left) hab)
end GlobalTheory
