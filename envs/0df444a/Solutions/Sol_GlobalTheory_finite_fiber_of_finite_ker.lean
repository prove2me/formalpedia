-- Prove2me | solution 1 for GlobalTheory.finite_fiber_of_finite_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:48:58.556993+00:00
-- url     : https://prove2.me/submissions/309667be-42b0-46dc-a004-294aed1e6734

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints

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
theorem _root_.solution {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Ga G T : C} [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    (h : Finite {x : T ⟶ Ga // x ≫ p = 1}) (y : T ⟶ G) :
    Finite {x : T ⟶ Ga // x ≫ p = y} := by
  rcases isEmpty_or_nonempty {x : T ⟶ Ga // x ≫ p = y} with he | ⟨⟨x₀, hx₀⟩⟩
  · infer_instance
  refine Finite.of_injective (β := {x : T ⟶ Ga // x ≫ p = 1})
    (fun x ↦ ⟨x₀⁻¹ * x.1, by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hx₀, x.2, inv_mul_cancel]⟩) ?_
  intro a b hab
  exact Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))
end GlobalTheory
