-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c1924b1c-ce61-576f-be0c-18b103ced05d

import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) :
    ∃ g : GrpObj (Over.mk f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (lift a b ≫ g.mul) =
          G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        overHomToSchemeHomOver (toUnit (Over.mk t) ≫ g.one) = G.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (a ≫ g.inv) = G.inv t (overHomToSchemeHomOver a)) :=
  ⟨G.grpObjOverMk, fun t a b => G.overHomToSchemeHomOver_mul t a b,
    fun t => G.overHomToSchemeHomOver_one t, fun t a => G.overHomToSchemeHomOver_inv t a⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq (solution)
