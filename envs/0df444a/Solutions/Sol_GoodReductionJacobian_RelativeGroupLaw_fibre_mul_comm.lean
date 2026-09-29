-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.fibre_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1b4774b2-5169-58cb-8d5d-2e6e2754a06c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_fibre_mul_comm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (s : (Spec (CommRingCat.of R) : Scheme.{u}))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (RelativeGroupLaw.baseResidueField s)))
    (x y : SchemeHomOver t' (RelativeGroupLaw.fibreStr f s)) :
    (G.fibre s).mul t' x y = (G.fibre s).mul t' y x := by
  rw [RelativeGroupLaw.fibre_mul, RelativeGroupLaw.fibre_mul, hcomm]

end S_GoodReductionJacobian_RelativeGroupLaw_fibre_mul_comm
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_fibre_mul_comm (solution)
