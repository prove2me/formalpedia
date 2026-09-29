-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3d453174-9caf-50e7-afb0-434679c8c6d8

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (S : Finset B) :
    ∃ U : B.Opens, IsAffineOpen U ∧ ∀ b ∈ S, b ∈ U := by

  obtain ⟨U, hU₁, hU₂⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing g

  exact GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
    LB U hU₁ hU₂ S

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing (solution)
