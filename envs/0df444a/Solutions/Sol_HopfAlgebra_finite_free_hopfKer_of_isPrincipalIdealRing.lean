-- Prove2me | solution 1 for HopfAlgebra.finite_free_hopfKer_of_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c6df08a6-dad8-50e8-8066-66b6d3474ed5

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing

set_option autoImplicit false

open HopfAlgebra

universe u v w

namespace S17KT5b

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
variable {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B)

theorem finite : Module.Finite R ↥(hopfKer π) := by
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsNoetherian R A := isNoetherian_of_isNoetherianRing_of_finite R A
  exact Module.Finite.of_injective (Subalgebra.val (hopfKer π)).toLinearMap Subtype.val_injective

theorem free : Module.Free R ↥(hopfKer π) := by
  haveI := finite π
  exact Module.free_of_finite_type_torsion_free'

end S17KT5b

theorem solution {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) :
    Module.Finite R ↥(HopfAlgebra.hopfKer π) ∧ Module.Free R ↥(HopfAlgebra.hopfKer π) :=
  ⟨S17KT5b.finite π, S17KT5b.free π⟩

end S_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing
end P2MW
export P2MW.S_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing (solution)
