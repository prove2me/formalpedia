-- Prove2me | solution 1 for HopfAlgebra.algebra_etale_of_module_finite_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4e002065-425c-5e28-97e3-157d8a222a1f

import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.HopfAlgebra.Basic
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero

set_option maxHeartbeats 3200000

attribute [local instance] Ideal.Quotient.field

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] :
    Algebra.Etale K A := by

  haveI : Algebra.FiniteType K A := inferInstance

  haveI : IsReduced A := HopfAlgebra.isReduced_of_finiteType_of_charZero K A

  haveI : IsArtinianRing A := .of_finite K A
  haveI : Finite (MaximalSpectrum A) := inferInstance

  have hI (I : MaximalSpectrum A) : Algebra.FormallyEtale K (A ⧸ I.asIdeal) := by
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    haveI : Module.Finite K (A ⧸ I.asIdeal) := Module.Finite.quotient K _
    haveI : Algebra.IsAlgebraic K (A ⧸ I.asIdeal) := Algebra.IsIntegral.isAlgebraic
    haveI : Algebra.IsSeparable K (A ⧸ I.asIdeal) := inferInstance
    exact Algebra.FormallyEtale.of_isSeparable K (A ⧸ I.asIdeal)
  refine ⟨?_, ?_⟩
  ·
    exact Algebra.FormallyEtale.of_equiv
      ((IsArtinianRing.equivPi A).restrictScalars K).symm
  ·
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

end S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
end P2MW
export P2MW.S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero (solution)
