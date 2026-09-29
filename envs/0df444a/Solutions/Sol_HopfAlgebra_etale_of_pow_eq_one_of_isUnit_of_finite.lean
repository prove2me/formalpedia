-- Prove2me | solution 1 for HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/592ba47f-943f-5ae3-b6fa-40bad8f573b6

import Mathlib
import Theorems.Thm_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit
import Theorems.Thm_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite

universe u v

set_option autoImplicit false

theorem solution
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    [IsNoetherianRing R] [Module.Finite R H] [Module.Flat R H]
    (n : ℕ) (hn : IsUnit (n : R))
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ n = 1) :
    Algebra.Etale R H := by
  haveI : Algebra.FinitePresentation R H := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI := HopfAlgebra.formallyUnramified_of_ker_counit_eq_sq
    (HopfAlgebra.ker_counit_eq_sq_of_pow_eq_one_of_isUnit (R := R) (H := H) n hn hH)
  exact Algebra.Etale.of_formallyUnramified_of_flat

end S_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite
end P2MW
export P2MW.S_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite (solution)
