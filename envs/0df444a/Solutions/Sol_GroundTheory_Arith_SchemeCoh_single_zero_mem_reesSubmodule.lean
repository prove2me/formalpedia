-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.single_zero_mem_reesSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:00.390154+00:00
-- url     : https://prove2.me/submissions/c8e9d2c8-bfc9-497c-88a7-6065832a28a0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open Polynomial
universe u v w
variable {A : Type u} [CommRing A] (I : Ideal A)
variable (M : Type v) [AddCommGroup M] [Module A M]
variable {I M}
variable (I M)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (m : M) :
    PolynomialModule.single A 0 m ∈ reesSubmodule I M := by
  intro n
  rw [PolynomialModule.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h
    simp
  · exact zero_mem _
end GroundTheory.Arith.SchemeCoh
