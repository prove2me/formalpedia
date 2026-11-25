-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.C_mem_reesCoeffRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:18.3567+00:00
-- url     : https://prove2.me/submissions/24d42b53-eb7c-45b3-b512-64d511465028

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesRing

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
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
noncomputable section
variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {V : X.Opens} (hV : IsAffineOpen V)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (c : Γ(X, V)) : Polynomial.C c ∈ reesCoeffRing I X V := by
  intro n
  rw [Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simp
  · exact zero_mem _
end GroundTheory.Arith.SchemeCoh
