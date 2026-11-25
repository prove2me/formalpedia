-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.map_mem_reesCoeffRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:20.683788+00:00
-- url     : https://prove2.me/submissions/28119747-145d-48a0-bc8b-018e5f93265a

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
theorem _root_.solution (r : reesAlgebra I) :
    (r : Polynomial A).map (algV X V) ∈ reesCoeffRing I X V := by
  intro n
  rw [Polynomial.coeff_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).1 r.2 n)
end GroundTheory.Arith.SchemeCoh
