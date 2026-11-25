-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.reesRingHom_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:22.162538+00:00
-- url     : https://prove2.me/submissions/0782a35b-84ee-4294-9399-568dd5eeef85

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
theorem _root_.solution (c : Γ(X, V)) : reesRingHom hV ((reesPr I X).app V c) = Polynomial.C c :=
  polyRingHom_inl hV c
end GroundTheory.Arith.SchemeCoh
