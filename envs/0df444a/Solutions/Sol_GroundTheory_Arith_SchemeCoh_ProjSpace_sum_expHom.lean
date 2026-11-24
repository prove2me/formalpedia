-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.sum_expHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:33.401333+00:00
-- url     : https://prove2.me/submissions/e99902ab-5863-4681-ad4b-b912f627a382

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent

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
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution (e : Fin (n + 1) →₀ ℕ) : ∑ j, expHom n e j = (e.degree : ℤ) := by
  rw [Finsupp.degree_eq_sum]
  push_cast
  rfl
end GroundTheory.Arith.SchemeCoh.ProjSpace
