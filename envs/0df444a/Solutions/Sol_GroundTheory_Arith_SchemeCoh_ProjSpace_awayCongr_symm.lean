-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.awayCongr_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:59:25.465384+00:00
-- url     : https://prove2.me/submissions/bce999db-3acb-4c95-9612-f1a179e506a8

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjBaseChange

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
open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
variable {A B n}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) :
    (awayCongr B n h).symm = awayCongr B n h.symm := by
  subst h
  rfl
end GroundTheory.Arith.SchemeCoh.ProjSpace
