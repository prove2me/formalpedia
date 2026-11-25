-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.awayCongr_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:20.78624+00:00
-- url     : https://prove2.me/submissions/7239f0c8-cdf4-4484-a1f2-d570017845de

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
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) {d : ℕ}
    (hs : s ∈ grading B n d) (ht : t ∈ grading B n d) (m : ℕ) (x : MvPolynomial (Fin (n + 1)) B)
    (hx : x ∈ grading B n (m • d)) :
    awayCongr B n h (Away.mk (grading B n) hs m x hx) = Away.mk (grading B n) ht m x hx := by
  subst h
  rfl
end GroundTheory.Arith.SchemeCoh.ProjSpace
