-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.iSup_stdOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:26:08.879802+00:00
-- url     : https://prove2.me/submissions/df86e951-ef1a-4613-a852-9969bb093599

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext


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
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open ProjSpace
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution : ⨆ j, stdOpen A n j = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (grading A n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' p 0 : homogeneousSubmodule (Fin (n + 1)) A 0) :
    MvPolynomial (Fin (n + 1)) A) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (MvPolynomial.mem_support_iff.mp hm) h0
end GroundTheory.Arith.SchemeCoh.ProjSpace
