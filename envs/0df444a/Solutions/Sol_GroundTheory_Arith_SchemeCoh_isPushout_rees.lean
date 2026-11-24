-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isPushout_rees
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:06.136008+00:00
-- url     : https://prove2.me/submissions/631ab594-8137-4453-9a71-63800813b350

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackGamma
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isPullback_rees
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isPushout_app_of_isPullback


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
variable {V : X.Opens} (hV : IsAffineOpen V)
include hV
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution :
    IsPushout (CommRingCat.ofHom (algV X V)) (CommRingCat.ofHom (algebraMap A (reesAlgebra I)))
      ((reesPr I X).app V) (reesInr I V) := by
  refine (isPushout_app_of_isPullback (isPullback_rees I X) hV).of_iso
    (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Scheme.ΓSpecIso (.of (reesAlgebra I))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp [algV]
  · exact Scheme.ΓSpecIso_naturality _
  · simp
  · simp [reesInr]
end GroundTheory.Arith.SchemeCoh
