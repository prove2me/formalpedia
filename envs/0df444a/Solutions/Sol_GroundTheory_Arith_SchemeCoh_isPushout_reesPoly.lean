-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isPushout_reesPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:07.11724+00:00
-- url     : https://prove2.me/submissions/c771970f-7f57-4634-a2a3-4e28fc9b7972

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackGamma
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isPullback_rees
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isPullback_reesPoly
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
    IsPushout (CommRingCat.ofHom (algV X V)) (CommRingCat.ofHom (Polynomial.C))
      ((reesPr I X).app V ≫ (reesPolyMap I X).app _) (polyInr I V) := by
  have h1 := (isPushout_app_of_isPullback (isPullback_rees I X) hV).flip
  have h2 := (isPushout_app_of_isPullback (isPullback_reesPoly I X) (hV.preimage (reesPr I X))).flip
  have h := (h1.paste_horiz h2).flip
  refine h.of_iso (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Scheme.ΓSpecIso (.of (Polynomial A)))
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [algV]
  · rw [Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, Scheme.ΓSpecIso_naturality,
      Category.assoc]
    rfl
  · simp
  · simp [polyInr]
end GroundTheory.Arith.SchemeCoh
