-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.locMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:12.740981+00:00
-- url     : https://prove2.me/submissions/2099937a-f3d2-4352-b332-d614a59e49d0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway

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
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjTwist
namespace GroundTheory.Arith.SchemeCoh.ProjTwist
theorem _root_.solution {f : A} (x : ProjectiveSpectrum 𝒜) (hx : f ∉ x.asHomogeneousIdeal)
    (a : A) : locMap x hx (algebraMap A _ a) = algebraMap A _ a := by
  rw [locMap, IsLocalization.map_eq]
  rfl
end GroundTheory.Arith.SchemeCoh.ProjTwist
