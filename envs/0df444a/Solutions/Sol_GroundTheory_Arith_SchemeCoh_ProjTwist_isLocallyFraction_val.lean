-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.isLocallyFraction_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:28.077733+00:00
-- url     : https://prove2.me/submissions/87e331be-1cda-4cf2-a8ac-a7a7e4bb2688

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist

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
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjTwist
variable {𝒜} {k : ℤ} {U V : (Proj 𝒜).Opens}
namespace GroundTheory.Arith.SchemeCoh.ProjTwist
theorem _root_.solution (s : Γ(twistingSheaf 𝒜 k, U)) :
    (isLocallyFraction 𝒜 k).pred (val s) := s.2
end GroundTheory.Arith.SchemeCoh.ProjTwist
