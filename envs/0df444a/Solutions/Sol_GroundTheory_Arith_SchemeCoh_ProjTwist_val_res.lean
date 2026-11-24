-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.val_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:06.731104+00:00
-- url     : https://prove2.me/submissions/9949e32c-f0f0-420c-9fc0-b1c18046ec41

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
theorem _root_.solution (h : V ≤ U) (s : Γ(twistingSheaf 𝒜 k, U)) (x : V) :
    val ((twistingSheaf 𝒜 k).presheaf.map (homOfLE h).op s) x = val s ⟨x.1, h x.2⟩ := rfl
end GroundTheory.Arith.SchemeCoh.ProjTwist
