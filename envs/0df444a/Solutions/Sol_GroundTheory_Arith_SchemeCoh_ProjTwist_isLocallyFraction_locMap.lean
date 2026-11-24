-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.isLocallyFraction_locMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:40.514128+00:00
-- url     : https://prove2.me/submissions/ea70da67-520f-4811-9e46-490eea6b1919

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
theorem _root_.solution {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k : ℤ}
    {z : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd k) :
    (isLocallyFraction 𝒜 k).pred
      (fun x : (Proj.basicOpen 𝒜 f : Opens (ProjectiveSpectrum.top 𝒜)) =>
        locMap x.1 (nmem_of_mem x) z) :=
  (toSection hf hd k ⟨z, hz⟩).2
end GroundTheory.Arith.SchemeCoh.ProjTwist
