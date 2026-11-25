-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.twistMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:33.616235+00:00
-- url     : https://prove2.me/submissions/b84fe878-b58d-4bf4-ad28-85e76fc817ad

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray

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
universe w w' u
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjTwist
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
namespace GroundTheory.Arith.SchemeCoh.ProjTwist
theorem _root_.solution {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal)
    (t : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op W)) (x : W) :
    (twistMap hu k hW t).1 x = twistFrac u k x.1 (hW x) * (t.1 x).val := rfl
end GroundTheory.Arith.SchemeCoh.ProjTwist
