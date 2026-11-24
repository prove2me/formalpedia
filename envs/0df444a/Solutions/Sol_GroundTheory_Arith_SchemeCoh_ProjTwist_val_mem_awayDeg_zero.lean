-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.val_mem_awayDeg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:42.220822+00:00
-- url     : https://prove2.me/submissions/34158f7a-bee5-4c77-a49a-cf1bb63e3299

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_mk_mem_awayDeg

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
theorem _root_.solution {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (z₀ : HomogeneousLocalization.Away 𝒜 f) : z₀.val ∈ awayDeg 𝒜 hf hd 0 := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf z₀
  rw [HomogeneousLocalization.Away.val_mk]
  exact mk_mem_awayDeg hf hd ha (by push_cast [smul_eq_mul]; ring)
end GroundTheory.Arith.SchemeCoh.ProjTwist
