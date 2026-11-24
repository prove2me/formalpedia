-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.exists_val_eq_of_mem_awayDeg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:39.717702+00:00
-- url     : https://prove2.me/submissions/0cf8de92-c16c-4791-92a2-db9d67ec592a

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
theorem _root_.solution {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    {z : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd 0) :
    ∃ z₀ : HomogeneousLocalization.Away 𝒜 f, z₀.val = z := by
  obtain ⟨n, j, a, ha, hj, rfl⟩ := hz
  have e : n • d = j := by
    have : ((n • d : ℕ) : ℤ) = j := by push_cast [smul_eq_mul]; linarith
    exact_mod_cast this
  refine ⟨HomogeneousLocalization.mk ⟨j, ⟨a, ha⟩, ⟨f ^ n, e ▸ SetLike.pow_mem_graded n hf⟩,
    (fpow f n).2⟩, ?_⟩
  rw [HomogeneousLocalization.val_mk]
  rfl
end GroundTheory.Arith.SchemeCoh.ProjTwist
