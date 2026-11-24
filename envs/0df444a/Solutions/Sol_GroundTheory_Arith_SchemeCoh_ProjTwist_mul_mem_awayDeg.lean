-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.mul_mem_awayDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:13.603801+00:00
-- url     : https://prove2.me/submissions/a9af9d19-3b6a-435a-a775-e359c50544de

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
theorem _root_.solution {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k₁ k₂ : ℤ}
    {z w : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd k₁) (hw : w ∈ awayDeg 𝒜 hf hd k₂) :
    z * w ∈ awayDeg 𝒜 hf hd (k₁ + k₂) := by
  obtain ⟨n, j, a, ha, hj, rfl⟩ := hz
  obtain ⟨m, j', b, hb, hj', rfl⟩ := hw
  refine ⟨n + m, j + j', a * b, SetLike.mul_mem_graded ha hb, by push_cast; linarith, ?_⟩
  rw [Localization.mk_mul, fpow_add]
end GroundTheory.Arith.SchemeCoh.ProjTwist
