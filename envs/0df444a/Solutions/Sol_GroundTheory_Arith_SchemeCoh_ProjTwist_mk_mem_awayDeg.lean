-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.mk_mem_awayDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:38.66551+00:00
-- url     : https://prove2.me/submissions/cd0c8aa7-9da6-4807-8459-88517c386ee4

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
theorem _root_.solution {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k : ℤ} {n j : ℕ} {a : A}
    (ha : a ∈ 𝒜 j) (hj : (j : ℤ) = n * d + k) :
    Localization.mk a (fpow f n) ∈ awayDeg 𝒜 hf hd k :=
  ⟨n, j, a, ha, hj, rfl⟩
end GroundTheory.Arith.SchemeCoh.ProjTwist
