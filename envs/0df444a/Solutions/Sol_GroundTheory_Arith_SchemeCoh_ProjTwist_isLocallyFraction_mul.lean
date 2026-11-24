-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.isLocallyFraction_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:24:46.497054+00:00
-- url     : https://prove2.me/submissions/dd3c71b0-b4f4-4564-9180-21dedb00d232

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
theorem _root_.solution {U : Opens (ProjectiveSpectrum.top 𝒜)} {k₁ k₂ k₃ : ℤ}
    (hk : k₁ + k₂ = k₃) {a b : ∀ x : U, Loc 𝒜 x.1} (ha : (isLocallyFraction 𝒜 k₁).pred a)
    (hb : (isLocallyFraction 𝒜 k₂).pred b) : (isLocallyFraction 𝒜 k₃).pred (a * b) := fun x => by
  obtain ⟨Va, ma, ia, i, j, hij, r, s, hr, hs, hsn, wa⟩ := ha x
  obtain ⟨Vb, mb, ib, i', j', hij', r', s', hr', hs', hsn', wb⟩ := hb x
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, i + i', j + j', by push_cast; omega,
    r * r', s * s', SetLike.mul_mem_graded hr hr', SetLike.mul_mem_graded hs hs',
    fun ⟨y, hya, hyb⟩ => nmem_mul (hsn ⟨y, hya⟩) (hsn' ⟨y, hyb⟩), fun ⟨y, hya, hyb⟩ => ?_⟩
  have e1 : a (ia ⟨y, hya⟩) = _ := wa ⟨y, hya⟩
  have e2 : b (ib ⟨y, hyb⟩) = _ := wb ⟨y, hyb⟩
  change a (ia ⟨y, hya⟩) * b (ib ⟨y, hyb⟩) = _
  rw [e1, e2, Localization.mk_mul]
  rfl
end GroundTheory.Arith.SchemeCoh.ProjTwist
