-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjHom.transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:09:08.391349+00:00
-- url     : https://prove2.me/submissions/bae84b80-7463-44c7-a6b3-d26676aea7e5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjHom
variable {X : Scheme.{u}}
variable (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
namespace GroundTheory.Arith.SchemeCoh.ProjHom
theorem _root_.solution {R S : CommRingCat.{u}} (ρ : R ⟶ S) {v x y : R} {x' y' : S} (hx : ρ x = x')
    (hy : ρ y = y') (k : ℕ) (h : v * x ^ k = y) : ρ v * x' ^ k = y' := by
  subst hx hy
  rw [← map_pow, ← map_mul, h]
end GroundTheory.Arith.SchemeCoh.ProjHom
