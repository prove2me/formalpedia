-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjHom.mul_pow_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:09:12.224825+00:00
-- url     : https://prove2.me/submissions/ea27b888-741e-42e8-8e28-2e26537069b9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjHom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



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
theorem _root_.solution {R : Type*} [CommRing R] {v u w c : R} (hc : IsUnit c) (k d : ℕ)
    (h : v * (c ^ d * u) ^ k = c ^ (k • d) * w) : v * u ^ k = w := by
  apply (hc.pow (k * d)).mul_right_injective
  simp only [smul_eq_mul] at h
  calc c ^ (k * d) * (v * u ^ k) = v * (c ^ d * u) ^ k := by ring
    _ = c ^ (k * d) * w := h
end GroundTheory.Arith.SchemeCoh.ProjHom
