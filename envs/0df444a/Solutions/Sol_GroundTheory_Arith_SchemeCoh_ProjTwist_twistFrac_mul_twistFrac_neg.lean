-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.twistFrac_mul_twistFrac_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:29.836554+00:00
-- url     : https://prove2.me/submissions/f4be5832-1b5f-402b-a4fc-c6fbc8723bf2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayDegEquiv_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_ofL
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_zero
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
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.awayDegEquiv_apply
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_ofL
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_zero
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



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
theorem _root_.solution (u : A) (k : ℤ) (x : ProjectiveSpectrum 𝒜)
    (hx : u ∉ x.asHomogeneousIdeal) : twistFrac u k x hx * twistFrac u (-k) x hx = 1 := by
  rw [twistFrac, twistFrac, Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [neg_neg, Submonoid.coe_mul, Submonoid.coe_one, one_mul, mul_one]
  ring
end GroundTheory.Arith.SchemeCoh.ProjTwist
