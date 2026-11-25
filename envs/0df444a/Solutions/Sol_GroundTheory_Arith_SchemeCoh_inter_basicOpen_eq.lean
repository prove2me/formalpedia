-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.inter_basicOpen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:36.536311+00:00
-- url     : https://prove2.me/submissions/451937bf-9882-4113-8b4f-99dad10c3370

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
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
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
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
open ProjTwist
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {ι : Type w} (v : ι → A) {m : ℕ} (i : Fin (m + 1) → ι) :
    inter (X := (Proj 𝒜).toTopCat) (fun j => Proj.basicOpen 𝒜 (v j)) i =
      Proj.basicOpen 𝒜 (∏ a, v (i a)) := by
  ext x
  change x ∈ inter (X := (Proj 𝒜).toTopCat) (fun j => Proj.basicOpen 𝒜 (v j)) i ↔ _
  rw [mem_inter_iff]
  change (∀ a, v (i a) ∉ x.asHomogeneousIdeal.toIdeal) ↔
    (∏ a, v (i a)) ∉ x.asHomogeneousIdeal.toIdeal
  have := x.isPrime
  rw [Ideal.IsPrime.prod_mem_iff]
  simp
end GroundTheory.Arith.SchemeCoh
