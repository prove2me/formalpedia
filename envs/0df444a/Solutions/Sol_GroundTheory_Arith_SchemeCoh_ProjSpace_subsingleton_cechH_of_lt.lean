-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.subsingleton_cechH_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:12:42.366315+00:00
-- url     : https://prove2.me/submissions/ca4f1499-69eb-4a11-b5f3-7ad4fcfe0b62

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechCompute
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
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
noncomputable section
open scoped Classical
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {k : ℤ} {q : ℕ} (hq0 : 0 < q) (hqn : q < n) :
    Subsingleton (cechH (twistAb A n k) (cover A n) q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  refine subsingleton_of_forall_eq 0 fun c => ?_
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [cls_eq_zero_iff, coboundaries_succ]
  refine exists_d_eq_of_coeff_allNeg σ hσ fun i m hm => coeff_lval_eq_zero σ (fun hi => ?_) hm
  have := Fintype.card_le_of_surjective i hi
  simp only [Fintype.card_fin] at this
  omega
end GroundTheory.Arith.SchemeCoh.ProjSpace
