-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.lval_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:48.202166+00:00
-- url     : https://prove2.me/submissions/3a7cc76a-e5e3-46fb-953e-73f8f1b6a705

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayDegEquiv_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_res_theta
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_theta_lval
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_ofL
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_range_comp_subset
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_LDeg_mono
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply
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


attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.awayDegEquiv_apply
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_zero
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_ofL

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p)
    (i : Fin (p + 2) → Fin (n + 1)) :
    lval (d _ _ p σ) i = ∑ a : Fin (p + 2), ((-1 : ℤ) ^ (a : ℕ)) • lval σ (i ∘ a.succAbove) := by
  have key : d _ _ p σ i = theta i k (∑ a : Fin (p + 2), ((-1 : ℤ) ^ (a : ℕ)) •
      ⟨lval σ (i ∘ a.succAbove), LDeg_mono (range_comp_subset _ _) k (lval_mem σ _)⟩) := by
    rw [d_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul]
    congr 1
    conv_lhs => rw [← theta_lval σ (i ∘ a.succAbove)]
    exact res_theta (range_comp_subset _ _) _ k _
  rw [lval, key, AddEquiv.symm_apply_apply, AddSubgroup.val_finsetSum]
  simp
end GroundTheory.Arith.SchemeCoh.ProjSpace
