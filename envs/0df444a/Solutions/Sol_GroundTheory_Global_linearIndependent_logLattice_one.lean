-- Prove2me | solution 1 for GroundTheory.Global.linearIndependent_logLattice_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:09.576023+00:00
-- url     : https://prove2.me/submissions/e79f847b-9161-4c5e-9b98-37f5a77724fe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_linearIndependent_logLattice_basis
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_Global_sum_fullLog
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution {ι : Type*} (b : Basis ι ℤ (logLattice L)) :
    LinearIndependent ℝ (Sum.elim (fun i => (b i : InfinitePlace L → ℝ))
      (fun _ : Unit => (1 : InfinitePlace L → ℝ))) := by
  classical
  refine LinearIndependent.sum_type (linearIndependent_logLattice_basis L b) ?_ ?_
  · rw [linearIndependent_unique_iff]
    exact one_ne_zero
  · let s : (InfinitePlace L → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => ∑ w, y w
        map_add' := fun y z => by simp [Finset.sum_add_distrib]
        map_smul' := fun c y => by simp [Finset.mul_sum] }
    have hs : Submodule.span ℝ (Set.range fun i => (b i : InfinitePlace L → ℝ)) ≤
        LinearMap.ker s := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨x, hx⟩ := (b i).2
      change ∑ w, (b i : InfinitePlace L → ℝ) w = 0
      rw [← hx]
      exact sum_fullLog L x
    rw [Submodule.disjoint_def]
    intro y hy1 hy2
    rw [Set.range_const, Submodule.mem_span_singleton] at hy2
    obtain ⟨c, rfl⟩ := hy2
    have h1 : s (c • 1) = 0 := hs hy1
    have h2 : s (c • 1) = c * Fintype.card (InfinitePlace L) := by
      simp [s, Finset.sum_const]
    rw [h2] at h1
    have h3 : (Fintype.card (InfinitePlace L) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [mul_eq_zero, or_iff_left h3] at h1
    rw [h1, zero_smul]
end GroundTheory.Global
