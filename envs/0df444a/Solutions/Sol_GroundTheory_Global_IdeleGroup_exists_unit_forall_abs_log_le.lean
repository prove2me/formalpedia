-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.exists_unit_forall_abs_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:21.886256+00:00
-- url     : https://prove2.me/submissions/f77edb79-5f0c-49cf-b7cc-89b37498b973

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteModule_diagonal_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_log_infiniteModule
import Theorems.Thm_GroundTheory_Global_IdeleGroup_logVector_diagonal_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (M₀ : ℝ) : ∃ M : ℝ, ∀ y : IdeleGroup K,
    |Real.log (infiniteModule y)| ≤ M₀ → ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |Real.log ‖((diagonal K (unitsToUnits K u) * y : IdeleGroup K) : 𝔸[K]).1 w‖| ≤ M := by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded B).exists_norm_le
  set C' := max C 0 with hC'
  refine ⟨M₀ + Fintype.card {w : InfinitePlace K // w ≠ w₀} * C' + C', fun y hy ↦ ?_⟩
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans hy
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨⟨e, he⟩, hmem, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logVector y)
  rw [Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)] at he
  obtain ⟨u, -, rfl⟩ := he
  refine ⟨Additive.toMul u, ?_⟩
  set z := diagonal K (unitsToUnits K (Additive.toMul u)) * y with hz
  have hF : logVector z ∈ ZSpan.fundamentalDomain B := by
    rw [hz, logVector_diagonal_mul]
    exact hmem
  have hbound : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(w.1.mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w.1‖| ≤ C' := fun w ↦ by
    have := (norm_le_pi_norm (logVector z) w).trans (hC _ hF)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hmult : ∀ (w : InfinitePlace K) (t : ℝ), |t| ≤ |(w.mult : ℝ) * t| := fun w t ↦ by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg t) (by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast w.mult_pos)
  have hmod : infiniteModule z = infiniteModule y := by
    rw [hz, infiniteModule_mul, infiniteModule_diagonal_unitsToUnits, one_mul]
  intro w
  by_cases hw : w = w₀
  · subst hw
    have hsum := log_infiniteModule z
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K), hmod] at hsum
    have h1 : |∑ w : {w : InfinitePlace K // w ≠ w₀},
        (w.1.mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w.1‖| ≤
        Fintype.card {w : InfinitePlace K // w ≠ w₀} * C' := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun w _ ↦ hbound w).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h2 : ((w₀ : InfinitePlace K).mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w₀‖ = Real.log (infiniteModule y) -
        ∑ w : {w : InfinitePlace K // w ≠ w₀},
          (w.1.mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w.1‖ := by
      linarith
    refine (hmult (w₀ : InfinitePlace K) _).trans ?_
    rw [h2]
    refine (abs_sub _ _).trans ?_
    linarith
  · refine (hmult w _).trans ((hbound ⟨w, hw⟩).trans ?_)
    have : 0 ≤ (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ) * C' :=
      mul_nonneg (Nat.cast_nonneg _) hC'0
    linarith
end GroundTheory.Global.IdeleGroup
