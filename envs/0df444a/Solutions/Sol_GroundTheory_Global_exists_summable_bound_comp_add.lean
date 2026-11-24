-- Prove2me | solution 1 for GroundTheory.Global.exists_summable_bound_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:40.596505+00:00
-- url     : https://prove2.me/submissions/5884f5bb-b17c-49f6-b552-dbeb9e989d59

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Theorems.Thm_GroundTheory_Global_exists_norm_le_inv_one_add_pow

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
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GroundTheory.Global
theorem _root_.solution (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (R : ℝ) :
    ∃ u : Λ → ℝ, Summable u ∧ ∀ ℓ : Λ, ∀ x : E, ‖x‖ ≤ R → ‖g (x + ℓ)‖ ≤ u ℓ := by
  set k := finrank ℤ Λ + 1
  obtain ⟨C, hC, hg⟩ := exists_norm_le_inv_one_add_pow g k
  set R' := max R 0
  refine ⟨fun ℓ => C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹, ?_, ?_⟩
  · apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with ℓ hℓ
    have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  · intro ℓ x hx
    have hR : ‖x‖ ≤ R' := hx.trans (le_max_left _ _)
    have hR0 : 0 ≤ R' := le_max_right _ _
    have key : 1 + ‖ℓ‖ ≤ (1 + R') * (1 + ‖x + ℓ‖) := by
      have : ‖(ℓ : E)‖ ≤ ‖x + ℓ‖ + ‖x‖ := by
        calc ‖(ℓ : E)‖ = ‖(x + ℓ) - x‖ := by simp
          _ ≤ ‖x + ℓ‖ + ‖x‖ := norm_sub_le _ _
      have h' : ‖ℓ‖ ≤ ‖x + ℓ‖ + ‖x‖ := this
      nlinarith [norm_nonneg (x + ℓ)]
    calc ‖g (x + ℓ)‖ ≤ C * ((1 + ‖x + ℓ‖) ^ k)⁻¹ := hg _
      _ = C * ((1 + R') ^ k * (((1 + R') * (1 + ‖x + ℓ‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc ((1 + R') ^ k), mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ C * ((1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹) := by
          gcongr
      _ = C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹ := by ring
end GroundTheory.Global
