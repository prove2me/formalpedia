-- Prove2me | solution 1 for GlobalTheory.exists_linearMap_det_eq_prod_inv_succMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:47.658804+00:00
-- url     : https://prove2.me/submissions/fb033139-0c0c-4b77-b6fd-deb84702c26a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Theorems.Thm_GlobalTheory_exists_basis_norm_eq_succMin
import Theorems.Thm_GlobalTheory_spanCovol_bot
import Theorems.Thm_GlobalTheory_succMin_le_norm_of_notMem_span
import Theorems.Thm_GlobalTheory_succMin_mono_of_isZLattice
import Theorems.Thm_GlobalTheory_succMin_pos_of_isZLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ T : E →ₗ[ℝ] E, LinearMap.det T = (∏ i : Fin (finrank ℝ E), succMin L (i + 1))⁻¹ ∧
      ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖T x‖ := by
  obtain ⟨b, hbL, hbN⟩ := exists_basis_norm_eq_succMin L
  have h : finrank ℝ E = Fintype.card (Fin (finrank ℝ E)) := (Fintype.card_fin _).symm
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h b
  let l : Fin (finrank ℝ E) → ℝ := fun i ↦ succMin L (i + 1)
  have hl : ∀ i, 0 < l i := fun i ↦ succMin_pos_of_isZLattice (by omega) i.2
  let T : E →ₗ[ℝ] E := Matrix.toLin o.toBasis o.toBasis (Matrix.diagonal fun i ↦ (l i)⁻¹)
  have hT : ∀ x i, o.repr (T x) i = (l i)⁻¹ * o.repr x i := by
    intro x i
    have := Matrix.repr_toLin o.toBasis o.toBasis (Matrix.diagonal fun i ↦ (l i)⁻¹) x
    have h2 := congrFun this i
    rw [Matrix.mulVec_diagonal] at h2
    exact h2
  refine ⟨T, ?_, fun x hx h0 ↦ ?_⟩
  · rw [LinearMap.det_toLin, Matrix.det_diagonal, Finset.prod_inv_distrib]
  · have hne : (Finset.univ.filter fun i ↦ o.repr x i ≠ 0).Nonempty := by
      by_contra hc
      apply h0
      apply o.repr.injective
      ext i
      simpa using (Finset.filter_eq_empty_iff.1 (Finset.not_nonempty_iff_eq_empty.1 hc)
        (Finset.mem_univ i))
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image _ id hne
    have hk0 : o.repr x k ≠ 0 := (Finset.mem_filter.1 hk).2
    have hspan : x ∉ span ℝ (b '' {j | (j : ℕ) < k}) := by
      intro hmem
      have hle : span ℝ (b '' {j | (j : ℕ) < k}) ≤ LinearMap.ker (o.toBasis.coord k) := by
        refine span_le.2 ?_
        rintro _ ⟨j, hj, rfl⟩
        exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular' h b
          (show j < k from hj)
      exact hk0 (hle hmem)
    have hx1 : l k ≤ ‖x‖ :=
      succMin_le_norm_of_notMem_span b.linearIndependent hbL (fun j ↦ (hbN j).le) k.2.le hx hspan
    have hcmp : ‖(l k)⁻¹ • x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
      rw [← o.repr.norm_map, ← o.repr.norm_map, EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [hT, map_smul, PiLp.smul_apply, smul_eq_mul]
      by_cases hi : o.repr x i = 0
      · simp [hi]
      · have hik : i ≤ k := hmax i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        have hlik : l i ≤ l k :=
          succMin_mono_of_isZLattice (Nat.succ_le_succ hik) k.2
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (inv_pos.2 (hl i)).le,
          Real.norm_of_nonneg (inv_pos.2 (hl k)).le]
        have := hl i
        have := hl k
        gcongr
    refine le_trans ?_ (le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hcmp)
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 (hl k)).le, le_inv_mul_iff₀ (hl k), mul_one]
    exact hx1
end GlobalTheory
