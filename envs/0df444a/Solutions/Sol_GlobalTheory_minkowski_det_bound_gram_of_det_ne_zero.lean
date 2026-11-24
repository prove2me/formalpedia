-- Prove2me | solution 1 for GlobalTheory.minkowski_det_bound_gram_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:39.773254+00:00
-- url     : https://prove2.me/submissions/2f557109-3c5e-4a2b-9833-47bcf58887c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_MinkowskiDetBoundGramOfDetNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtA_mink_pi_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (m : ℕ) (hm : 0 < m) (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.det ≠ 0)
    (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ (B * Bᵀ) *ᵥ (fun i => (z i : ℝ))) :
    a ^ m ≤ (m : ℝ) ^ m * (B * Bᵀ).det := by
  classical
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (Ne.isUnit hB)
  have hli : LinearIndependent ℝ B.row := Matrix.linearIndependent_rows_iff_isUnit.2 hu
  let b : Module.Basis (Fin m) ℝ (Fin m → ℝ) := basisOfPiSpaceOfLinearIndependent hli
  have hb : (b : Fin m → Fin m → ℝ) = B.row := coe_basisOfPiSpaceOfLinearIndependent hli
  have hpos : 0 < |B.det| := abs_pos.2 hB
  set t : ℝ := |B.det| ^ ((m : ℝ)⁻¹) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hpos _
  have htm : t ^ m = |B.det| := Real.rpow_inv_natCast_pow hpos.le hm.ne'
  obtain ⟨x, hx, hx0, hxt⟩ := ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_le hm b ht0 (by
    rw [htm, hb]; exact le_of_eq rfl)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hx0
  have hx' : ∑ i, c i • b i = (fun i => (c i : ℝ)) ᵥ* B := by
    ext j
    simp [hb, Matrix.vecMul, dotProduct, Finset.sum_apply]
  rw [hx'] at hxt
  have h1 := h c hc
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose] at h1
  set y := (fun i => (c i : ℝ)) ᵥ* B
  have h2 : y ⬝ᵥ y ≤ m * t ^ 2 := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin m)), y i * y i ≤ t ^ 2 := by
      intro i _
      have h3 : |y i| ≤ t := (norm_le_pi_norm y i).trans hxt
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have h4 := Finset.sum_le_sum this
    simpa [dotProduct] using h4
  calc a ^ m ≤ (m * t ^ 2) ^ m := pow_le_pow_left₀ ha (h1.trans h2) m
    _ = (m : ℝ) ^ m * (B * Bᵀ).det := by
      rw [mul_pow, ← pow_mul, mul_comm 2 m, pow_mul, htm, sq_abs, det_mul, det_transpose, sq]
end GlobalTheory
