-- Prove2me | solution 1 for GlobalTheory.minkowski_det_bound_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:50.622086+00:00
-- url     : https://prove2.me/submissions/8f5c91f8-b5a8-4cbe-988a-b5754b64e903

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_MinkowskiDetBoundGramOfDetNeZero
import Theorems.Thm_GlobalTheory_minkowski_det_bound_gram_of_det_ne_zero

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
theorem _root_.solution (m : ℕ) (hm : 0 < m) (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosDef) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (z i : ℝ))) :
    a ^ m ≤ (m : ℝ) ^ m * G.det := by
  open MatrixOrder in
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hG.posSemidef.nonneg
  have hC' : G = Cᵀ * Cᵀᵀ := by
    rw [hC, transpose_transpose, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hd := hG.det_pos
  have hB : (Cᵀ).det ≠ 0 := by
    intro h0
    rw [hC', det_mul, h0, zero_mul] at hd
    exact lt_irrefl _ hd
  rw [hC'] at h ⊢
  exact minkowski_det_bound_gram_of_det_ne_zero m hm _ hB a ha h
end GlobalTheory
