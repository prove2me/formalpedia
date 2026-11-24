-- Prove2me | solution 1 for GlobalTheory.ClassMin.shifted_lt_add_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:09.455314+00:00
-- url     : https://prove2.me/submissions/ad4b379f-954a-4e67-b781-47132896f83a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
import Theorems.Thm_GlobalTheory_ClassMin_map_add_zsmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
variable {X : Type*} [AddCommGroup X]
variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}
namespace GlobalTheory.ClassMin
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (hN : 1 + 2 * c < N) {ν : X →+ ℝ} {e μ : X}
    (hμ : 0 < Q μ) (hF : 0 ≤ Q μ / N + ν μ) (h : |polar Q e μ| ≤ c * polar Q μ μ) :
    Q e / N + ν e < Q (e + N • μ) / N + ν (e + N • μ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have e1 : Q (e + N • μ) / N + ν (e + N • μ) = Q e / N + ν e +
      (polar Q e μ + (N - 1) * Q μ + N * (Q μ / N + ν μ)) := by
    rw [map_add_zsmul, map_add, map_zsmul, zsmul_eq_mul]
    field_simp
    ring
  rw [polar_self, two_smul, abs_le] at h
  have h1 := mul_pos (sub_pos.2 hN) hμ
  have h2 := mul_nonneg hN0.le hF
  rw [e1]
  nlinarith [h.1]
end GlobalTheory.ClassMin
