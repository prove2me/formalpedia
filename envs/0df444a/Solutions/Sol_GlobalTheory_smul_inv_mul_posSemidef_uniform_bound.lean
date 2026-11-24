-- Prove2me | solution 1 for GlobalTheory.smul_inv_mul_posSemidef_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:51.007802+00:00
-- url     : https://prove2.me/submissions/b0928800-187c-4a29-af5c-54c8baa6fe16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
import Theorems.Thm_GlobalTheory_WeightedInverseBound_norm_sq_le_dot
import Theorems.Thm_GlobalTheory_WeightedInverseBound_norm_le_of_coercive
import Theorems.Thm_GlobalTheory_WeightedInverseBound_isUnit_det_of_coercive
import Theorems.Thm_GlobalTheory_WeightedInverseBound_norm_mulVec_le
import Theorems.Thm_GlobalTheory_WeightedInverseBound_abs_entry_le
import Theorems.Thm_GlobalTheory_WeightedInverseBound_bound_one_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open WeightedInverseBound
namespace GlobalTheory
theorem _root_.solution : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖ := by
  intro g a B c C hc hB
  obtain ⟨K, hK⟩ := bound_one_add B hB
  refine ⟨(1 + g / c * (1 + g * |C|)) * K, fun Y' t hs hlo hhi ht i x => ?_⟩
  have hw := hK t ht i x
  set P := ∑ l, t l • B l with hP
  have hP0 : ∀ z, 0 ≤ z ⬝ᵥ P.mulVec z := by
    intro z
    have : P.PosSemidef := Matrix.posSemidef_sum _ fun l _ => (hB l).smul (ht l).le
    simpa using this.dotProduct_mulVec_nonneg z
  have hY : ∀ z, c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Y' + P).mulVec z := by
    intro z
    rw [Matrix.add_mulVec, dotProduct_add]
    linarith [hlo z, hP0 z]
  have hZ : ∀ z, 1 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (1 + P).mulVec z := by
    intro z
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec]
    linarith [hP0 z]
  have hYu := isUnit_det_of_coercive hc hY
  have hZu := isUnit_det_of_coercive one_pos hZ
  set v := (t i • B i).mulVec x with hv
  set w := (1 + P)⁻¹.mulVec v with hwdef
  have hu : (t i • ((Y' + P)⁻¹ * B i)).mulVec x = (Y' + P)⁻¹.mulVec v := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_smul]
  rw [hu]
  set u := (Y' + P)⁻¹.mulVec v with hudef
  have e1 : (Y' + P).mulVec u = v := by
    rw [hudef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hYu, Matrix.one_mulVec]
  have e2 : (1 + P).mulVec w = v := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hZu, Matrix.one_mulVec]
  have e3 : (Y' + P).mulVec (u - w) = w - Y'.mulVec w := by
    rw [Matrix.mulVec_sub, e1, ← e2, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    abel
  have h0 : ∀ z, 0 ≤ z ⬝ᵥ Y'.mulVec z := fun z =>
    le_trans (mul_nonneg hc.le (le_trans (mul_self_nonneg _) (norm_sq_le_dot z))) (hlo z)
  have b1 := norm_mulVec_le (abs_nonneg C) (abs_entry_le hs h0 hhi) w
  have b2 := norm_le_of_coercive hc hY (u - w)
  rw [e3] at b2
  have b3 : ‖w - Y'.mulVec w‖ ≤ (1 + g * |C|) * ‖w‖ := by
    have := norm_sub_le w (Y'.mulVec w)
    linarith
  have b4 : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := by
    have := norm_add_le w (u - w)
    rwa [add_sub_cancel] at this
  have hgc : (0 : ℝ) ≤ g / c := by positivity
  have b5 := mul_le_mul_of_nonneg_left b3 hgc
  calc ‖u‖ ≤ (1 + g / c * (1 + g * |C|)) * ‖w‖ := by linarith
    _ ≤ (1 + g / c * (1 + g * |C|)) * (K * ‖x‖) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring
end GlobalTheory
