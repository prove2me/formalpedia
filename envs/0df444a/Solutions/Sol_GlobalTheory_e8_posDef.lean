-- Prove2me | solution 1 for GlobalTheory.e8_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:24.665898+00:00
-- url     : https://prove2.me/submissions/122cfb44-ff67-4bda-bf9f-181866019d37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8
import Theorems.Thm_GlobalTheory_e8_det_eq_one
import Theorems.Thm_GlobalTheory_E8roots_transpose_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (E8.map (fun x : ℤ => (x : ℝ))).PosDef := by
  set f : ℤ →+* ℝ := Int.castRingHom ℝ with hf
  change (E8.map f).PosDef
  have h : E8.map f = ((1 / 2 : ℝ) • E8roots.map f)ᴴ * ((1 / 2 : ℝ) • E8roots.map f) := by
    have h4 : (E8roots.map f)ᵀ * E8roots.map f = (4 : ℝ) • E8.map f := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, E8roots_transpose_mul_self]
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        smul_eq_mul, map_mul]
      simp [hf]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, h4, smul_smul, smul_smul]
    norm_num
  have hs : (E8.map f).PosSemidef := by
    rw [h]; exact Matrix.posSemidef_conjTranspose_mul_self _
  rw [hs.posDef_iff_det_ne_zero]
  have : (E8.map f).det = f E8.det := (RingHom.map_det f E8).symm
  rw [this, e8_det_eq_one, map_one]
  exact one_ne_zero
end GlobalTheory
