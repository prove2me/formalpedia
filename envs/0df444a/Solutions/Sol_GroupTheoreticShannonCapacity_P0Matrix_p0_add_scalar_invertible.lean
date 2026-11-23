-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.p0_add_scalar_invertible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:56.583351+00:00
-- url     : https://prove2.me/submissions/fdcac824-58ff-4a50-8a3f-dbca46888373

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_p0_sign_property

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (q : ℝ) (hq : 0 < q) :
    IsUnit (M + q • 1) := by
  -- Show det ≠ 0 by proving the kernel is trivial
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [isUnit_iff_ne_zero]
  -- Use the contrapositive: if det = 0 then ∃ nonzero v with (M + qI)v = 0
  intro hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
  obtain ⟨v, hv_ne, hv_eq⟩ := hdet
  -- Apply p0_sign_property to get i with v_i ≠ 0 and (Mv)_i * v_i ≥ 0
  obtain ⟨i, hi_ne, hi_sign⟩ := p0_sign_property n M hM v hv_ne
  -- From (M + qI)v = 0, we have (Mv)_i = -q * v_i
  have hMv_eq : (M.mulVec v) i = -q * v i := by
    have := congr_fun hv_eq i
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
    linarith
  -- But then (Mv)_i * v_i = -q * v_i² < 0
  have hcontra : (M.mulVec v) i * v i < 0 := by
    rw [hMv_eq]
    have hv_sq_pos : v i * v i > 0 := mul_self_pos.mpr hi_ne
    nlinarith
  -- Contradiction with hi_sign
  linarith
end GroupTheoreticShannonCapacity.P0Matrix
