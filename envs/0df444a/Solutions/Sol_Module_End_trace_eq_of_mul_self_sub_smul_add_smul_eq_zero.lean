-- Prove2me | solution 1 for Module.End.trace_eq_of_mul_self_sub_smul_add_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d45cb52c-0b9d-526c-a39c-b1bd539c22ad

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_trace_eq_of_mul_self_sub_smul_add_smul_eq_zero

open Matrix

theorem solution {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (b : Module.Basis (Fin 2) k V) {f : Module.End k V} {a c : k}
    (hrel : f * f - a • f + c • 1 = 0) (hdet : LinearMap.det f = c) (hc : c ≠ 0) :
    LinearMap.trace k V f = a := by
  classical
  set M : Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrix b b f with hM
  have htr : LinearMap.trace k V f = M.trace := LinearMap.trace_eq_matrix_trace k b f
  have hdetM : M.det = c := by rw [hM, LinearMap.det_toMatrix]; exact hdet
  have hMrel : M * M - a • M + c • 1 = 0 := by
    have := congrArg (LinearMap.toMatrixAlgEquiv b) hrel
    simp only [map_sub, map_add, map_mul, map_one, map_zero, map_smul,
      LinearMap.toMatrixAlgEquiv_apply, hM] at this
    exact this
  rw [htr, Matrix.trace_fin_two]
  by_contra hne
  have hta : M 0 0 + M 1 1 - a ≠ 0 := sub_ne_zero.mpr hne
  have h00 := congrFun (congrFun hMrel 0) 0
  have h01 := congrFun (congrFun hMrel 0) 1
  have h10 := congrFun (congrFun hMrel 1) 0
  have h11 := congrFun (congrFun hMrel 1) 1
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two, smul_eq_mul,
    Fin.one_eq_zero_iff, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat,
    if_true, if_false, mul_one, mul_zero, add_zero,
    eq_self_iff_true, ite_true, ite_false] at h00 h01 h10 h11
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = c := by
    rw [← Matrix.det_fin_two]; exact hdetM

  have k00 : M 0 0 * (M 0 0 + M 1 1 - a) = 0 := by linear_combination h00 + hd
  have k01 : M 0 1 * (M 0 0 + M 1 1 - a) = 0 := by linear_combination h01

  have z00 : M 0 0 = 0 := (mul_eq_zero.mp k00).resolve_right hta
  have z01 : M 0 1 = 0 := (mul_eq_zero.mp k01).resolve_right hta
  exact hc (by linear_combination -hd + M 1 1 * z00 - M 1 0 * z01)

end S_Module_End_trace_eq_of_mul_self_sub_smul_add_smul_eq_zero
end P2MW
export P2MW.S_Module_End_trace_eq_of_mul_self_sub_smul_add_smul_eq_zero (solution)
