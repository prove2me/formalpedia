-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_eq_phase_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:33.816902+00:00
-- url     : https://prove2.me/submissions/d4467f3f-78e4-454a-89c4-c55e6724c338

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
public import Theorems.Thm_Lean4LPD_PauliString_qubitXZ_eq_phase_qubitPauli
public import Theorems.Thm_Lean4LPD_PauliString_yPhase_succ
public import Theorems.Thm_Lean4LPD_PauliString_tensorPauli_succ_apply
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_split
public import Theorems.Thm_Lean4LPD_PauliString_cls_fst
public import Theorems.Thm_Lean4LPD_PauliString_cls_herm
public import Theorems.Thm_Lean4LPD_PauliString_cls_snd
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_apply
public import Theorems.Thm_Lean4LPD_PauliString_herm_x
public import Theorems.Thm_Lean4LPD_PauliString_herm_z
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_highSet
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sq
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_restr_apply
public import Theorems.Thm_Lean4LPD_PauliString_restr_univ
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_wt_cls
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_iPow_add
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_norm_iPow
public import Theorems.Thm_Lean4LPD_star_negOnePow
attribute [local simp] Lean4LPD.PauliString.cls_fst
attribute [local simp] Lean4LPD.PauliString.cls_herm
attribute [local simp] Lean4LPD.PauliString.cls_snd
attribute [local simp] Lean4LPD.PauliString.coeffVec_apply
attribute [local simp] Lean4LPD.PauliString.herm_x
attribute [local simp] Lean4LPD.PauliString.herm_z
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_highSet
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.pauliNorm_sq
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.restr_apply
attribute [local simp] Lean4LPD.PauliString.restr_univ
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.toMatrix_one
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
attribute [local simp] Lean4LPD.PauliString.weight_one
attribute [local simp] Lean4LPD.PauliString.weight_phaseMul
attribute [local simp] Lean4LPD.PauliString.wt_cls
attribute [local simp] Lean4LPD.conj_negOnePow
attribute [local simp] Lean4LPD.iPow_signPhase
attribute [local simp] Lean4LPD.iPow_two
attribute [local simp] Lean4LPD.negOnePow_mul_self
attribute [local simp] Lean4LPD.negOnePow_one
attribute [local simp] Lean4LPD.negOnePow_zero
attribute [local simp] Lean4LPD.norm_iPow
attribute [local simp] Lean4LPD.star_negOnePow



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset
namespace Lean4LPD.PauliString
theorem _root_.solution : ∀ {n : ℕ} (s : PauliString n),
    toMatrix s = iPow (s.phase - yPhase s.x s.z) • tensorPauli n s.x s.z := by
  intro n
  induction n with
  | zero =>
      intro s
      ext a b
      have hab : a = b + s.x := Subsingleton.elim _ _
      have hab' : a = b := Subsingleton.elim _ _
      rw [Matrix.smul_apply, smul_eq_mul, toMatrix_apply, if_pos hab]
      simp only [tensorPauli, Matrix.one_apply, if_pos hab', mul_one]
      simp [yPhase, dotProduct]
  | succ n ih =>
      intro s
      ext a b
      rw [toMatrix_split, qubitXZ_eq_phase_qubitPauli]
      rw [ih (dropFirst s)]
      simp only [Matrix.smul_apply, smul_eq_mul, tensorPauli_succ_apply, dropFirst]
      have hphase : iPow (-((s.x 0 * s.z 0).val : ZMod 4)) *
          iPow (s.phase - yPhase (Fin.tail s.x) (Fin.tail s.z)) =
          iPow (s.phase - yPhase s.x s.z) := by
        rw [← iPow_add, yPhase_succ]
        congr 1
        ring
      calc
        (iPow (-((s.x 0 * s.z 0).val : ZMod 4)) * qubitPauli (s.x 0) (s.z 0) (a 0) (b 0)) *
            (iPow (s.phase - yPhase (Fin.tail s.x) (Fin.tail s.z)) *
              tensorPauli n (Fin.tail s.x) (Fin.tail s.z) (Fin.tail a) (Fin.tail b)) =
            (iPow (-((s.x 0 * s.z 0).val : ZMod 4)) *
              iPow (s.phase - yPhase (Fin.tail s.x) (Fin.tail s.z))) *
                (qubitPauli (s.x 0) (s.z 0) (a 0) (b 0) *
                  tensorPauli n (Fin.tail s.x) (Fin.tail s.z) (Fin.tail a) (Fin.tail b)) := by ring
        _ = _ := by rw [hphase]
end Lean4LPD.PauliString
