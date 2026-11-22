-- Prove2me | solution 1 for Lean4LPD.PauliString.linearIndependent_toMatrix_mul_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:21.177711+00:00
-- url     : https://prove2.me/submissions/9a478a21-327c-463c-bbf3-7030728266ad

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_ne_zero
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_ne_smul

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : sympForm G s = 1) :
    LinearIndependent ℂ ![toMatrix s, toMatrix (G * s)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, add_zero, smul_eq_zero] at hab
    exact ⟨hab.resolve_right (toMatrix_ne_zero s), rfl⟩
  · refine absurd ?_ (toMatrix_mul_ne_smul h (-(b⁻¹ * a)))
    have hB : b • toMatrix (G * s) = (-a) • toMatrix s := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
      exact hab
    calc toMatrix (G * s) = b⁻¹ • (b • toMatrix (G * s)) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = (-(b⁻¹ * a)) • toMatrix s := by rw [hB, smul_smul]; congr 1; ring
end Lean4LPD.PauliString
