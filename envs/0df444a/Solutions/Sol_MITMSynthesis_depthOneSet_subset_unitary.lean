-- Prove2me | solution 1 for MITMSynthesis.depthOneSet_subset_unitary
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-10T12:29:28.77633+00:00
-- url     : https://prove2.me/submissions/020d4a8d-3da7-4596-9237-705d72ffa7d4

import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S

open MITMSynthesis
open scoped Kronecker

private theorem placement_mem_unitary {n : ℕ} (p : Placement n) :
    p.unitary ∈ Matrix.unitaryGroup (Q n) ℂ := by
  classical
  let R := {j : Fin n // j ∉ Set.range p.qubits} → Fin 2
  let e : Q n ≃ Q p.gate.arity × R :=
    (Equiv.piEquivPiSubtypeProd (fun j : Fin n => j ∈ Set.range p.qubits)
      (fun _ => Fin 2)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr (Equiv.ofInjective p.qubits p.qubits.injective).symm
          (Equiv.refl (Fin 2))) (Equiv.refl R))
  let K : Matrix (Q p.gate.arity × R) (Q p.gate.arity × R) ℂ :=
    (p.gate.mat : Matrix (Q p.gate.arity) (Q p.gate.arity) ℂ) ⊗ₖ (1 : Matrix R R ℂ)
  have hK : K ∈ Matrix.unitaryGroup (Q p.gate.arity × R) ℂ :=
    Matrix.kronecker_mem_unitary p.gate.mat.property (one_mem _)
  have hPlace : p.unitary = K.submatrix e e := by
    ext x y
    have hComplement : (∀ j, j ∉ Set.range p.qubits → x j = y j) ↔
        (fun j : {j : Fin n // j ∉ Set.range p.qubits} => x j) =
          (fun j : {j : Fin n // j ∉ Set.range p.qubits} => y j) := by
      constructor
      · intro h
        funext j
        exact h j j.property
      · intro h j hj
        exact congrFun h ⟨j, hj⟩
    change (if (∀ j, j ∉ Set.range p.qubits → x j = y j) then
      (p.gate.mat : Matrix (Q p.gate.arity) (Q p.gate.arity) ℂ) (x ∘ p.qubits) (y ∘ p.qubits)
        else 0) = (p.gate.mat : Matrix (Q p.gate.arity) (Q p.gate.arity) ℂ)
          (x ∘ p.qubits) (y ∘ p.qubits) *
        (1 : Matrix R R ℂ) (fun j => x j) (fun j => y j)
    by_cases h : ∀ j, j ∉ Set.range p.qubits → x j = y j
    · simp only [Matrix.one_apply, if_pos h, if_pos (hComplement.mp h), mul_one]
    · have h' := fun hc => h (hComplement.mpr hc)
      simp only [Matrix.one_apply, if_neg h, if_neg h', mul_zero]
  rw [hPlace, Matrix.mem_unitaryGroup_iff]
  change K.submatrix e e * (star K).submatrix e e = 1
  rw [Matrix.submatrix_mul_equiv, Matrix.mem_unitaryGroup_iff.mp hK,
    Matrix.submatrix_one_equiv]

private theorem layer_mem_unitary {n : ℕ} (L : List (Placement n)) :
    layerUnitary L ∈ Matrix.unitaryGroup (Q n) ℂ := by
  induction L with
  | nil => exact one_mem _
  | cons p L ih =>
    exact mul_mem (placement_mem_unitary p) ih

theorem solution (n : ℕ) (G : Set Gate) :
    depthOneSet n G ⊆ (Matrix.unitaryGroup (Q n) ℂ : Set (Matrix (Q n) (Q n) ℂ)) := by
  rintro M ⟨L, _, rfl⟩
  exact layer_mem_unitary L

#print axioms solution
