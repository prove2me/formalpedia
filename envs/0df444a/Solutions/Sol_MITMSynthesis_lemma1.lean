-- Prove2me | solution 1 for MITMSynthesis.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-10T12:29:39.101237+00:00
-- url     : https://prove2.me/submissions/411cb81c-4216-4548-8d9f-d9ae1c0c4e0f

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

private theorem depth_set_mem_unitary {n : ℕ} {G : Set Gate} {M : Matrix (Q n) (Q n) ℂ}
    (hM : M ∈ depthOneSet n G) : M ∈ Matrix.unitaryGroup (Q n) ℂ := by
  obtain ⟨L, _, rfl⟩ := hM
  exact layer_mem_unitary L

private theorem product_mem_unitary {n : ℕ} {G : Set Gate} (L : List (Matrix (Q n) (Q n) ℂ))
    (hL : ∀ M ∈ L, M ∈ depthOneSet n G) : L.prod ∈ Matrix.unitaryGroup (Q n) ℂ := by
  induction L with
  | nil => exact one_mem _
  | cons M L ih =>
    rw [List.prod_cons]
    exact mul_mem (depth_set_mem_unitary (hL M (List.mem_cons_self ..)))
      (ih (fun A hA => hL A (List.mem_cons_of_mem M hA)))

theorem solution {n : ℕ} {G : Set Gate} (hG : IsInstructionSet G) (l : ℕ)
    (U : Matrix (Q n) (Q n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Q n) ℂ) :
    U ∈ S (depthOneSet n G) l ↔
      ∃ W ∈ S (depthOneSet n G) ((l + 1) / 2), ∃ X ∈ S (depthOneSet n G) (l / 2),
        W = star X * U := by
  clear hG hU
  have hLength : l / 2 + (l + 1) / 2 = l := by omega
  constructor
  · rintro ⟨L, hL, hAll, rfl⟩
    let A := L.take (l / 2)
    let B := L.drop (l / 2)
    have hA : ∀ M ∈ A, M ∈ depthOneSet n G :=
      fun M hM => hAll M (List.mem_of_mem_take hM)
    have hB : ∀ M ∈ B, M ∈ depthOneSet n G :=
      fun M hM => hAll M (List.mem_of_mem_drop hM)
    have hAB : A.prod * B.prod = L.prod := by
      rw [← List.prod_append, List.take_append_drop]
    have hAstar : star A.prod * A.prod = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (product_mem_unitary A hA)
    refine ⟨B.prod, ⟨B, ?_, hB, rfl⟩, A.prod, ⟨A, ?_, hA, rfl⟩, ?_⟩
    · simp only [B, List.length_drop, hL]
      omega
    · simp only [A, List.length_take, hL]
      omega
    · rw [← hAB, ← mul_assoc, hAstar, one_mul]
  · rintro ⟨W, ⟨B, hB, hAllB, rfl⟩, X, ⟨A, hA, hAllA, rfl⟩, hEq⟩
    have hAstar : A.prod * star A.prod = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (product_mem_unitary A hAllA)
    refine ⟨A ++ B, ?_, ?_, ?_⟩
    · simpa only [List.length_append, hA, hB] using hLength
    · intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · exact hAllA M hM
      · exact hAllB M hM
    · rw [List.prod_append, hEq, ← mul_assoc, hAstar, one_mul]

#print axioms solution
