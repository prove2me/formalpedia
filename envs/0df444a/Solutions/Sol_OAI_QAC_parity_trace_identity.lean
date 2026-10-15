-- Prove2me | solution 1 for OAI.QAC.parity_trace_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:35:16.655055+00:00
-- url     : https://prove2.me/submissions/4a47bd77-de71-4224-915e-4e2e1469a4c7

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/ParityTrace.lean:L70-L86
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.parity_trace_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Ancilla
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ParityTrace
import Theorems.Thm_OAI_QAC_ancillaProjection_diagonal
import Theorems.Thm_OAI_QAC_sum_ancillaValid

-- ---- from OAI.InformationTheory.QuantumCircuit.ProductProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma tensorMatrix_mul {N : ℕ} (a b : Fin N → QubitOperator) :
    tensorMatrix a * tensorMatrix b = tensorMatrix (fun i => a i * b i) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, tensorMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z => a i (x i) z * b i z (y i))).symm

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

end SpectralAlgebra

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Computational ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma tensorMatrix_diagonal {N : ℕ} (f : Fin N → Bit → ℂ) :
    tensorMatrix (fun i => Matrix.diagonal (f i)) = Matrix.diagonal (fun x => ∏ i, f i (x i)) := by
  classical
  ext x y
  simp only [tensorMatrix,Matrix.diagonal_apply]
  by_cases hxy : x=y
  · subst y; simp
  · simp only [ite_eq_right hxy]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma flipWord_involutive {N : ℕ} (F : Finset (Fin N)) : Function.Involutive (flipWord F) := by
  intro z
  funext i
  simp only [flipWord]
  split_ifs
  · generalize z i = b
    fin_cases b <;> decide
  · rfl

lemma bitH_X_H : bitH*bitX*bitH=bitZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitH,bitX,bitZ,bitSign,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals first | linear_combination 2*halfScale_complex_sq | linear_combination -2*halfScale_complex_sq

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Ancilla ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma inputHadamard_ancilla_flip (n N : ℕ) :
    localMatrix (inputHadamard n N)*(inputFlip n N*ancillaProjection n N)*
      localMatrix (inputHadamard n N) = inputPhase n N*ancillaProjection n N := by
  unfold localMatrix inputFlip inputPhase ancillaProjection
  simp only [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i.val<n
  · simpa only [inputHadamard,ite_eq_left hi,hadamardGate,mul_one] using bitH_X_H
  · simp [inputHadamard,hi]

lemma bitX_entry (a b : Bit) : bitX a b = if a=1-b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [bitX]

lemma inputFlip_entry (n N : ℕ) (x y : Word N) :
    inputFlip n N x y = if x=flipWord (inputSet n N) y then 1 else 0 := by
  classical
  have hloc (i : Fin N) : (if i.val<n then bitX else (1:QubitOperator)) (x i) (y i) =
      if x i=flipWord (inputSet n N) y i then 1 else 0 := by
    by_cases hi : i.val<n
    · simp [hi,bitX_entry,flipWord,inputSet]
    · simp [hi,Matrix.one_apply,flipWord,inputSet]
  simp only [inputFlip,tensorMatrix,hloc]
  rw [Fintype.prod_boole]
  simp only [← funext_iff]

lemma ancillaValid_flip {n N : ℕ} (z : Word N) :
    ancillaValid n (flipWord (inputSet n N) z) ↔ ancillaValid n z := by
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  simp [flipWord,inputSet,not_lt.mpr hi]

lemma inputFlip_mul_ancilla_entry {n N : ℕ} (B : Operator N) (z : Word N) :
    (inputFlip n N*ancillaProjection n N*B) z z =
      if ancillaValid n z then B (flipWord (inputSet n N) z) z else 0 := by
  classical
  rw [ancillaProjection_diagonal]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,inputFlip_entry]
  have hf (y : Word N) : z=flipWord (inputSet n N) y ↔ y=flipWord (inputSet n N) z := by
    constructor
    · intro h; rw [h,flipWord_involutive]
    · intro h; rw [h,flipWord_involutive]
  simp only [hf,ite_mul,zero_mul]
  simp [ancillaValid_flip]

lemma trace_flip_ancilla {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    Matrix.trace (inputFlip n N*ancillaProjection n N*B) =
      ∑ x : Word n, B (flipWord (inputSet n N) (inputWord x)) (inputWord x) := by
  simp only [Matrix.trace,Matrix.diag_apply,inputFlip_mul_ancilla_entry]
  exact sum_ancillaValid hnN _

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.ParityTrace ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma bitSign_add (a b : Bit) : bitSign (a+b)=bitSign a*bitSign b := by
  fin_cases a <;> fin_cases b <;> norm_num [bitSign,Fin.add_def,Fin.ext_iff]

lemma bitSign_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Bit) :
    bitSign (∑ i ∈ s, f i)=∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bitSign]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Finset.prod_insert hi,bitSign_add,ih]

lemma bitSign_parity {n : ℕ} (x : Word n) : bitSign (parity x)=∏ i, bitSign (x i) :=
  bitSign_finset_sum _ _

lemma inputPhase_diagonal (n N : ℕ) :
    inputPhase n N = Matrix.diagonal (fun z => (inputSign n z:ℂ)) := by
  have hloc : (fun i : Fin N => if i.val<n then bitZ else (1:QubitOperator)) =
      fun i => Matrix.diagonal (fun b => ((if i.val<n then bitSign b else 1:ℝ):ℂ)) := by
    funext i
    split_ifs <;> simp [bitZ,Matrix.diagonal_one]
  rw [inputPhase,hloc,tensorMatrix_diagonal]
  congr 1
  funext z
  simp only [inputSign,Complex.ofReal_prod]

lemma inputSign_inputWord {n N : ℕ} (hnN : n ≤ N) (x : Word n) :
    inputSign n (@inputWord n N x)=bitSign (parity x) := by
  classical
  rw [inputSign,bitSign_parity,← Finset.prod_filter]
  symm
  apply Finset.prod_bij (fun i _ => Fin.castLE hnN i)
  · intro i _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_castLE]
    exact i.isLt
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun k : Fin N => k.val) hij)
  · intro i hi
    refine ⟨⟨i.val,(Finset.mem_filter.mp hi).2⟩,Finset.mem_univ _,?_⟩
    rfl
  · intro i _
    simp [inputWord,i.isLt]

lemma trace_phase_ancilla {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    Matrix.trace (inputPhase n N*ancillaProjection n N*B) =
      ∑ x : Word n, (bitSign (parity x):ℂ)*B (inputWord x) (inputWord x) := by
  classical
  rw [inputPhase_diagonal,ancillaProjection_diagonal,Matrix.diagonal_mul_diagonal]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.diagonal_mul]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  rw [sum_ancillaValid hnN]
  simp only [inputSign_inputWord hnN]

/-- Character orthogonality as a finite-dimensional cyclic trace identity. -/
lemma parity_trace_identity {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    (∑ x : Word n, (localMatrix (inputHadamard n N)*B*localMatrix (inputHadamard n N))
      (flipWord (inputSet n N) (inputWord x)) (inputWord x)) =
    ∑ x : Word n, (bitSign (parity x):ℂ)*B (inputWord x) (inputWord x) := by
  rw [← trace_flip_ancilla hnN]
  let H := localMatrix (inputHadamard n N)
  let T := inputFlip n N*ancillaProjection n N
  change Matrix.trace (T*(H*B*H)) = _
  calc
    Matrix.trace (T*(H*B*H)) = Matrix.trace ((T*(H*B))*H) :=
      congrArg Matrix.trace (mul_assoc T (H*B) H).symm
    _ = Matrix.trace (H*T*(H*B)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace ((H*T*H)*B) := by rw [mul_assoc (H*T) H B]
    _ = Matrix.trace (inputPhase n N*ancillaProjection n N*B) := by
      rw [show H*T*H=inputPhase n N*ancillaProjection n N from inputHadamard_ancilla_flip n N]
    _ = _ := trace_phase_ancilla hnN B

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem solution {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    (∑ x : Word n, (localMatrix (inputHadamard n N)*B*localMatrix (inputHadamard n N))
      (flipWord (inputSet n N) (inputWord x)) (inputWord x)) =
    ∑ x : Word n, (bitSign (parity x):ℂ)*B (inputWord x) (inputWord x) := by
  first
    | exact OAI.QAC.parity_trace_identity hnN B
    | exact OAI.QAC.parity_trace_identity
    | (apply OAI.QAC.parity_trace_identity <;> assumption)
    | (intros; apply OAI.QAC.parity_trace_identity <;> assumption)
