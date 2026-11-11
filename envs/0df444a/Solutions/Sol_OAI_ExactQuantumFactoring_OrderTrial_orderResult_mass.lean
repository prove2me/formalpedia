-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.OrderTrial.orderResult_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:13:53.011898+00:00
-- url     : https://prove2.me/submissions/59ad741e-2031-43f8-8aeb-3a442bdbdf29

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_ExactQuantumFactoring
import Definitions.Def_OAIQ222A004

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExactnessFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.Exactness
open scoped BigOperators

lemma finiteInner_self {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    finiteInner v v = ((∑ x, Complex.normSq (v x):ℝ):ℂ) := by
  simp only [finiteInner, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]

end ExactQuantumFactoring.Exactness


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_GateSemantics
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

lemma sum_boolFin_succ {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : (Fin (n+1) → Bool) → α) :
    ∑ x, f x = (∑ x : Fin n → Bool, f (Fin.cons false x)) +
      ∑ x : Fin n → Bool, f (Fin.cons true x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  simpa [Fintype.sum_prod_type, Fin.consEquiv] using
    (add_comm (∑ x : Fin n → Bool, f (Fin.cons true x))
      (∑ x : Fin n → Bool, f (Fin.cons false x)))

lemma sum_boolFin_zero {α : Type*} [AddCommMonoid α]
    (f : (Fin 0 → Bool) → α) : ∑ x, f x = f Fin.elim0 := by
  exact Fintype.sum_unique _

lemma permutationMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) : permutationMatrix e ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    permutationMatrix, Matrix.of_apply]
  simp [Finset.sum_ite_eq', e.injective.eq_iff, Matrix.one_apply, eq_comm]

lemma not_localMatrix : Primitive.not.localMatrix = permutationMatrix notPerm := by
  change Matrix.of (fun x y : Basis 1 => Primitive.not.matrix (List.ofFn x) (List.ofFn y)) =
    permutationMatrix notPerm
  ext x y
  simp [Primitive.matrix, List.ofFn_succ, Matrix.of_apply,
    permutationMatrix, notPerm, funext_iff, Fin.forall_fin_succ]

lemma cnot_localMatrix : Primitive.cnot.localMatrix = permutationMatrix cnotPerm := by
  change Matrix.of (fun x y : Basis 2 => Primitive.cnot.matrix (List.ofFn x) (List.ofFn y)) =
    permutationMatrix cnotPerm
  ext x y
  simp [Primitive.matrix, List.ofFn_succ, Matrix.of_apply,
    permutationMatrix, cnotPerm, funext_iff, Fin.forall_fin_succ]

lemma toffoli_localMatrix : Primitive.toffoli.localMatrix = permutationMatrix toffoliPerm := by
  change Matrix.of (fun x y : Basis 3 => Primitive.toffoli.matrix (List.ofFn x) (List.ofFn y)) =
    permutationMatrix toffoliPerm
  ext x y
  simp [Primitive.matrix, List.ofFn_succ, Matrix.of_apply,
    permutationMatrix, toffoliPerm, funext_iff, Fin.forall_fin_succ]

lemma hadamard_local_unitary : Primitive.hadamard.localMatrix ∈
    Matrix.unitaryGroup (Basis Primitive.hadamard.arity) ℂ := by
  change Matrix.of (fun x y : Fin 1 → Bool =>
    Primitive.hadamard.matrix (List.ofFn x) (List.ofFn y)) ∈
    Matrix.unitaryGroup (Fin 1 → Bool) ℂ
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [sum_boolFin_succ]
  simp only [sum_boolFin_zero]
  have hx : x = Fin.cons (x 0) Fin.elim0 := by ext i; fin_cases i; rfl
  have hy : y = Fin.cons (y 0) Fin.elim0 := by ext i; fin_cases i; rfl
  rw [hx, hy]
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  cases x 0 <;> cases y 0 <;>
    simp [Primitive.matrix, List.ofFn_succ] <;> ring_nf <;>
      simp [inv_pow, hs]

lemma phase_local_unitary : Primitive.phase.localMatrix ∈
    Matrix.unitaryGroup (Basis Primitive.phase.arity) ℂ := by
  change Matrix.of (fun x y : Fin 1 → Bool =>
    Primitive.phase.matrix (List.ofFn x) (List.ofFn y)) ∈
    Matrix.unitaryGroup (Fin 1 → Bool) ℂ
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [sum_boolFin_succ]
  simp only [sum_boolFin_zero]
  have hx : x = Fin.cons (x 0) Fin.elim0 := by ext i; fin_cases i; rfl
  have hy : y = Fin.cons (y 0) Fin.elim0 := by ext i; fin_cases i; rfl
  rw [hx, hy]
  cases x 0 <;> cases y 0 <;> simp [Primitive.matrix, List.ofFn_succ]

lemma Primitive.local_unitary (p : Primitive) :
    p.localMatrix ∈ Matrix.unitaryGroup (Basis p.arity) ℂ := by
  cases p with
  | not => rw [not_localMatrix]; exact permutationMatrix_unitary _
  | cnot => rw [cnot_localMatrix]; exact permutationMatrix_unitary _
  | toffoli => rw [toffoli_localMatrix]; exact permutationMatrix_unitary _
  | hadamard => exact hadamard_local_unitary
  | phase => exact phase_local_unitary

lemma unitary_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  have hs : star (Matrix.reindex e e A) = Matrix.reindex e e (star A) :=
    Matrix.conjTranspose_reindex e e A
  rw [hs]
  change Matrix.reindexAlgEquiv ℂ ℂ e (star A) * Matrix.reindexAlgEquiv ℂ ℂ e A = 1
  rw [← map_mul, hA, map_one]

lemma controlledMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    controlledMatrix A ∈ Matrix.unitaryGroup (Bool × ι) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  ext ⟨a,x⟩ ⟨b,y⟩
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;>
    simp [controlledMatrix, Matrix.one_apply]
  · by_cases h : x = y
    · subst y; simp
    · simp [h, Ne.symm h]
  · simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.one_apply] using congrFun (congrFun hA x) y

lemma Gate.baseLocalMatrix_eq (g : Gate) : g.baseLocalMatrix =
    if g.inverse then star g.primitive.localMatrix else g.primitive.localMatrix := by
  ext x y
  cases hi : g.inverse <;>
    simp [Gate.baseLocalMatrix, Gate.baseMatrix, Primitive.localMatrix, hi]

lemma Gate.baseLocal_unitary (g : Gate) :
    g.baseLocalMatrix ∈ Matrix.unitaryGroup (Basis g.primitive.arity) ℂ := by
  rw [g.baseLocalMatrix_eq]
  split_ifs
  · exact Unitary.star_mem g.primitive.local_unitary
  · exact g.primitive.local_unitary

lemma Gate.controlled_localMatrix (p : Primitive) (inv : Bool) :
    (Gate.mk p inv true).localMatrix =
    Matrix.reindex (Fin.consEquiv (fun _ : Fin (p.arity+1) => Bool))
      (Fin.consEquiv (fun _ : Fin (p.arity+1) => Bool))
      (controlledMatrix (Gate.mk p inv true).baseLocalMatrix) := by
  change Matrix.of (fun x y : Basis (p.arity+1) =>
    (Gate.mk p inv true).matrix (List.ofFn x) (List.ofFn y)) = _
  ext x y
  simp only [Gate.matrix, ↓reduceIte, List.ofFn_succ, Matrix.of_apply,
    Matrix.reindex_apply, Fin.consEquiv, controlledMatrix,
    Gate.baseLocalMatrix]
  cases hx : x 0 <;> cases hy : y 0 <;> simp [hx, hy, Fin.tail_def]

lemma Gate.local_unitary (g : Gate) : g.localMatrix ∈ Matrix.unitaryGroup (Basis g.arity) ℂ := by
  rcases g with ⟨p, inv, ctrl⟩
  cases ctrl
  · exact Gate.baseLocal_unitary ⟨p, inv, false⟩
  · rw [Gate.controlled_localMatrix]
    exact unitary_reindex _ _ (controlledMatrix_unitary _ (Gate.baseLocal_unitary _))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitSemantics
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

lemma tensor_unitary {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (hB : B ∈ Matrix.unitaryGroup κ ℂ) :
    A ⊗ₖ B ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA hB ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  change (star A * A) ⊗ₖ (star B * B) = 1
  rw [hA, hB, Matrix.one_kronecker_one]

lemma Instruction.matrix_eq_reindex {q : ℕ} (o : Instruction q) :
    o.matrix = Matrix.reindex o.splitBasis.symm o.splitBasis.symm
      (o.gate.localMatrix ⊗ₖ (1 : Matrix (o.Unused → Bool) (o.Unused → Bool) ℂ)) := by
  classical
  ext x y
  change (if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i then
      o.gate.matrix (List.ofFn (x ∘ o.wire)) (List.ofFn (y ∘ o.wire)) else 0) =
    o.gate.matrix (List.ofFn (x ∘ o.wire)) (List.ofFn (y ∘ o.wire)) *
      if (fun i : o.Unused => x i.val) = (fun i : o.Unused => y i.val) then 1 else 0
  by_cases h : ∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i
  · have he : (fun i : o.Unused => x i.val) = (fun i : o.Unused => y i.val) :=
      funext (fun i => h i.val i.property)
    rw [ite_eq_left h, ite_eq_left he, mul_one]
  · have he : (fun i : o.Unused => x i.val) ≠ (fun i : o.Unused => y i.val) := by
      intro hh
      apply h
      intro i hi
      exact congrFun hh ⟨i,hi⟩
    rw [ite_eq_right h, ite_eq_right he, mul_zero]

lemma Instruction.unitary {q : ℕ} (o : Instruction q) :
    o.matrix ∈ Matrix.unitaryGroup (Basis q) ℂ := by
  classical
  rw [o.matrix_eq_reindex]
  exact unitary_reindex _ _ (tensor_unitary _ _ o.gate.local_unitary (one_mem _))

lemma programMatrix_fold {q : ℕ} (ops : List (Instruction q))
    (A : Matrix (Basis q) (Basis q) ℂ) :
    ops.foldl (fun A (o : Instruction _) => o.matrix * A) A = programMatrix ops * A := by
  induction ops generalizing A with
  | nil => simp [programMatrix]
  | cons o ops ih =>
    change ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * A) =
      ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * 1) * A
    rw [ih, ih, Matrix.mul_one, Matrix.mul_assoc]

lemma programMatrix_unitary {q : ℕ} (ops : List (Instruction q)) :
    programMatrix ops ∈ Matrix.unitaryGroup (Basis q) ℂ := by
  classical
  induction ops with
  | nil => exact one_mem _
  | cons o ops ih =>
    change ops.foldl (fun A (o : Instruction _) => o.matrix * A) (o.matrix * 1) ∈ _
    rw [programMatrix_fold, Matrix.mul_one]
    exact mul_mem ih o.unitary

lemma Gate.reverse_baseMatrix (g : Gate) (x y : List Bool) :
    g.reverse.baseMatrix x y = star (g.baseMatrix y x) := by
  cases h : g.inverse <;> simp [Gate.reverse, Gate.baseMatrix, h]

lemma Gate.reverse_matrix (g : Gate) (x y : List Bool) :
    g.reverse.matrix x y = star (g.matrix y x) := by
  by_cases h : g.controlled = true
  · cases x with
    | nil => cases y <;> simp [Gate.matrix, Gate.reverse, h]
    | cons a x =>
      cases y with
      | nil => simp [Gate.matrix, Gate.reverse, h]
      | cons b y =>
        cases a <;> cases b <;> simp [Gate.matrix, h, Gate.reverse]
        · by_cases hh : x = y
          · subst y; simp
          · simp [hh, Ne.symm hh]
        · simpa [Gate.reverse, h] using g.reverse_baseMatrix x y
  · have hf : g.controlled = false := Bool.eq_false_iff.mpr h
    simpa [Gate.matrix, hf, Gate.reverse] using g.reverse_baseMatrix x y

lemma Instruction.reverse_matrix {q : ℕ} (o : Instruction q) :
    o.reverse.matrix = star o.matrix := by
  classical
  ext x y
  change (if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i then
      o.gate.reverse.matrix (List.ofFn (x ∘ o.wire)) (List.ofFn (y ∘ o.wire)) else 0) =
    star (if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → y i = x i then
      o.gate.matrix (List.ofFn (y ∘ o.wire)) (List.ofFn (x ∘ o.wire)) else 0)
  rw [Gate.reverse_matrix]
  have he : (∀ i : Fin q, (∀ j, o.wire j ≠ i) → y i = x i) ↔
      (∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i) := by
    apply forall_congr'
    intro i
    exact imp_congr_right (fun _ => eq_comm)
  simp only [he]
  split_ifs <;> simp

lemma programMatrix_append {q : ℕ} (a b : List (Instruction q)) :
    programMatrix (a ++ b) = programMatrix b * programMatrix a := by
  unfold programMatrix
  rw [List.foldl_append, programMatrix_fold]
  rfl

lemma programMatrix_reverse {q : ℕ} (ops : List (Instruction q)) :
    programMatrix (ops.reverse.map Instruction.reverse) = star (programMatrix ops) := by
  induction ops with
  | nil => simp [programMatrix]
  | cons o ops ih =>
    rw [List.reverse_cons, List.map_append, programMatrix_append, ih]
    change programMatrix [o.reverse] * star (programMatrix ops) =
      star (ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * 1))
    rw [programMatrix_fold]
    simp [programMatrix, Instruction.reverse_matrix]

lemma unitary_finiteInner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (v w : ι → ℂ) :
    Exactness.finiteInner (A.mulVec v) (A.mulVec w) = Exactness.finiteInner v w := by
  change star (A.mulVec v) ⬝ᵥ A.mulVec w = star v ⬝ᵥ w
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hA,
    Matrix.one_mulVec]

lemma unitary_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    (∑ x, Complex.normSq (A.mulVec v x)) = ∑ x, Complex.normSq (v x) := by
  apply Complex.ofReal_injective
  simpa [Exactness.finiteInner_self] using unitary_finiteInner A hA v v

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil _root_.OAI.ExactQuantumFactoring.cnotAt_target _root_.OAI.ExactQuantumFactoring.notAt_target _root_.OAI.ExactQuantumFactoring.toffoliAt_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

lemma matrix_basisVector {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix κ ι ℂ) (x : ι) : A.mulVec (basisVector x) = fun y => A y x := by
  funext y
  simp [Matrix.mulVec, dotProduct, basisVector]

lemma permutationMatrix_basisVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) (x : ι) :
    (permutationMatrix e).mulVec (basisVector x) = basisVector (e x) := by
  rw [matrix_basisVector]
  rfl

lemma Instruction.liftPerm_matrix {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity))
    (he : o.gate.localMatrix = permutationMatrix e) :
    o.matrix = permutationMatrix (o.liftPerm e) := by
  classical
  rw [o.matrix_eq_reindex, he]
  ext x y
  change ((if (o.splitBasis x).1 = e (o.splitBasis y).1 then (1:ℂ) else 0) *
      if (o.splitBasis x).2 = (o.splitBasis y).2 then 1 else 0) =
    if x = o.liftPerm e y then 1 else 0
  have hh : x = o.liftPerm e y ↔
      (o.splitBasis x).1 = e (o.splitBasis y).1 ∧
      (o.splitBasis x).2 = (o.splitBasis y).2 := by
    rw [← o.splitBasis.injective.eq_iff]
    simp [Instruction.liftPerm, Prod.ext_iff]
  simp only [hh]
  split_ifs <;> simp_all

lemma Instruction.liftPerm_wire {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity)) (x : Basis q) (i : Fin o.gate.arity) :
    o.liftPerm e x (o.wire i) = e (x ∘ o.wire) i := by
  have h := congrArg (fun z => z.1 i) (o.splitBasis.apply_symm_apply
    ((Equiv.prodCongr e (Equiv.refl (o.Unused → Bool))) (o.splitBasis x)))
  exact h

lemma Instruction.liftPerm_unused {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity)) (x : Basis q) (i : Fin q)
    (hi : ∀ j, o.wire j ≠ i) : o.liftPerm e x i = x i := by
  have h := congrArg (fun z => z.2 ⟨i,hi⟩) (o.splitBasis.apply_symm_apply
    ((Equiv.prodCongr e (Equiv.refl (o.Unused → Bool))) (o.splitBasis x)))
  exact h

lemma Instruction.liftPerm_basisVector {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity))
    (he : o.gate.localMatrix = permutationMatrix e) (x : Basis q) :
    o.matrix.mulVec (basisVector x) = basisVector (o.liftPerm e x) := by
  rw [o.liftPerm_matrix e he, permutationMatrix_basisVector]

lemma notAt_lift {q : ℕ} (t : Fin q) (x : Basis q) :
    (notAt t).liftPerm notPerm x = Function.update x t (!x t) := by
  classical
  funext i
  by_cases hi : t = i
  · subst i
    rw [Function.update_self]
    exact (notAt t).liftPerm_wire notPerm x ⟨0,by change 0<1; decide⟩
  · rw [(notAt t).liftPerm_unused notPerm x i (by intro j; exact hi)]
    simp [Function.update, Ne.symm hi]

lemma cnotAt_lift {q : ℕ} (c t : Fin q) (hct : c ≠ t) (x : Basis q) :
    (cnotAt c t hct).liftPerm cnotPerm x =
      Function.update x t (Bool.xor (x c) (x t)) := by
  classical
  funext i
  by_cases hi : t = i
  · subst i
    rw [Function.update_self]
    exact (cnotAt c t hct).liftPerm_wire cnotPerm x ⟨1,by change 1<2; decide⟩
  · by_cases hc : c = i
    · subst i
      rw [Function.update_of_ne (Ne.symm hi)]
      exact (cnotAt c t hct).liftPerm_wire cnotPerm x ⟨0,by change 0<2; decide⟩
    · rw [(cnotAt c t hct).liftPerm_unused cnotPerm x i (by
        intro j; fin_cases j <;> simpa [cnotAt] using (by assumption : _))]
      simp [Function.update, Ne.symm hi]

lemma toffoliAt_lift {q : ℕ} (a b t : Fin q)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (x : Basis q) :
    (toffoliAt a b t hab hat hbt).liftPerm toffoliPerm x =
      Function.update x t (Bool.xor (x t) (x a && x b)) := by
  classical
  funext i
  by_cases hi : t = i
  · subst i
    rw [Function.update_self]
    exact (toffoliAt a b t hab hat hbt).liftPerm_wire toffoliPerm x ⟨2,by change 2<3; decide⟩
  · by_cases ha : a = i
    · subst i
      rw [Function.update_of_ne (Ne.symm hi)]
      exact (toffoliAt a b t hab hat hbt).liftPerm_wire toffoliPerm x ⟨0,by change 0<3; decide⟩
    · by_cases hb : b = i
      · subst i
        rw [Function.update_of_ne (Ne.symm hi)]
        exact (toffoliAt a b t hab hat hbt).liftPerm_wire toffoliPerm x ⟨1,by change 1<3; decide⟩
      · rw [(toffoliAt a b t hab hat hbt).liftPerm_unused toffoliPerm x i (by
          intro j; fin_cases j <;> simpa [toffoliAt] using (by assumption : _))]
        simp [Function.update, Ne.symm hi]

lemma notAt_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (notAt t).matrix.mulVec (basisVector x) = basisVector (Function.update x t (!x t)) := by
  rw [Instruction.liftPerm_basisVector (notAt t) notPerm (by exact not_localMatrix), notAt_lift]

lemma cnotAt_basis {q : ℕ} (c t : Fin q) (hct : c ≠ t) (x : Basis q) :
    (cnotAt c t hct).matrix.mulVec (basisVector x) =
      basisVector (Function.update x t (Bool.xor (x c) (x t))) := by
  rw [Instruction.liftPerm_basisVector (cnotAt c t hct) cnotPerm (by exact cnot_localMatrix), cnotAt_lift]

lemma toffoliAt_basis {q : ℕ} (a b t : Fin q) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (x : Basis q) :
    (toffoliAt a b t hab hat hbt).matrix.mulVec (basisVector x) =
      basisVector (Function.update x t (Bool.xor (x t) (x a && x b))) := by
  rw [Instruction.liftPerm_basisVector (toffoliAt a b t hab hat hbt) toffoliPerm (by exact toffoli_localMatrix), toffoliAt_lift]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanProgram
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil _root_.OAI.ExactQuantumFactoring.cnotAt_target _root_.OAI.ExactQuantumFactoring.notAt_target _root_.OAI.ExactQuantumFactoring.toffoliAt_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

lemma programMatrix_nil {q : ℕ} : programMatrix ([] : List (Instruction q)) = 1 := rfl

lemma programMatrix_cons {q : ℕ} (o : Instruction q) (ops : List (Instruction q)) :
    programMatrix (o :: ops) = programMatrix ops * o.matrix := by
  change ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * 1) = _
  rw [programMatrix_fold, Matrix.mul_one]

lemma programMatrix_singleton {q : ℕ} (o : Instruction q) :
    programMatrix [o] = o.matrix := by
  rw [programMatrix_cons, programMatrix_nil, Matrix.one_mul]

namespace BooleanOp

lemma eval_at {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) :
    o.eval x t = Bool.xor (x t) (o.value x) := Function.update_self _ _ _

lemma eval_away {q : ℕ} {t i : Fin q} (o : BooleanOp q t) (x : Basis q) (hi : i ≠ t) :
    o.eval x i = x i := Function.update_of_ne hi _ _

lemma eval_fresh {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) (ht : x t = false) :
    o.eval x = Function.update x t (o.value x) := by
  simp [eval, ht]

lemma compile_basis {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) :
    (programMatrix o.compile).mulVec (basisVector x) = basisVector (o.eval x) := by
  cases o with
  | constant b =>
    cases b
    · simp [compile, programMatrix_nil, eval, value]
    · rw [compile, programMatrix_singleton, notAt_basis]
      simp [eval, value]
  | copy a ha =>
    rw [compile, programMatrix_singleton, cnotAt_basis]
    simp [eval, value, Bool.xor_comm]
  | neg a ha =>
    rw [compile, programMatrix_cons, programMatrix_singleton, ← Matrix.mulVec_mulVec,
      cnotAt_basis, notAt_basis]
    congr 1
    simp only [Function.update_self, Function.update_idem, eval, value]
    congr 1
    cases x a <;> cases x t <;> rfl
  | conj a b ha hb =>
    simp only [compile]
    split_ifs with hab
    · rw [programMatrix_singleton, cnotAt_basis]
      subst b
      simp [eval, value, Bool.xor_comm]
    · rw [programMatrix_singleton, toffoliAt_basis]
      rfl

end BooleanOp

lemma BooleanProgram.compile_basis {q : ℕ} (p : BooleanProgram q) (x : Basis q) :
    (programMatrix p.compile).mulVec (basisVector x) = basisVector (p.eval x) := by
  induction p generalizing x with
  | nil => simp [compile, eval, programMatrix_nil]
  | cons o p ih =>
    change (programMatrix (o.2.compile ++ BooleanProgram.compile p)).mulVec (basisVector x) = _
    rw [programMatrix_append, ← Matrix.mulVec_mulVec, BooleanOp.compile_basis, ih]
    rfl

/-- Reversing the actual compiled gate list erases the complete retained trace,
not only its output. No irreversible erasure is used. -/
lemma BooleanProgram.uncompute {q : ℕ} (p : BooleanProgram q) (x : Basis q) :
    (programMatrix (p.compile.reverse.map Instruction.reverse)).mulVec
      (basisVector (p.eval x)) = basisVector x := by
  rw [← p.compile_basis x, programMatrix_reverse, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp (programMatrix_unitary _), Matrix.one_mulVec]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanNetwork
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring

namespace BoolNode

lemma eval_map {n m : ℕ} (f : Fin n → Fin m) (o : BoolNode n) (x : Fin m → Bool) :
    (o.map f).eval x = o.eval (x ∘ f) := by cases o <;> rfl

lemma compileOp_value {n q : ℕ} (h : n + 1 ≤ q) (o : BoolNode n) (x : Basis q) :
    (o.compileOp h).value x = o.eval (fun i => x (i.castLE (by omega))) := by
  cases o <;> rfl

end BoolNode

namespace BoolNet

lemma eval_input {n k : ℕ} (p : BoolNet n k) (x : Fin n → Bool) (i : Fin n) :
    p.eval x (i.castLE p.input_le) = x i := by
  induction p with
  | input => rfl
  | add p o ih =>
    have he : i.castLE (p.add o).input_le = (i.castLE p.input_le).castSucc := rfl
    rw [he, eval_add_castSucc, ih]

lemma attach_eval {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l)
    (x : Fin n → Bool) :
    (a.attach ρ b).2.1.eval x ∘ (a.attach ρ b).2.2 = b.eval (a.eval x ∘ ρ) := by
  induction b with
  | input => rfl
  | @add l b o ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [attach, Function.comp_apply, Fin.snoc_last, eval_add_last, BoolNode.eval_map]
      rw [ih]
    · simp only [attach, Function.comp_apply, Fin.snoc_castSucc, eval_add_castSucc]
      exact congrFun ih j

lemma attach_preserve {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l)
    (x : Fin n → Bool) (i : Fin k) :
    (a.attach ρ b).2.1.eval x (i.castLE (a.attach_le ρ b)) = a.eval x i := by
  induction b with
  | input => rfl
  | add b o ih =>
    change ((a.attach ρ b).2.1.add (o.map (a.attach ρ b).2.2)).eval x
      (i.castLE (a.attach_le ρ b)).castSucc = _
    rw [eval_add_castSucc, ih]

end BoolNet


end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanNetworkFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring

namespace BooleanNetwork

lemma eval_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l)
    (x : Fin n → Bool) : (a.comp b).eval x = b.eval (a.eval x) := by
  change ((a.net.attach a.output b.net).2.1.eval x ∘ (a.net.attach a.output b.net).2.2) ∘
    b.output = _
  rw [BoolNet.attach_eval]
  rfl

lemma eval_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l)
    (x : Fin n → Bool) : (a.pair b).eval x = Fin.append (a.eval x) (b.eval x) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [pair, eval, Function.comp_apply, Fin.append_left]
    exact BoolNet.attach_preserve _ _ _ _ _
  · simp only [pair, eval, Function.comp_apply, Fin.append_right]
    have he := congrFun (BoolNet.attach_eval a.net (fun i => i.castLE a.net.input_le) b.net x) (b.output j)
    have hi : a.net.eval x ∘ (fun i : Fin n => i.castLE a.net.input_le) = x := by
      funext j
      exact BoolNet.eval_input _ _ _
    rw [hi] at he
    exact he

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanAlgebra
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.BooleanNetwork

@[simp] lemma eval_bnot {n : ℕ} (a : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    a.bnot.eval x j = !(a.eval x 0) := by simp [bnot, eval_comp, BoolNode.eval]

@[simp] lemma eval_band {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.band b).eval x j = (a.eval x 0 && b.eval x 0) := by
  simp only [band, eval_comp, eval_node, BoolNode.eval, eval_pair]
  rfl

@[simp] lemma eval_bor {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.bor b).eval x j = (a.eval x 0 || b.eval x 0) := by
  simp [bor]

@[simp] lemma eval_bxor {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.bxor b).eval x j = Bool.xor (a.eval x 0) (b.eval x 0) := by
  simp only [bxor, eval_bor, eval_band, eval_bnot]
  cases a.eval x 0 <;> cases b.eval x 0 <;> rfl

@[simp] lemma eval_mux {n : ℕ} (c a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (mux c a b).eval x j = if c.eval x 0 then a.eval x 0 else b.eval x 0 := by
  simp only [mux, eval_bor, eval_band, eval_bnot]
  cases c.eval x 0 <;> simp

lemma eval_assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) (x : Fin n → Bool) :
    (assign i v).eval x = Function.update x i (v.eval x 0) := by
  funext j
  simp only [assign, eval_rewire, Function.comp_apply, eval_pair, eval_select]
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanVector
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


open scoped BigOperators
namespace ExactQuantumFactoring.BooleanNetwork

@[simp] lemma eval_vector {n m : ℕ} (f : Fin m → BooleanNetwork n 1)
    (x : Fin n → Bool) (i : Fin m) : (vector f).eval x i = (f i).eval x 0 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [vector, eval_pair, Fin.append_right_eq_snoc]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc]
      exact ih _ j

lemma eval_padRight (n m : ℕ) (x : Fin n → Bool) :
    (padRight n m).eval x = Fin.append x (fun _ => false) := by
  funext i
  rw [padRight, eval_vector]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [j.isLt]
  · simp

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGCompiler
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

open BooleanNetwork Std.Sat

namespace AIGCompiler

variable {n : ℕ} (g : AIG (Fin n))

lemma fanin_eval (f : AIG.Fanin) (h : f.gate < g.decls.size) (x : Fin (n+g.decls.size) → Bool) :
    (faninNet g f).eval x 0 = Bool.xor (x (graphWire g ⟨f.gate,h⟩)) f.invert := by
  simp only [faninNet, dite_eq_left h]
  cases f.invert <;> simp

lemma node_eval (i : Fin g.decls.size) (x : Fin n → Bool)
    (y : Fin (n+g.decls.size) → Bool)
    (hi : ∀ j, y (j.castAdd g.decls.size) = x j)
    (hg : ∀ j : Fin g.decls.size, j.val < i.val → y (graphWire g j) = nodeDenote g x j) :
    (nodeNet g i).eval y 0 = nodeDenote g x i := by
  unfold nodeNet nodeDenote
  cases h : g.decls[i.val] with
  | false => simpa only [eval_constant] using (AIG.denote_idx_false (assign := x) (invert := false) h).symm
  | atom v => simpa only [eval_bit, hi, Bool.xor_false] using (AIG.denote_idx_atom (assign := x) (invert := false) h).symm
  | gate a b =>
    have hab := g.hdag i.isLt h
    dsimp only
    rw [eval_band, fanin_eval g a (by omega), fanin_eval g b (by omega),
      hg ⟨a.gate, by omega⟩ hab.1, hg ⟨b.gate, by omega⟩ hab.2]
    have he := (AIG.denote_idx_gate (assign := x) (invert := false) h).symm
    simpa only [AIG.denote, nodeDenote, Bool.xor_false] using he

lemma graph_input (k : ℕ) (h : k ≤ g.decls.size) (x : Fin (n+g.decls.size) → Bool) (j : Fin n) :
    (partialGraph g k h).eval x (j.castAdd g.decls.size) = x (j.castAdd g.decls.size) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [partialGraph, eval_comp, nodeStep, eval_assign, Function.update_of_ne, ih]
    intro he
    have := congrArg Fin.val he
    simp [graphWire] at this
    omega

lemma graph_value (k : ℕ) (h : k ≤ g.decls.size) (x : Fin (n+g.decls.size) → Bool)
    (j : Fin g.decls.size) (hj : j.val < k) :
    (partialGraph g k h).eval x (graphWire g j) =
      nodeDenote g (fun i => x (i.castAdd g.decls.size)) j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [partialGraph, eval_comp, nodeStep, eval_assign]
    by_cases hjk : j.val = k
    · have hj' : j = ⟨k, by omega⟩ := Fin.ext hjk
      rw [hj', Function.update_self]
      apply node_eval g
      · exact fun i => graph_input g k (by omega) x i
      · exact fun i hi => ih (by omega) i (by simpa using hi)
    · rw [Function.update_of_ne]
      · exact ih (by omega) j (by omega)
      · intro he
        have := congrArg Fin.val he
        simp [graphWire] at this
        omega

/-- The circuit interpreter's own, already verified, AIG semantics is preserved
by a retained-trace network of at most five nodes per AIG declaration. -/
theorem graph_correct (x : Fin (n+g.decls.size) → Bool) (j : Fin g.decls.size) :
    (partialGraph g g.decls.size le_rfl).eval x (graphWire g j) =
      nodeDenote g (fun i => x (i.castAdd g.decls.size)) j :=
  graph_value g _ le_rfl x j j.isLt

lemma compile_correct {m : ℕ} (refs : Fin m → AIG.Ref g) (x : Fin n → Bool) (i : Fin m) :
    (compile g refs).eval x i = AIG.denote x ⟨g, refs i⟩ := by
  rw [compile, eval_comp, eval_comp, eval_vector, fanin_eval g _ (by simpa using (refs i).hgate),
    graph_correct, eval_padRight]
  have he : (fun j : Fin n => Fin.append x (fun _ : Fin g.decls.size => false)
      (j.castAdd g.decls.size)) = x := by funext j; exact Fin.append_left ..
  rw [he]
  simp only [nodeDenote, AIG.denote, Bool.xor_false, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

lemma compileVec_correct {w : ℕ} (refs : AIG.RefVec g w) (x : Fin n → Bool) (i : Fin w) :
    (compileVec g refs).eval x i = AIG.denote x ⟨g, refs.get i.val i.isLt⟩ :=
  compile_correct ..

end AIGCompiler
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGInputs
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGCompiler
open Std.Sat

lemma inputsPrefix_correct (n k : ℕ) (h : k ≤ n) (x : Fin n → Bool) (i : Fin k) :
    AIG.denote x ⟨(inputsPrefix n k h).1, (inputsPrefix n k h).2 i⟩ = x (i.castLE h) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [inputsPrefix, Fin.snoc_last]
      change AIG.denote x ((inputsPrefix n k (by omega)).1.mkAtom ⟨k, by omega⟩) = _
      rw [AIG.denote_mkAtom]
      rfl
    · simp only [inputsPrefix, Fin.snoc_castSucc]
      rw [AIG.LawfulOperator.denote_cast_entry (f := @AIG.mkAtom (Fin n) _ _)
        (entry := ⟨(inputsPrefix n k (by omega)).1, (inputsPrefix n k (by omega)).2 j⟩)]
      exact ih (by omega) j

lemma inputs_correct (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    AIG.denote x ⟨(inputs n).1, (inputs n).2 i⟩ = x i := inputsPrefix_correct ..

lemma refVector_get {α : Type} [Hashable α] [DecidableEq α] {g : AIG α} {w : ℕ}
    (f : Fin w → AIG.Ref g) (i : ℕ) (hi : i < w) :
    (refVector f).get i hi = f ⟨i,hi⟩ := by
  simp [refVector, AIG.RefVec.get, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

end ExactQuantumFactoring.AIGCompiler


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EncodedStates
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma encodeState_apply {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ : α → ℂ) (x : Basis q) :
    encodeState e ψ x = ∑ a, if x=e a then ψ a else 0 := by
  classical
  simp only [encodeState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVector]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma encodeState_at {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (he : Function.Injective e) (ψ : α → ℂ) (a : α) :
    encodeState e ψ (e a) = ψ a := by
  classical
  rw [encodeState_apply]
  simp [he.eq_iff]

lemma encodeState_basis {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (e : α → Basis q) (a : α) : encodeState e (basisVector a) = basisVector (e a) := by
  classical
  simp [encodeState, basisVector, ite_smul]

lemma encodeState_add {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ χ : α → ℂ) :
    encodeState e (ψ+χ) = encodeState e ψ + encodeState e χ := by
  classical
  simp only [encodeState, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma encodeState_smul {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (c : ℂ) (ψ : α → ℂ) :
    encodeState e (c • ψ) = c • encodeState e ψ := by
  classical
  simp only [encodeState, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma encodeState_sum {α β : Type*} [Fintype α] [Fintype β] {q : ℕ}
    (e : α → Basis q) (ψ : β → α → ℂ) :
    encodeState e (∑ b, ψ b) = ∑ b, encodeState e (ψ b) := by
  classical
  simp only [encodeState, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- A basis-level implementation law extends to every coherent superposition. -/
lemma matrix_encodeState {α β : Type*} [Fintype α] [Fintype β] {p q : ℕ}
    (e : α → Basis p) (f : β → Basis q) (U : Matrix (Basis q) (Basis p) ℂ)
    (V : Matrix β α ℂ)
    (h : ∀ a, U.mulVec (basisVector (e a)) = encodeState f (fun b => V b a))
    (ψ : α → ℂ) : U.mulVec (encodeState e ψ) = encodeState f (V.mulVec ψ) := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, h]
  simp_rw [← encodeState_smul]
  rw [← encodeState_sum]
  congr 1
  funext b
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma matrix_encode_permutation {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (e : α → Basis q) (U : Matrix (Basis q) (Basis q) ℂ) (v : Equiv.Perm α)
    (h : ∀ a, U.mulVec (basisVector (e a)) = basisVector (e (v a)))
    (ψ : α → ℂ) : U.mulVec (encodeState e ψ) = encodeState e (ψ ∘ v.symm) := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, h]
  unfold encodeState
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    Equiv.sum_comp v (fun a => (ψ ∘ v.symm) a • basisVector (e a))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RegisterCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

namespace Register

lemma liftMatrix_one {p q : ℕ} (w : Register p q) : w.liftMatrix 1 = 1 := by
  classical
  rw [liftMatrix, Matrix.one_kronecker_one]
  exact map_one (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm)

lemma liftMatrix_mul {p q : ℕ} (w : Register p q)
    (A B : Matrix (Basis p) (Basis p) ℂ) :
    w.liftMatrix (A * B) = w.liftMatrix A * w.liftMatrix B := by
  classical
  change (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm)
    ((A * B) ⊗ₖ (1 : Matrix (w.Unused → Bool) (w.Unused → Bool) ℂ)) =
    (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm) (A ⊗ₖ 1) *
    (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm) (B ⊗ₖ 1)
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm)]
  congr 1
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

end Register

lemma Instruction.place_matrix {p q : ℕ} (w : Register p q) (o : Instruction p) :
    (o.place w).matrix = w.liftMatrix o.matrix := by
  classical
  ext x y
  let A := ∀ i : Fin q, (∀ j, w (o.wire j) ≠ i) → x i = y i
  let B := ∀ i : Fin p, (∀ j, o.wire j ≠ i) → x (w i) = y (w i)
  let C := (fun i : w.Unused => x i.val) = (fun i : w.Unused => y i.val)
  have he : A ↔ B ∧ C := by
    constructor
    · intro h
      constructor
      · intro i hi
        apply h (w i)
        intro j hh
        exact hi j (w.injective hh)
      · funext i
        apply h i.val
        intro j
        exact i.property (o.wire j)
    · rintro ⟨hB,hC⟩ i hi
      by_cases hh : ∃ j, w j = i
      · obtain ⟨j,rfl⟩ := hh
        exact hB j (fun k hk => hi k (congrArg w hk))
      · exact congrFun hC ⟨i,by simpa only [not_exists] using hh⟩
  change (if A then o.gate.matrix (List.ofFn (x ∘ w ∘ o.wire))
      (List.ofFn (y ∘ w ∘ o.wire)) else 0) =
      (if B then o.gate.matrix (List.ofFn (x ∘ w ∘ o.wire))
        (List.ofFn (y ∘ w ∘ o.wire)) else 0) * if C then 1 else 0
  simp only [he]
  split_ifs <;> simp_all

lemma programMatrix_place {p q : ℕ} (w : Register p q) (ops : List (Instruction p)) :
    programMatrix (ops.map (Instruction.place w)) = w.liftMatrix (programMatrix ops) := by
  induction ops with
  | nil => simp [programMatrix_nil, Register.liftMatrix_one]
  | cons o ops ih =>
    rw [List.map_cons, programMatrix_cons, programMatrix_cons, ih,
      Instruction.place_matrix, Register.liftMatrix_mul]

lemma Register.liftMatrix_pairState {p q : ℕ} (w : Register p q)
    (A : Matrix (Basis p) (Basis p) ℂ) (v : State p) (z : (w.Unused → Bool) → ℂ) :
    (w.liftMatrix A).mulVec (w.pairState v z) = w.pairState (A.mulVec v) z := by
  classical
  ext x
  change (∑ y, (A (w.split x).1 (w.split y).1 *
      if (w.split x).2 = (w.split y).2 then 1 else 0) *
      (v (w.split y).1 * z (w.split y).2)) =
    (∑ u, A (w.split x).1 u * v u) * z (w.split x).2
  rw [← Equiv.sum_comp w.split.symm]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp [Finset.sum_mul, mul_assoc]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RegisterBasis
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil _root_.OAI.ExactQuantumFactoring.cnotAt_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

lemma Register.replace_inside {p q : ℕ} (w : Register p q) (x : Basis q) (y : Basis p)
    (i : Fin p) : w.replace x y (w i) = y i := by
  have h := congrArg Prod.fst (w.split.apply_symm_apply (y, (w.split x).2))
  exact congrFun h i

lemma Register.replace_outside {p q : ℕ} (w : Register p q) (x : Basis q) (y : Basis p)
    (i : w.Unused) : w.replace x y i.val = x i.val := by
  have h := congrArg Prod.snd (w.split.apply_symm_apply (y, (w.split x).2))
  exact congrFun h i

lemma Register.pairState_basis {p q : ℕ} (w : Register p q) (x : Basis q) :
    w.pairState (basisVector (x ∘ w)) (basisVector (w.split x).2) = basisVector x := by
  classical
  funext y
  change (if (w.split y).1 = (w.split x).1 then (1 : ℂ) else 0) *
    (if (w.split y).2 = (w.split x).2 then 1 else 0) = if y = x then 1 else 0
  by_cases hy : y = x
  · subst y; simp
  · have hh : ¬ ((w.split y).1 = (w.split x).1 ∧ (w.split y).2 = (w.split x).2) := by
      intro h; exact hy (w.split.injective (Prod.ext h.1 h.2))
    rcases not_and_or.mp hh with h | h <;> simp [hy,h]

lemma Register.pairState_replace_basis {p q : ℕ} (w : Register p q) (x : Basis q) (v : Basis p) :
    w.pairState (basisVector v) (basisVector (w.split x).2) = basisVector (w.replace x v) := by
  have h := w.pairState_basis (w.replace x v)
  have he : w.split (w.replace x v) = (v, (w.split x).2) := w.split.apply_symm_apply _
  change w.pairState (basisVector (w.split (w.replace x v)).1)
    (basisVector (w.split (w.replace x v)).2) = _ at h
  simpa only [he] using h

lemma placed_basis {p q : ℕ} (w : Register p q) (ops : List (Instruction p))
    (x : Basis q) (v : Basis p)
    (h : (programMatrix ops).mulVec (basisVector (x ∘ w)) = basisVector v) :
    (programMatrix (ops.map (Instruction.place w))).mulVec (basisVector x) =
      basisVector (w.replace x v) := by
  rw [programMatrix_place, ← w.pairState_basis x, w.liftMatrix_pairState, h,
    w.pairState_replace_basis]

lemma swapAt_basis {q : ℕ} (a b : Fin q) (h : a ≠ b) (x : Basis q) :
    (programMatrix (swapAt a b h)).mulVec (basisVector x) =
      basisVector (x ∘ Equiv.swap a b) := by
  rw [swapAt, programMatrix_cons, programMatrix_cons, programMatrix_singleton,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    cnotAt_basis, cnotAt_basis, cnotAt_basis]
  congr 1
  funext i
  by_cases ha : i = a
  · subst i; simp only [Function.comp_apply, Function.update_self,
      Function.update_of_ne h, Function.update_of_ne h.symm, Equiv.swap_apply_left]
    cases x a <;> cases x b <;> rfl
  · by_cases hb : i = b
    · subst i; simp [Function.comp_apply, h, h.symm]
    · simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne ha hb,
        Function.update_of_ne ha, Function.update_of_ne hb]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RegisterEncoded
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma Register.placed_basis_state {p q : ℕ} (w : Register p q)
    (ops : List (Instruction p)) (x : Basis q) :
    (programMatrix (ops.map (Instruction.place w))).mulVec (basisVector x) =
      encodeState (w.replace x) ((programMatrix ops).mulVec (basisVector (x ∘ w))) := by
  classical
  rw [programMatrix_place, ← w.pairState_basis x, w.liftMatrix_pairState]
  unfold encodeState
  simp_rw [← w.pairState_replace_basis]
  funext y
  simp only [Register.pairState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    basisVector]
  simp

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AppendRegister
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma append_rightRegister {p q : ℕ} (x : Basis p) (y : Basis q) :
    Fin.append x y ∘ rightRegister p q = y := by
  funext i
  exact Fin.append_right _ _ i

lemma append_right_injective {p q : ℕ} (x : Basis p) :
    Function.Injective (Fin.append x : Basis q → Basis (p+q)) := by
  intro y z h
  have hh := congrArg (fun v => v ∘ rightRegister p q) h
  simpa only [append_rightRegister] using hh

lemma append_replace_right {p q : ℕ} (x : Basis p) (y z : Basis q) :
    (rightRegister p q).replace (Fin.append x y) z = Fin.append x z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hj : ∀ k, rightRegister p q k ≠ j.castAdd q := by
      intro k h
      have hh := congrArg Fin.val h
      change p+k.val=j.val at hh
      have := j.isLt
      omega
    rw [Register.replace_outside _ _ _ ⟨j.castAdd q,hj⟩]
    simp only [Fin.append_left]
  · change (rightRegister p q).replace (Fin.append x y) z (rightRegister p q j) = _
    rw [Register.replace_inside,Fin.append_right]

lemma rightProgram_basis {p q : ℕ} (ops : List (Instruction q)) (x : Basis p) (y : Basis q) :
    (programMatrix (rightProgram p ops)).mulVec (basisVector (Fin.append x y)) =
      encodeState (Fin.append x) ((programMatrix ops).mulVec (basisVector y)) := by
  rw [rightProgram,Register.placed_basis_state,append_rightRegister]
  congr 1
  funext z
  exact append_replace_right x y z

lemma rightProgram_entry {p q : ℕ} (ops : List (Instruction q)) (x : Basis p) (y z : Basis q) :
    programMatrix (rightProgram p ops) (Fin.append x z) (Fin.append x y) =
      programMatrix ops z y := by
  have hh := congrFun (rightProgram_basis ops x y) (Fin.append x z)
  simpa only [encodeState_at _ (append_right_injective x),matrix_basisVector] using hh

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QuantumCore
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Exact integer arithmetic for the prescribed-mass order trial.
These are dependencies of the actual main theorem, not assumptions about an
unknown order and not a replacement target. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators

lemma sampleCount_bounds {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    Q ≤ t+sampleCount Q d t*d ∧ t+sampleCount Q d t*d ≤ Q+d := by
  have htQ : t < Q := lt_of_lt_of_le ht hdQ
  have hr := Nat.mod_lt (Q-1-t) hd
  have heq : (Q-1-t)%d + ((Q-1-t)/d)*d = Q-1-t := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div (Q-1-t) d
  unfold sampleCount
  rw [Nat.add_mul, one_mul]
  omega

lemma lt_sampleCount_iff {Q d t i : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    i < sampleCount Q d t ↔ t+i*d < Q := by
  have htQ : t < Q := lt_of_lt_of_le ht hdQ
  unfold sampleCount
  rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
  omega

lemma sum_progression {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    (∑ i ∈ Finset.range (sampleCount Q d t), f (t+i*d)) =
      ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t), f x := by
  apply Finset.sum_bij (fun i _ => t+i*d)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at *
    refine ⟨(lt_sampleCount_iff hd hdQ ht).mp hi, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  · intro i hi j hj heq
    exact Nat.mul_right_cancel hd (Nat.add_left_cancel heq)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have heq : t+(x/d)*d=x := by
      have h := Nat.mod_add_div x d
      rw [hx.2] at h
      simpa only [Nat.mul_comm] using h
    refine ⟨x/d, ?_, heq⟩
    rw [Finset.mem_range, lt_sampleCount_iff hd hdQ ht, heq]
    exact hx.1
  · intro i hi
    rfl

lemma binError_bound {Q d j : ℕ} (hd : 0 < d) : |binError Q d j| ≤ 1/2 := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have h₁ : bin Q d j*(2*d) ≤ 2*j*Q+d := Nat.div_mul_le_self _ _
  have h₂ : 2*j*Q+d < (bin Q d j+1)*(2*d) := by
    have hr := Nat.mod_lt (2*j*Q+d) (by omega : 0 < 2*d)
    have heq := Nat.mod_add_div (2*j*Q+d) (2*d)
    change (2*j*Q+d)%(2*d) + (2*d)*bin Q d j = 2*j*Q+d at heq
    nlinarith
  have h₁' : (bin Q d j:ℝ)*(2*d) ≤ 2*j*Q+d := by exact_mod_cast h₁
  have h₂' : (2:ℝ)*j*Q+d < ((bin Q d j:ℝ)+1)*(2*d) := by exact_mod_cast h₂
  have heq : binError Q d j*(d:ℝ) = (bin Q d j:ℝ)*d-(j:ℝ)*Q := by
    rw [binError, sub_mul, div_mul_cancel₀ _ hd'.ne']
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_left₀ hd').mp
    nlinarith
  · apply (mul_le_mul_iff_left₀ hd').mp
    nlinarith

end ExactQuantumFactoring.OrderTrial



/-! Dependencies for the actual prescribed-probability order trial.
The phase below is proved to be exactly the quarter-linear interpolant in
sections/03-order-transform.tex. No oracle/order information is input. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators
open MeasureTheory intervalIntegral

lemma triangle_local {x : ℝ} (h : |x| ≤ 1/2) : triangle x = 1 - 4 * |x| := by
  unfold triangle
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by simpa using h)]

lemma triangle_add_int (x : ℝ) (k : ℤ) : triangle (x + k) = triangle x := by
  simp only [triangle, UnitAddCircle.norm_eq, round_add_intCast, Int.cast_add]
  congr 2
  ring_nf

lemma triangle_half (x : ℝ) : triangle (x + 1/2) = -triangle x := by
  let y : ℝ := x - round x
  have hy : |y| ≤ 1/2 := abs_sub_round x
  have hx : x = y + round x := by dsimp [y] <;> ring
  rw [hx]
  rw [show y + (round x : ℝ) + 1/2 = (y+1/2) + round x by ring,
    triangle_add_int, triangle_add_int]
  rcases le_total y 0 with hneg | hpos
  · have hy' : |y + 1/2| ≤ 1/2 := by rw [abs_le] at hy ⊢; constructor <;> linarith
    rw [triangle_local hy, triangle_local hy', abs_of_nonpos hneg,
      abs_of_nonneg (by have := (abs_le.mp hy).1; linarith : 0 ≤ y+1/2)]
    ring
  · have hy' : |y - 1/2| ≤ 1/2 := by rw [abs_le] at hy ⊢; constructor <;> linarith
    rw [show y+1/2 = (y-1/2) + (1 : ℤ) by norm_num; ring,
      triangle_add_int, triangle_local hy, triangle_local hy', abs_of_nonneg hpos,
      abs_of_nonpos (by have := (abs_le.mp hy).2; linarith : y-1/2 ≤ 0)]
    ring

lemma triangle_continuous : Continuous triangle := by
  exact continuous_const.sub (continuous_const.mul
    (AddCircle.continuous_mk' (1 : ℝ)).norm)

lemma phase_continuous : Continuous phase := by
  have h := (Complex.continuous_ofReal.comp triangle_continuous).sub
    ((Complex.continuous_ofReal.comp
      (triangle_continuous.comp (continuous_id.sub (continuous_const (y := (1/4 : ℝ)))))).mul
      (continuous_const (y := Complex.I)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  apply Complex.ext <;> simp [phase]

lemma phase_quarter (x : ℝ) : phase (x + 1/4) = -Complex.I * phase x := by
  have h := triangle_half (x - 1/4)
  rw [show x-1/4+1/2 = x+1/4 by ring] at h
  apply Complex.ext
  · simpa only [phase, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] using h
  · simp only [phase, neg_mul, Complex.neg_im, Complex.I_mul_im]
    congr 2
    ring

lemma phase_add_int (x : ℝ) (k : ℤ) : phase (x + k) = phase x := by
  apply Complex.ext
  · exact triangle_add_int _ _
  · change -triangle (x + k - 1/4) = -triangle (x-1/4)
    rw [show x + k - 1/4 = (x-1/4)+k by ring, triangle_add_int]

lemma phase_zero_quarter {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phase (t/4) = (1-t : ℂ) + (t : ℂ) * (-Complex.I) := by
  have ha : |t/4| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  have hb : |t/4-1/4| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  apply Complex.ext
  · change triangle (t/4) = _
    rw [triangle_local ha, abs_of_nonneg (by positivity : 0 ≤ t/4)]
    simp
    ring
  · change -triangle (t/4-1/4) = _
    rw [triangle_local hb, abs_of_nonpos (by linarith : t/4-1/4 ≤ 0)]
    simp
    ring

lemma triangle_quadratic_lower (x : ℝ) : 1/2 - 8*x^2 ≤ triangle x := by
  have hn : ‖(x : UnitAddCircle)‖ ≤ |x| := by
    rw [UnitAddCircle.norm_eq]
    simpa using round_le x 0
  have hs := sq_nonneg (|x| - 1/4)
  rw [triangle]
  nlinarith [sq_abs x]

lemma phase_add_quarters (x : ℝ) (q : ℤ) :
    phase (x + (q : ℝ)/4) = (-Complex.I)^q * phase x := by
  have hi : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  induction q using Int.induction_on with
  | zero => simp
  | succ q ih =>
      simp only [Int.cast_natCast] at ih
      rw [Int.cast_add, Int.cast_natCast, Int.cast_one,
        show x + ((q : ℝ) + 1)/4 = (x + (q : ℝ)/4) + 1/4 by ring,
        phase_quarter, ih, zpow_add₀ hi]
      simp only [zpow_one]
      ring
  | pred q ih =>
      have h := phase_quarter (x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4)
      rw [show x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4 + 1/4 =
          x + ((-(q : ℤ) : ℤ) : ℝ)/4 by push_cast; ring, ih] at h
      calc
        phase (x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4) =
            (-Complex.I)⁻¹ * ((-Complex.I)^(-(q : ℤ)) * phase x) := by
          rw [h, ← mul_assoc, inv_mul_cancel₀ hi, one_mul]
        _ = (-Complex.I)^(-(q : ℤ)-1) * phase x := by
          rw [show -(q : ℤ)-1 = -(q : ℤ)+(-1) by ring,
            zpow_add₀ hi, zpow_neg_one]
          ring

lemma phase_interpolates (q : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phase (((q : ℝ)+t)/4) = (1-t : ℂ)*(-Complex.I)^q +
      (t : ℂ)*(-Complex.I)^(q+1) := by
  rw [show ((q : ℝ)+t)/4 = t/4 + (q : ℝ)/4 by ring,
    phase_add_quarters, phase_zero_quarter ht0 ht1,
    zpow_add₀ (neg_ne_zero.mpr Complex.I_ne_zero)]
  simp only [zpow_one]
  ring

lemma phase_norm_le (x : ℝ) : ‖phase x‖ ≤ 1 := by
  let q : ℤ := ⌊4*x⌋
  let t : ℝ := 4*x-q
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Int.floor_le _)
  have ht1 : t ≤ 1 := by
    have h := Int.lt_floor_add_one (4*x)
    change 4*x - (⌊4*x⌋ : ℝ) ≤ 1
    linarith
  have hx : x = ((q : ℝ)+t)/4 := by dsimp [t] <;> ring
  rw [hx, phase_interpolates q ht0 ht1]
  calc
    _ ≤ ‖(1-t : ℂ)*(-Complex.I)^q‖ + ‖(t : ℂ)*(-Complex.I)^(q+1)‖ := norm_add_le _ _
    _ = 1 := by
      simp only [norm_mul, norm_zpow, norm_neg, Complex.norm_I, one_zpow, mul_one,
        ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]
      ring

lemma triangle_sub_le (x y : ℝ) : |triangle x - triangle y| ≤ 4*|x-y| := by
  have h₁ := abs_norm_sub_norm_le (x : UnitAddCircle) (y : UnitAddCircle)
  have h₂ : ‖(x : UnitAddCircle) - (y : UnitAddCircle)‖ ≤ |x-y| := by
    rw [← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq]
    simpa using round_le (x-y) 0
  have heq : triangle x - triangle y =
      -4 * (‖(x : UnitAddCircle)‖ - ‖(y : UnitAddCircle)‖) := by
    unfold triangle
    ring
  rw [heq, abs_mul]
  norm_num
  linarith

lemma phase_norm_sub_le (x y : ℝ) : ‖phase x-phase y‖ ≤ 8*|x-y| := by
  have h := Complex.norm_le_abs_re_add_abs_im (phase x-phase y)
  simp only [phase, Complex.sub_re, Complex.sub_im] at h
  rw [show -triangle (x-1/4) - -triangle (y-1/4) =
    -(triangle (x-1/4)-triangle (y-1/4)) by ring, abs_neg] at h
  have h₁ := triangle_sub_le x y
  have h₂ := triangle_sub_le (x-1/4) (y-1/4)
  rw [show (x-1/4)-(y-1/4) = x-y by ring] at h₂
  unfold phase
  linarith

lemma segment_phase_sub_le (a : ℝ) {η : ℝ} (hη : |η| ≤ 1/2) (v w : ℝ) :
    ‖phase (a+η*v)-phase (a+η*w)‖ ≤ 4*|v-w| := by
  have h := phase_norm_sub_le (a+η*v) (a+η*w)
  rw [show (a+η*v)-(a+η*w) = η*(v-w) by ring, abs_mul] at h
  nlinarith [abs_nonneg (v-w)]

lemma centered_quadratic_integral (c η : ℝ) :
    (∫ v in (0 : ℝ)..1, (1/2 - 8*(c+η*(v-1/2))^2)) =
      1/2 - 8*c^2 - (2/3)*η^2 := by
  have heq : (fun v : ℝ => 1/2 - 8*(c+η*(v-1/2))^2) =
      (fun v => (1/2-8*c^2+8*c*η-2*η^2) +
        (-16*c*η+8*η^2)*v + (-8*η^2)*v^2) := by
    funext v; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    norm_num
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma centered_integral_re_lower {c η : ℝ} (hc : |c| ≤ 1/8) (hη : |η| ≤ 1/2) :
    5/24 ≤ (∫ v in (0 : ℝ)..1, phase (c+η*(v-1/2))).re := by
  have hf : Continuous (fun v : ℝ => phase (c+η*(v-1/2))) :=
    phase_continuous.comp (by fun_prop)
  have hq : Continuous (fun v : ℝ => 1/2-8*(c+η*(v-1/2))^2) := by fun_prop
  have h := integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hq.intervalIntegrable _ _) ((Complex.continuous_re.comp hf).intervalIntegrable _ _)
    (fun v _ => triangle_quadratic_lower (c+η*(v-1/2)))
  rw [centered_quadratic_integral] at h
  change 1/2-8*c^2-(2/3)*η^2 ≤
    ∫ v in (0:ℝ)..1, Complex.reCLM (phase (c+η*(v-1/2))) at h
  rw [Complex.reCLM.intervalIntegral_comp_comm (hf.intervalIntegrable _ _)] at h
  change 1/2-8*c^2-(2/3)*η^2 ≤
    (∫ v in (0:ℝ)..1, phase (c+η*(v-1/2))).re at h
  have hc2 : c^2 ≤ (1/8 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg c) (by norm_num)).2 hc
  have hη2 : η^2 ≤ (1/2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg η) (by norm_num)).2 hη
  nlinarith [sq_abs c, sq_abs η]

lemma averagePhase_lower (a : ℝ) {η : ℝ} (hη : |η| ≤ 1/2) :
    (1/8 : ℝ) ≤ ‖averagePhase a η‖ := by
  let q : ℤ := round (4*(a+η/2))
  let c : ℝ := a+η/2-(q : ℝ)/4
  have hc : |c| ≤ 1/8 := by
    have h := abs_sub_round (4*(a+η/2))
    have hc4 : 4*c = 4*(a+η/2)-q := by dsimp [c] <;> ring
    rw [← hc4, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4)] at h
    linarith
  have hf : (fun v : ℝ => phase (a+η*v)) =
      (fun v => (-Complex.I)^q * phase (c+η*(v-1/2))) := by
    funext v
    rw [← phase_add_quarters]
    congr 1
    dsimp [c]
    ring
  have hn : ‖averagePhase a η‖ = ‖∫ v in (0:ℝ)..1, phase (c+η*(v-1/2))‖ := by
    unfold averagePhase
    rw [hf, intervalIntegral.integral_const_mul, norm_mul, norm_zpow]
    simp
  rw [hn]
  calc
    (1/8 : ℝ) ≤ 5/24 := by norm_num
    _ ≤ (∫ v in (0:ℝ)..1, phase (c+η*(v-1/2))).re := centered_integral_re_lower hc hη
    _ ≤ _ := Complex.re_le_norm _

lemma averagePhase_upper (a η : ℝ) : ‖averagePhase a η‖ ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (fun v _ => phase_norm_le (a+η*v))
  simpa only [averagePhase, sub_zero, abs_one, mul_one] using h

lemma residueIntegral_bounds {d : ℕ} (hd : 0 < d) (u : ℝ) {η : ℝ}
    (hη : |η| ≤ 1/2) :
    1/(8*d : ℝ) ≤ ‖residueIntegral d u η‖ ∧ ‖residueIntegral d u η‖ ≤ 1/d := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn : ‖residueIntegral d u η‖ = (d : ℝ)⁻¹ * ‖averagePhase (u/d) η‖ := by
    rw [residueIntegral, norm_mul, norm_inv, Complex.norm_natCast]
  rw [hn]
  constructor
  · have h := mul_le_mul_of_nonneg_left (averagePhase_lower (u/d) hη)
      (inv_nonneg.mpr hd'.le)
    simpa only [one_div, mul_inv_rev] using h
  · simpa only [mul_one, one_div] using
      mul_le_mul_of_nonneg_left (averagePhase_upper (u/d) η) (inv_nonneg.mpr hd'.le)

/-- Quantitative rectangle rule with exactly the constant required in
(majorant-integral-bounds). -/
lemma rectangle_error {f : ℝ → ℂ} (hf : Continuous f)
    (hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w|) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ‖h • f a - ∫ v in a..a+h, f v‖ ≤ 2*h^2 := by
  have heq : (∫ v in a..a+h, (f a-f v)) = h • f a - ∫ v in a..a+h, f v := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), intervalIntegral.integral_const]
    congr 1
    ring_nf
  rw [← heq]
  calc
    _ ≤ ∫ v in a..a+h, ‖f a-f v‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ v in a..a+h, 4*(v-a) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_const.sub hf).norm.intervalIntegrable _ _)
        ((show Continuous (fun v : ℝ => 4*(v-a)) by fun_prop).intervalIntegrable _ _)
      intro v hv
      have h₁ := hL a v
      rw [abs_of_nonpos (by linarith [hv.1] : a-v ≤ 0)] at h₁
      change ‖f a-f v‖ ≤ 4*(v-a)
      linarith
    _ = 2*h^2 := by
      rw [intervalIntegral.integral_const_mul]
      have hir : (∫ v in a..a+h, (v-a)) =
          (∫ v in a..a+h, v) - ∫ _ in a..a+h, a :=
        intervalIntegral.integral_sub (f := fun v : ℝ => v) (g := fun _ => a)
          (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      rw [hir, integral_id, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

lemma rectangle_sum_error {f : ℝ → ℂ} (hf : Continuous f)
    (hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w|) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (M : ℕ) :
    ‖h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in a..a+M*h, f v‖ ≤
      M*(2*h^2) := by
  have hInt₀ := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (μ := volume) (a := fun i : ℕ => a+(i:ℝ)*h) (n := M)
    (fun i _ => hf.intervalIntegrable _ _)
  have hInt : (∑ i ∈ Finset.range M, ∫ v in (a+(i:ℝ)*h)..(a+((i:ℝ)+1)*h), f v) =
      ∫ v in a..a+M*h, f v := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] using hInt₀
  rw [← hInt, Finset.smul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range M,
        ‖h • f (a+i*h) - ∫ v in (a+i*h)..(a+(i+1)*h), f v‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range M, (2*h^2) := by
      apply Finset.sum_le_sum
      intro i _
      have hr := rectangle_error hf hL (a+(i:ℝ)*h) hh
      simpa only [show a+(i:ℝ)*h+h = a+((i:ℝ)+1)*h by ring] using hr
    _ = M*(2*h^2) := by simp

lemma integral_endpoint_error {f : ℝ → ℂ} (hf : Continuous f)
    (hb : ∀ v, ‖f v‖ ≤ 1) {a b : ℝ} (ha : 0 ≤ a) (hb₁ : 1 ≤ b) :
    ‖(∫ v in a..b, f v) - ∫ v in (0:ℝ)..1, f v‖ ≤ a+(b-1) := by
  have heq : (∫ v in a..b, f v) - ∫ v in (0:ℝ)..1, f v =
      (∫ v in (1:ℝ)..b, f v) - ∫ v in (0:ℝ)..a, f v := by
    have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
    have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 1) (hf.intervalIntegrable 1 b)
    linear_combination h₁ - h₂
  rw [heq]
  have h₁ := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1:ℝ)) (b := b) (fun v _ => hb v)
  have h₂ := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := a) (fun v _ => hb v)
  rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hb₁)] at h₁
  rw [one_mul, sub_zero, abs_of_nonneg ha] at h₂
  calc
    _ ≤ ‖∫ v in (1:ℝ)..b, f v‖ + ‖∫ v in (0:ℝ)..a, f v‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma rectangle_sum_unit_error {f : ℝ → ℂ} (hf : Continuous f)
    (hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w|) (hb : ∀ v, ‖f v‖ ≤ 1)
    {a h : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1) (ha₀ : 0 ≤ a) (ha₁ : a ≤ h)
    (M : ℕ) (hM₀ : 1 ≤ a+M*h) (hM₁ : a+M*h ≤ 1+h) :
    ‖h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in (0:ℝ)..1, f v‖ ≤ 6*h := by
  have h₁ := rectangle_sum_error hf hL a hh₀ M
  have h₂ := integral_endpoint_error hf hb ha₀ hM₀
  have hsplit : h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in (0:ℝ)..1, f v =
      (h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in a..a+M*h, f v) +
      ((∫ v in a..a+M*h, f v) - ∫ v in (0:ℝ)..1, f v) := by abel
  rw [hsplit]
  calc
    _ ≤ ‖h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in a..a+M*h, f v‖ +
      ‖(∫ v in a..a+M*h, f v) - ∫ v in (0:ℝ)..1, f v‖ := norm_add_le _ _
    _ ≤ M*(2*h^2) + a+(a+M*h-1) := by linarith
    _ ≤ 6*h := by
      have h₃ : (M:ℝ)*h ≤ 1+h := by linarith
      have h₄ := mul_le_mul_of_nonneg_right h₃ hh₀
      nlinarith [mul_nonneg hh₀ (sub_nonneg.mpr hh₁)]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionRecovery
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.OrderTrial.binErrorRat_cast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded Euclidean recovery of the manuscript's nearest-bin labels.
The denominator bound is logarithmic, never a search through B labels. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma euclidConvergent_zero_pair (k : ℕ) : ∀ b,
    euclidConvergent 0 b k=0 ∧ euclidConvergent b 0 k=0 := by
  induction k with
  | zero => intro b; simp [euclidConvergent]
  | succ k ih =>
    intro b
    constructor <;> simp [euclidConvergent,(ih b).1,(ih b).2]

lemma euclidConvergent_zero_right (a k : ℕ) : euclidConvergent a 0 k=0 :=
  (euclidConvergent_zero_pair k a).2

lemma real_floor_ratio (a b : ℕ) : ⌊(a:ℝ)/b⌋ = ((a/b:ℕ):ℤ) := by
  have hf := Rat.floor_cast (α:=ℝ) ((a:ℚ)/b)
  simp only [Rat.cast_div,Rat.cast_natCast] at hf
  rw [hf,Rat.floor_natCast_div_natCast]
  norm_cast

lemma euclidConvergent_real (a b k : ℕ) :
    euclidConvergent a b k = Real.convergent ((a:ℝ)/b) k := by
  induction k generalizing a b with
  | zero =>
    simp only [euclidConvergent,Real.convergent_zero,real_floor_ratio]
    norm_cast
  | succ k ih =>
    rw [euclidConvergent,Real.convergent_succ,real_floor_ratio,
      Int.fract_div_natCast_eq_div_natCast_mod,inv_div,← ih]
    congr 1

lemma ratio_euclid (a b : ℕ) :
    (a:ℚ)/b = (a/b:ℕ)+((b:ℚ)/((a%b:ℕ):ℚ))⁻¹ := by
  have h := Int.floor_add_fract ((a:ℚ)/b)
  rw [Rat.floor_natCast_div_natCast,Int.fract_div_natCast_eq_div_natCast_mod] at h
  simpa only [Int.cast_natCast,← Int.natCast_ediv,inv_div] using h.symm

/-- Two Euclidean steps halve the denominator; the zero remainder is treated
separately, since natural remainder by zero is not zero. -/
lemma euclid_two_halving {b r : ℕ} (hr : 0 < r) (hrb : r<b) : 2*(b%r)<b := by
  by_cases h : 2*r ≤ b
  · have hm := Nat.mod_lt b hr
    omega
  · have hb : b<2*r := by omega
    have hmod : b%r=b-r := by
      apply Nat.mod_eq_sub_mod hrb.le |>.trans
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

/-- At most twice the denominator bit bound suffices, including rational
termination and all later convergents. -/
lemma euclidConvergent_terminal (s a b h : ℕ) (hb : b<2^s) :
    euclidConvergent a b (2*s+h) = (a:ℚ)/b := by
  induction s generalizing a b h with
  | zero =>
    have : b=0 := by simpa using hb
    subst b
    simp [euclidConvergent_zero_right]
  | succ s ih =>
    by_cases hb0 : b=0
    · subst b
      simp [euclidConvergent_zero_right]
    have hbpos : 0<b := Nat.pos_of_ne_zero hb0
    by_cases h0 : a%b=0
    · have he : 2*(s+1)+h = (2*s+h+1)+1 := by omega
      rw [he,euclidConvergent,h0,euclidConvergent_zero_right,inv_zero,add_zero]
      simpa [h0] using (ratio_euclid a b).symm
    · have hr : 0<a%b := Nat.pos_of_ne_zero h0
      have hh := euclid_two_halving hr (Nat.mod_lt a hbpos)
      have hb' : b%(a%b)<2^s := by
        rw [pow_succ] at hb
        omega
      have he : 2*(s+1)+h = (2*s+h+1)+1 := by omega
      rw [he,euclidConvergent,euclidConvergent,ih _ _ h hb']
      rw [← ratio_euclid b (a%b),← ratio_euclid a b]

/-- Every possible convergent is already in this polynomial-size list. -/
lemma euclidConvergent_bounded {s a b k : ℕ} (hb : b<2^s) :
    ∃ i ≤ 2*s, euclidConvergent a b k = euclidConvergent a b i := by
  by_cases hk : k≤2*s
  · exact ⟨k,hk,rfl⟩
  · refine ⟨2*s,le_rfl,?_⟩
    obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hk)
    rw [euclidConvergent_terminal s a b h hb]
    simpa using (euclidConvergent_terminal s a b 0 hb).symm

lemma bin_error_div {Q d j : ℕ} (hd : 0<d) (hQ : 0<Q) :
    |(bin Q d j:ℝ)/Q-(j:ℝ)/d| ≤ 1/(2*(Q:ℝ)) := by
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have he : (bin Q d j:ℝ)/Q-(j:ℝ)/d = binError Q d j/(Q:ℝ) := by
    unfold binError
    field_simp
  rw [he,abs_div,abs_of_pos hQ',div_le_iff₀ hQ']
  have hh : 1/(2*(Q:ℝ))*(Q:ℝ)=1/2 := by field_simp
  rw [hh]
  exact binError_bound hd

/-- Legendre recovery with an explicit O(log Q) search bound. -/
lemma bin_has_bounded_convergent {Q d j s : ℕ}
    (hd : 0<d) (hQ : d^2<Q) (hsize : Q<2^s) (hcop : Nat.Coprime j d) :
    ∃ i ≤ 2*s, euclidConvergent (bin Q d j) Q i = (j:ℚ)/d := by
  have hdq : ((j:ℚ)/d).den=d := by
    have hh := Rat.den_div_eq_of_coprime (a:=(j:ℤ)) (b:=(d:ℤ))
      (by exact_mod_cast hd) (by simpa using hcop)
    apply Int.ofNat_inj.mp
    simpa only [Int.cast_natCast] using hh
  have hQ0 : 0<Q := lt_of_le_of_lt (Nat.zero_le _) hQ
  have ha := bin_error_div (j:=j) hd hQ0
  have hs : 1/(2*(Q:ℝ)) < 1/(2*(d:ℝ)^2) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · have hh : (d:ℝ)^2<(Q:ℝ) := by exact_mod_cast hQ
      linarith
  obtain ⟨k,hk⟩ := Real.exists_rat_eq_convergent
    (ξ:=(bin Q d j:ℝ)/Q) (q:=(j:ℚ)/d) (by
      simpa only [hdq,Rat.cast_div,Rat.cast_natCast] using ha.trans_lt hs)
  rw [← euclidConvergent_real] at hk
  obtain ⟨i,hi,hei⟩ := euclidConvergent_bounded (k:=k) hsize
  exact ⟨i,hi,hei.symm.trans hk.symm⟩


lemma bin_mul_bounds {Q d j : ℕ} (hd : 0<d) :
    2*bin Q d j*d ≤ 2*j*Q+d ∧ 2*j*Q ≤ 2*bin Q d j*d+d := by
  have h₁ : bin Q d j*(2*d) ≤ 2*j*Q+d := Nat.div_mul_le_self _ _
  have h₂ : 2*j*Q+d < (bin Q d j+1)*(2*d) := by
    have hr := Nat.mod_lt (2*j*Q+d) (by omega : 0<2*d)
    have he := Nat.mod_add_div (2*j*Q+d) (2*d)
    change (2*j*Q+d)%(2*d)+(2*d)*bin Q d j=2*j*Q+d at he
    nlinarith
  constructor <;> nlinarith

lemma bin_lt {Q d j : ℕ} (hd : 0<d) (hdQ : d≤Q) (hj : j<d) : bin Q d j<Q := by
  unfold bin
  apply (Nat.div_lt_iff_lt_mul (by omega : 0<2*d)).2
  have hh := Nat.mul_le_mul_right (2*Q) (show j+1≤d by omega)
  nlinarith

lemma same_bin_cross {Q d e j i : ℕ} (hd : 0<d) (he : 0<e)
    (hQ : d*e<Q) (hbin : bin Q d j=bin Q e i) : j*e=i*d := by
  obtain ⟨hd₁,hd₂⟩ := bin_mul_bounds (Q:=Q) (j:=j) hd
  obtain ⟨he₁,he₂⟩ := bin_mul_bounds (Q:=Q) (j:=i) he
  rw [← hbin] at he₁ he₂
  have hde₁ := Nat.mul_le_mul_right e hd₁
  have hde₂ := Nat.mul_le_mul_right e hd₂
  have hed₁ := Nat.mul_le_mul_right d he₁
  have hed₂ := Nat.mul_le_mul_right d he₂
  apply le_antisymm
  · by_contra hh
    have hh' : i*d+1≤j*e := by omega
    have hh'' := Nat.mul_le_mul_right (2*Q) hh'
    nlinarith
  · by_contra hh
    have hh' : j*e+1 ≤ i*d := by omega
    have hh'' := Nat.mul_le_mul_right (2*Q) hh'
    nlinarith

lemma same_bin_unique {Q d e j i : ℕ} (hd : 0<d) (he : 0<e)
    (hQ : d*e<Q) (hj : Nat.Coprime j d) (hi : Nat.Coprime i e)
    (hbin : bin Q d j=bin Q e i) : d=e ∧ j=i := by
  have hc := same_bin_cross hd he hQ hbin
  have heq : (j:ℚ)/d=(i:ℚ)/e := by
    apply (div_eq_div_iff (by positivity : (d:ℚ)≠0) (by positivity : (e:ℚ)≠0)).2
    exact_mod_cast hc
  have hh := Rat.div_int_inj (a:=(j:ℤ)) (b:=(d:ℤ)) (c:=(i:ℤ)) (d:=(e:ℤ))
    (by exact_mod_cast hd) (by exact_mod_cast he)
    (by simpa using hj) (by simpa using hi) (by simpa only [Int.cast_natCast] using heq)
  exact ⟨Int.ofNat_inj.mp hh.2,Int.ofNat_inj.mp hh.1⟩

lemma rationalLabel_reduced {d j : ℕ} (hd : 0<d) (hcop : Nat.Coprime j d) :
    rationalLabel ((j:ℚ)/d)=(d,j) := by
  have hn := Rat.num_div_eq_of_coprime (a:=(j:ℤ)) (b:=(d:ℤ))
    (by exact_mod_cast hd) (by simpa using hcop)
  have hd' := Rat.den_div_eq_of_coprime (a:=(j:ℤ)) (b:=(d:ℤ))
    (by exact_mod_cast hd) (by simpa using hcop)
  apply Prod.ext
  · apply Int.ofNat_inj.mp
    simpa only [rationalLabel,Int.cast_natCast] using hd'
  · simp only [rationalLabel,Int.cast_natCast] at hn ⊢
    rw [hn,Int.toNat_natCast]

lemma mem_recoveredLabels {s Q B k : ℕ} {l : ℕ×ℕ} :
    l ∈ recoveredLabels s Q B k ↔
      IsBinLabel Q B k l ∧ ∃ i≤2*s, rationalLabel (euclidConvergent k Q i)=l := by
  simp only [recoveredLabels,List.mem_filter,List.mem_map,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i,hi,he⟩,hl⟩
    exact ⟨hl,i,by omega,he⟩
  · rintro ⟨hl,i,hi,he⟩
    exact ⟨⟨i,by omega,he⟩,hl⟩

lemma recoveredLabels_complete {s Q B k d j : ℕ}
    (hQ : B^2≤Q) (hsize : Q<2^s) (hl : IsBinLabel Q B k (d,j)) :
    (d,j) ∈ recoveredLabels s Q B k := by
  obtain ⟨hd,hdB,hjd,hcop,hbin⟩ := hl
  have hdQ : d^2<Q := by nlinarith
  obtain ⟨i,hi,he⟩ := bin_has_bounded_convergent hd hdQ hsize hcop
  apply mem_recoveredLabels.mpr
  refine ⟨⟨hd,hdB,hjd,hcop,hbin⟩,i,hi,?_⟩
  rw [← hbin,he,rationalLabel_reduced hd hcop]

lemma IsBinLabel.unique {Q B k : ℕ} {l r : ℕ×ℕ} (hQ : B^2≤Q)
    (hl : IsBinLabel Q B k l) (hr : IsBinLabel Q B k r) : l=r := by
  have hp : l.1*r.1<Q := by
    have h₁ := hl.2.1
    have h₂ := hr.2.1
    nlinarith [hl.1,hr.1]
  exact Prod.ext
    (same_bin_unique hl.1 hr.1 hp hl.2.2.2.1 hr.2.2.2.1
      (hl.2.2.2.2.trans hr.2.2.2.2.symm)).1
    (same_bin_unique hl.1 hr.1 hp hl.2.2.2.1 hr.2.2.2.1
      (hl.2.2.2.2.trans hr.2.2.2.2.symm)).2

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionPairs
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial

lemma convergentPair_reduced (a b k : ℕ) :
    0<(convergentPair a b k).2 ∧
      Nat.Coprime (convergentPair a b k).1 (convergentPair a b k).2 := by
  induction k generalizing a b with
  | zero => simp [convergentPair]
  | succ k ih =>
    have hh := ih b (a%b)
    simp only [convergentPair]
    split_ifs with h
    · simp
    · constructor
      · exact Nat.pos_of_ne_zero h
      · simpa [Nat.coprime_add_mul_left_left] using hh.2.symm

lemma convergentPair_ratio (a b k : ℕ) :
    ((convergentPair a b k).1:ℚ)/(convergentPair a b k).2=euclidConvergent a b k := by
  induction k generalizing a b with
  | zero => simp [convergentPair,euclidConvergent]
  | succ k ih =>
    have hh := ih b (a%b)
    by_cases h : (convergentPair b (a%b) k).1=0
    · have he : euclidConvergent b (a%b) k=0 := by rw [← hh,h]; simp
      simp [convergentPair,h,euclidConvergent,he]
    · have hp : ((convergentPair b (a%b) k).1:ℚ) ≠ 0 := by exact_mod_cast h
      simp only [convergentPair,ite_eq_right h,Nat.cast_add,Nat.cast_mul,euclidConvergent]
      rw [← hh,inv_div,add_div,mul_div_cancel_right₀ _ hp]

lemma convergentPair_label (a b k : ℕ) :
    rationalLabel (euclidConvergent a b k)=
      ((convergentPair a b k).2,(convergentPair a b k).1) := by
  rw [← convergentPair_ratio]
  exact rationalLabel_reduced (convergentPair_reduced a b k).1 (convergentPair_reduced a b k).2

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The exact integer in the two most significant wires is the quarter-bin. -/
lemma bitsValue_quarter (b : ℕ) (x : Fin (b+2) → Bool) :
    (bitsValue x).toNat / 2^b =
      2*(x (Fin.last (b+1))).toNat + (x ((Fin.last b).castSucc)).toNat := by
  have hlow := (bitsValue (fun i : Fin b => x i.castSucc.castSucc)).isLt
  simp only [bitsValue, BitVec.toNat_cons', Nat.shiftLeft_eq]
  have he : (x (Fin.last (b+1))).toNat * 2^(b+1) +
      ((x ((Fin.last b).castSucc)).toNat * 2^b +
        (bitsValue (fun i : Fin b => x i.castSucc.castSucc)).toNat) =
      (2*(x (Fin.last (b+1))).toNat + (x ((Fin.last b).castSucc)).toNat) * 2^b +
        (bitsValue (fun i : Fin b => x i.castSucc.castSucc)).toNat := by
    rw [pow_succ]
    ring
  rw [he, Nat.mul_comm _ (2^b), Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt hlow, Nat.add_zero]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

lemma binaryInputs_left (w : ℕ) (x : Fin (w+w) → Bool) (i : ℕ) (hi : i < w) :
    AIG.denote x ⟨(inputs (w+w)).1, (binaryInputs w).lhs.get i hi⟩ =
      (leftWord x).getLsbD i := by
  rw [binaryInputs, refVector_get, inputs_correct]
  exact (bitsValue_bit (fun j => x (j.castAdd w)) ⟨i,hi⟩).symm

lemma binaryInputs_right (w : ℕ) (x : Fin (w+w) → Bool) (i : ℕ) (hi : i < w) :
    AIG.denote x ⟨(inputs (w+w)).1, (binaryInputs w).rhs.get i hi⟩ =
      (rightWord x).getLsbD i := by
  rw [binaryInputs, refVector_get, inputs_correct]
  exact (bitsValue_bit (fun j => x (Fin.natAdd w j)) ⟨i,hi⟩).symm

lemma add_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (add w).eval x i = (leftWord x + rightWord x).getLsbD i.val := by
  rw [add, compileVec_correct]
  exact denote_blastAdd _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma mul_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (mul w).eval x i = (leftWord x * rightWord x).getLsbD i.val := by
  rw [mul, compileVec_correct]
  exact denote_blastMul _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitArithmeticDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

lemma sub_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (sub w).eval x i = (leftWord x - rightWord x).getLsbD i.val := by
  rw [sub, compileVec_correct]
  exact denote_blastSub _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma mod_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (mod w).eval x i = (leftWord x % rightWord x).getLsbD i.val := by
  rw [mod, compileVec_correct]
  exact denote_blastUmod _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordNetworks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
namespace BitArithmetic
open BooleanNetwork

lemma leftWord_append {w : ℕ} (a b : Basis w) : leftWord (Fin.append a b) = bitsValue a := by
  simp [leftWord]
lemma rightWord_append {w : ℕ} (a b : Basis w) : rightWord (Fin.append a b) = bitsValue b := by
  simp only [rightWord, Fin.append_right]

lemma mul_word (w : ℕ) (a b : Basis w) :
    bitsValue ((mul w).eval (Fin.append a b)) = bitsValue a * bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((mul w).eval (Fin.append a b))).getLsbD i =
    (mul w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    mul_correct, leftWord_append, rightWord_append]

lemma mod_word (w : ℕ) (a b : Basis w) :
    bitsValue ((mod w).eval (Fin.append a b)) = bitsValue a % bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((mod w).eval (Fin.append a b))).getLsbD i =
    (mod w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    mod_correct, leftWord_append, rightWord_append]

lemma bitsValue_append_zero {w t : ℕ} (x : Basis w) :
    bitsValue (Fin.append x (fun _ : Fin t => false)) = (bitsValue x).setWidth (w+t) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue (Fin.append x (fun _ : Fin t => false))).getLsbD i =
    Fin.append x (fun _ => false) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hw : i < w
  · have he : (⟨i,hi⟩ : Fin (w+t)) = (⟨i,hw⟩ : Fin w).castAdd t := Fin.ext rfl
    rw [he, Fin.append_left]
    exact (bitsValue_bit x ⟨i,hw⟩).symm
  · have he : (⟨i,hi⟩ : Fin (w+t)) = Fin.natAdd w (⟨i-w,by omega⟩ : Fin t) := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    rw [he, Fin.append_right, BitVec.getLsbD_of_ge _ _ (by omega)]

lemma padRight_word (w t : ℕ) (x : Basis w) :
    bitsValue ((padRight w t).eval x) = (bitsValue x).setWidth (w+t) := by
  rw [eval_padRight, bitsValue_append_zero]

lemma bitsValue_take {w t : ℕ} (x : Basis (w+t)) :
    bitsValue (x ∘ (Fin.castAdd t)) = (bitsValue x).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue (x ∘ Fin.castAdd t)).getLsbD i = x ((⟨i,hi⟩ : Fin w).castAdd t) from
    bitsValue_bit _ ⟨i,hi⟩, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  exact (bitsValue_bit x ((⟨i,hi⟩ : Fin w).castAdd t)).symm

lemma setWidth_toNat_of_le {w t : ℕ} (h : w ≤ t) (x : BitVec w) :
    (x.setWidth t).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ModularMultiply
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma mulMod_word {n w : ℕ} (a b m : BooleanNetwork n w) (x : Basis n)
    (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((mulMod a b m).eval x)).toNat =
      (bitsValue (a.eval x)).toNat * (bitsValue (b.eval x)).toNat %
        (bitsValue (m.eval x)).toNat := by
  simp only [mulMod, eval_rewire, eval_comp, eval_pair]
  rw [bitsValue_take, mod_word, BitVec.toNat_setWidth, BitVec.toNat_umod,
    mul_word, BitVec.toNat_mul]
  simp only [padRight_word, setWidth_toNat_of_le (by omega : w ≤ w+w)]
  have hp : (bitsValue (a.eval x)).toNat * (bitsValue (b.eval x)).toNat < 2^(w+w) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (bitsValue (a.eval x)).isLt
      (bitsValue (b.eval x)).isLt
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt]
  exact (Nat.mod_lt _ hm).trans (bitsValue (m.eval x)).isLt

lemma wordMux_eval {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w)
    (x : Basis n) :
    (wordMux c a b).eval x = if c.eval x 0 then a.eval x else b.eval x := by
  funext i
  simp only [wordMux, eval_comp, eval_vector, eval_mux, eval_bit, eval_pair]
  have h₀ : (⟨0,by omega⟩ : Fin (1+w+w)) = (Fin.castAdd w ((0 : Fin 1).castAdd w)) := rfl
  have h₁ : (⟨1+i.val,by omega⟩ : Fin (1+w+w)) = (Fin.natAdd 1 i).castAdd w := rfl
  have h₂ : (⟨1+w+i.val,by omega⟩ : Fin (1+w+w)) = Fin.natAdd (1+w) i := rfl
  simp only [h₀,h₁,h₂,Fin.append_left,Fin.append_right]
  split <;> rfl

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ModularPower
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

lemma powerStep_pack {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b) :
    (powerStep w i).eval (powerPack a m e z) =
      powerPack a m e ((powerNew w i).eval (powerPack a m e z)) := by
  simp only [powerStep, eval_pair, eval_select, powerPack]
  congr 1
  funext j
  exact Fin.append_left _ _ j

lemma powerNew_value {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b)
    (hm : 0 < (bitsValue m).toNat) :
    (bitsValue ((powerNew w i).eval (powerPack a m e z))).toNat =
      (if e i then ((bitsValue z).toNat^2 % (bitsValue m).toNat)*
        (bitsValue a).toNat % (bitsValue m).toNat
      else (bitsValue z).toNat^2 % (bitsValue m).toNat) := by
  rw [powerNew, wordMux_eval, powerBit_eval]
  have hm' : 0 < (bitsValue ((powerModulus w b).eval (powerPack a m e z))).toNat := by
    simpa only [powerModulus_eval] using hm
  split <;> rw [mulMod_word _ _ _ _ hm']
  · rw [mulMod_word _ _ _ _ hm']
    simp only [powerAcc_eval, powerBase_eval, powerModulus_eval, pow_two]
  · simp only [powerAcc_eval, powerModulus_eval, pow_two]

lemma horner_pow_step (a m v : ℕ) (b : Bool) :
    (if b then ((a^v % m)^2 % m)*a % m else (a^v % m)^2 % m) =
      a^(2*v+b.toNat) % m := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero]
    rw [← Nat.pow_mod, ← pow_mul]
    congr 2
    omega
  · simp only [↓reduceIte, Bool.toNat_true]
    rw [← Nat.pow_mod, Nat.mod_mul_mod, ← pow_mul, pow_succ, Nat.mul_comm v 2]

lemma powerPrefix_value {w b : ℕ} (a m : Basis w) (e : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) (k : ℕ) (hk : k ≤ b) :
    ∃ z : Basis w,
      (powerPrefix w b k hk).eval
        (powerPack a m e (fun i => (BitVec.ofNat w 1).getLsbD i.val)) = powerPack a m e z ∧
      (bitsValue z).toNat = (bitsValue a).toNat ^ horner e k hk % (bitsValue m).toNat := by
  induction k with
  | zero =>
    refine ⟨(fun i => (BitVec.ofNat w 1).getLsbD i.val),?_,?_⟩
    · simp only [powerPrefix, eval_select, Function.comp_id]
    · rw [bitsValue_bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      · simp [horner, Nat.mod_eq_of_lt (by omega : 1 < (bitsValue m).toNat)]
      · have h := (bitsValue m).isLt
        omega
  | succ k ih =>
    obtain ⟨z,hz,hv⟩ := ih (by omega)
    refine ⟨(powerNew w ⟨k,by omega⟩).eval (powerPack a m e z),?_,?_⟩
    · rw [powerPrefix,eval_comp,hz,powerStep_pack]
    · rw [powerNew_value _ _ _ _ _ (by omega), hv, horner_pow_step]
      rfl

lemma modularPower_value {w b : ℕ} (a m : Basis w) (e : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (bitsValue ((modularPower w b).eval (Fin.append (Fin.append a m) e))).toNat =
      (bitsValue a).toNat ^ horner e b le_rfl % (bitsValue m).toNat := by
  obtain ⟨z,hz,hv⟩ := powerPrefix_value a m e hm b le_rfl
  have hc : (wordConstant (n := (w+w)+b) (BitVec.ofNat w 1)).eval
      (Fin.append (Fin.append a m) e) =
        (fun i => (BitVec.ofNat w 1).getLsbD i.val) := by
    funext i
    simp [wordConstant]
  simp only [modularPower,eval_comp,eval_rewire,eval_pair,eval_select,
    Function.comp_id,hc]
  change (bitsValue (((powerPrefix w b b le_rfl).eval
    (powerPack a m e (fun i => (BitVec.ofNat w 1).getLsbD i.val))) ∘
      Fin.natAdd ((w+w)+b))).toNat = _
  rw [hz]
  have he : powerPack a m e z ∘ Fin.natAdd ((w+w)+b) = z := by
    funext i
    exact Fin.append_right _ _ i
  rw [he,hv]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularPaths
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators

lemma hybrid_update {b k : ℕ} (x y : Bits b) (t : Fin b) (v : Bool) (h : k ≤ t.val) :
    hybrid x (Function.update y t v) k = hybrid x y k := by
  funext i
  unfold hybrid
  by_cases hi : i.val < k
  · rw [ite_eq_left hi, ite_eq_left hi, Function.update_of_ne]
    intro he; subst i; omega
  · rw [ite_eq_right hi, ite_eq_right hi]

lemma hybrid_of_tail {b k : ℕ} (x y : Bits b) (h : TailEq k x y) :
    hybrid x y k = y := by
  funext i
  unfold hybrid
  split_ifs with hi
  · rfl
  · exact (h i (by omega)).symm

lemma tail_update {b k : ℕ} (hk : k < b) (x y : Bits b) (v : Bool) :
    TailEq k x (Function.update y ⟨k,hk⟩ v) ↔
      v = x ⟨k,hk⟩ ∧ TailEq (k+1) x y := by
  constructor
  · intro h
    constructor
    · simpa using h ⟨k,hk⟩ le_rfl
    · intro i hi
      have hn : i ≠ (⟨k,hk⟩ : Fin b) := by intro he; have hh := congrArg Fin.val he; change i.val=k at hh; omega
      simpa only [Function.update_of_ne hn] using h i (by omega)
  · rintro ⟨hv,h⟩ i hi
    by_cases he : i.val = k
    · have hi' : i = (⟨k,hk⟩ : Fin b) := Fin.ext he
      subst i; simpa using hv
    · rw [Function.update_of_ne (by intro hh; exact he (congrArg Fin.val hh))]
      exact h i (by omega)

variable {A : Type*} [AddCommGroup A]

lemma pathShift_update {b k : ℕ} (hk : k ≤ b) (δ : Fin b → Bits b → A)
    (x y : Bits b) (t : Fin b) (v : Bool) (h : k ≤ t.val) :
    pathShift δ x (Function.update y t v) k hk = pathShift δ x y k hk := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pathShift, pathShift, ih (by omega) (by omega), hybrid_update _ _ _ _ h]

lemma pathWeight_update {b k : ℕ} (hk : k ≤ b) (x y : Bits b)
    (t : Fin b) (v : Bool) (h : k ≤ t.val) :
    pathWeight x (Function.update y t v) k hk = pathWeight x y k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pathWeight, pathWeight, ih (by omega) (by omega), Function.update_of_ne]
    intro he; have hh := congrArg Fin.val he; change k=t.val at hh; omega

/-- Every data wire has a single H and therefore exactly one compatible path
for each input/output pair, even though the phase register is coherent. -/
theorem evolve_path {b : ℕ} (δ : Fin b → Bits b → A) (x y : Bits b) (χ : A → ℂ)
    (k : ℕ) (hk : k ≤ b) (z : A) :
    evolve δ x χ k hk y z =
      if TailEq k x y then pathWeight x y k hk * χ (z-pathShift δ x y k hk) else 0 := by
  classical
  induction k generalizing y z with
  | zero =>
    have he : TailEq 0 x y ↔ y=x := by simp [TailEq, funext_iff]
    simp [evolve, pathWeight, pathShift, he]
  | succ k ih =>
    rw [evolve, ih _ (by omega), ih _ (by omega)]
    simp only [tail_update]
    rw [pathShift_update _ _ _ _ _ _ le_rfl,
      pathShift_update _ _ _ _ _ _ le_rfl,
      pathWeight_update _ _ _ _ _ le_rfl, pathWeight_update _ _ _ _ _ le_rfl]
    by_cases ht : TailEq (k+1) x y
    · rw [ite_eq_left ht, pathShift, pathWeight, hybrid_of_tail _ _ ht]
      rw [show z-δ ⟨k,by omega⟩ y-pathShift δ x y k (by omega) =
        z-(pathShift δ x y k (by omega)+δ ⟨k,by omega⟩ y) by abel]
      cases hx : x ⟨k,by omega⟩ <;> cases hy : y ⟨k,by omega⟩ <;>
        simp [ht, hEntry] <;> ring
    · simp [ht]

lemma evolve_full {b : ℕ} (δ : Fin b → Bits b → A) (x y : Bits b) (χ : A → ℂ) (z : A) :
    evolve δ x χ b le_rfl y z =
      pathWeight x y b le_rfl * χ (z-pathShift δ x y b le_rfl) := by
  rw [evolve_path, ite_eq_left (by intro i hi; exact False.elim (Nat.not_le.mpr i.isLt hi))]

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularAlgebra
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators

lemma pathShift_prefix {A : Type*} [AddCommGroup A] {b : ℕ}
    (δ : Fin b → Bits b → A) (x y : Bits b) (k : ℕ) (hk : k ≤ b) :
    pathShift δ x y k hk =
      ∑ j : Fin k, δ (j.castLE hk) (hybrid x y (j.val+1)) := by
  induction k with
  | zero => simp [pathShift]
  | succ k ih =>
    rw [pathShift, ih (by omega), Fin.sum_univ_castSucc]
    rfl

lemma pathShift_full_sum {A : Type*} [AddCommGroup A] {b : ℕ}
    (δ : Fin b → Bits b → A) (x y : Bits b) :
    pathShift δ x y b le_rfl = ∑ j : Fin b, δ j (hybrid x y (j.val+1)) := by
  rw [pathShift_prefix]
  rfl

lemma pathWeight_prefix {b : ℕ} (x y : Bits b) (k : ℕ) (hk : k ≤ b) :
    pathWeight x y k hk = ∏ j : Fin k, hEntry (x (j.castLE hk)) (y (j.castLE hk)) := by
  induction k with
  | zero => simp [pathWeight]
  | succ k ih => rw [pathWeight, ih (by omega), Fin.prod_univ_castSucc]; rfl

lemma hEntry_pow (a c : Bool) :
    hEntry a c = (-1:ℂ)^(a.toNat*c.toNat) * (Real.sqrt 2 : ℂ)⁻¹ := by
  cases a <;> cases c <;> simp [hEntry, div_eq_mul_inv]

lemma pathWeight_full {b : ℕ} (x y : Bits b) :
    pathWeight x y b le_rfl = (-1:ℂ)^dot x y * (Real.sqrt 2 : ℂ)⁻¹^b := by
  rw [pathWeight_prefix]
  simp only [hEntry_pow, Fin.castLE_refl, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

lemma selected_evolve {A : Type*} [AddCommGroup A] [Fintype A] {b : ℕ}
    (δ : Fin b → Bits b → A) (x y : Bits b) (χ : A → ℂ) :
    (∑ z, star (χ z) * evolve δ x χ b le_rfl y z) =
      pathWeight x y b le_rfl *
        ∑ z, star (χ (z+pathShift δ x y b le_rfl)) * χ z := by
  simp only [evolve_full]
  calc
    _ = pathWeight x y b le_rfl * ∑ z, star (χ z) * χ (z-pathShift δ x y b le_rfl) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      congr 1
      symm
      simpa only [Equiv.coe_addRight, add_sub_cancel_right] using
        Equiv.sum_comp (Equiv.addRight (pathShift δ x y b le_rfl))
          (fun z => star (χ z) * χ (z-pathShift δ x y b le_rfl))

lemma productTerm {b : ℕ} (x y : Bits b) (i j : Fin b) :
    (2^(b-1-i.val)*(x i).toNat) * (2^j.val*(y j).toNat) =
      lowTerm x y i j +
        (if i=j then 2^(b-1)*(x i).toNat*(y i).toNat else 0) +
          2^b*highTerm x y i j := by
  have he : (2^(b-1-i.val)*(x i).toNat) * (2^j.val*(y j).toNat) =
      2^(b-1-i.val+j.val)*(x i).toNat*(y j).toNat := by rw [pow_add]; ring
  rw [he]
  by_cases hij : i.val < j.val
  · have hn : i ≠ j := by intro h; subst j; omega
    have hw : b-1-i.val+j.val = b+(j.val-i.val-1) := by have := i.isLt; omega
    simp only [lowTerm, highTerm, ite_eq_right (by omega : ¬j.val < i.val), ite_eq_left hij,
      ite_eq_right hn, hw, pow_add]
    ring
  · by_cases hji : j.val < i.val
    · have hn : i ≠ j := by intro h; subst j; omega
      simp [lowTerm, highTerm, hij, hji, hn]
    · have heq : i=j := Fin.ext (by omega)
      subst j
      have hw : b-1-i.val+i.val = b-1 := by have := i.isLt; omega
      simp [lowTerm, highTerm, hw]

lemma product_decomposition {b : ℕ} (x y : Bits b) :
    inputNumber x * outputNumber y =
      (∑ i, ∑ j, lowTerm x y i j) + 2^(b-1)*dot x y +
        2^b*(∑ i, ∑ j, highTerm x y i j) := by
  unfold inputNumber outputNumber
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, productTerm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  simp only [dot, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma rowShift_hybrid {b : ℕ} (x y : Bits b) (j : Fin b) :
    rowShift j (hybrid x y (j.val+1)) = ∑ i, lowTerm x y i j := by
  unfold rowShift
  apply Finset.sum_congr rfl
  intro i _
  unfold lowTerm
  by_cases hi : j.val < i.val
  · simp [hi, hybrid, show ¬i.val < j.val+1 by omega]
  · simp [hi]

lemma pathShift_rows {A : Type*} [Ring A]
    {b : ℕ} (x y : Bits b) :
    pathShift (fun j z => (rowShift j z : A)) x y b le_rfl =
      ((∑ i, ∑ j, lowTerm x y i j : ℕ) : A) := by
  rw [pathShift_full_sum]
  simp only [rowShift_hybrid, Nat.cast_sum]
  exact Finset.sum_comm

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_HornerEncoding
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

namespace BitArithmetic

lemma horner_sum {b : ℕ} (e : Basis b) (k : ℕ) (hk : k ≤ b) :
    horner e k hk = ∑ i : Fin k, 2^(k-1-i.val)*(e (i.castLE hk)).toNat := by
  induction k with
  | zero => simp [horner]
  | succ k ih =>
    rw [horner,ih (by omega),Fin.sum_univ_castSucc,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have he : k+1-1-i.val = (k-1-i.val)+1 := by have := i.isLt; omega
      rw [show (i.castSucc : Fin (k+1)).val = i.val from rfl,he,pow_succ]
      have hi : ((i.castSucc).castLE hk) = i.castLE (by omega : k ≤ b) := Fin.ext rfl
      rw [hi]
      ring
    · simp only [Fin.val_last,Nat.add_sub_cancel,Nat.sub_self,pow_zero,one_mul]
      rfl

lemma horner_full {b : ℕ} (e : Basis b) :
    horner e b le_rfl = Triangular.inputNumber e := by
  rw [horner_sum]
  rfl

end BitArithmetic

lemma Triangular.inputNumber_bijective (b : ℕ) :
    Function.Bijective (fun x : Basis b =>
      (⟨inputNumber x,inputNumber_lt x⟩ : Fin (2^b))) := by
  have h := (bitsEquiv b).bijective.comp (reverseBits b).bijective
  have he : (fun x : Basis b => (⟨inputNumber x,inputNumber_lt x⟩ : Fin (2^b))) =
    fun x => ((bitsEquiv b (reverseBits b x)).toFin) := by
    funext x
    apply Fin.ext
    exact inputNumber_reverse x
  rw [he]
  exact (BitVec.equivFin (m := b)).bijective.comp h

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BinLabelCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma checkedPair_nonzero_iff {Q B k i : ℕ} :
    (checkedPair Q B k i).1≠0 ↔
      IsBinLabel Q B k ((convergentPair k Q i).2,(convergentPair k Q i).1) := by
  dsimp only [checkedPair]
  split_ifs with h
  · exact ⟨fun _ => h,fun _ => Nat.ne_of_gt h.1⟩
  · simp [h]
lemma checkedPair_sound {Q B k i : ℕ} (h : (checkedPair Q B k i).1≠0) :
    IsBinLabel Q B k (checkedPair Q B k i) := by
  have hh := checkedPair_nonzero_iff.mp h
  simp [checkedPair,hh]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrial
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.OrderTrial.binErrorRat_cast _root_.OAI.ExactQuantumFactoring.OrderTrial.evalReal_C _root_.OAI.ExactQuantumFactoring.OrderTrial.evalReal_X _root_.OAI.ExactQuantumFactoring.OrderTrial.evalReal_add _root_.OAI.ExactQuantumFactoring.OrderTrial.evalReal_comp _root_.OAI.ExactQuantumFactoring.OrderTrial.evalReal_linearArg _root_.OAI.ExactQuantumFactoring.OrderTrial.evalReal_mul _root_.OAI.ExactQuantumFactoring.OrderTrial.evalReal_pow _root_.OAI.ExactQuantumFactoring.OrderTrial.evalReal_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open MeasureTheory intervalIntegral

lemma phase_bin_progression {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) (j t i : ℕ) :
    phase ((bin Q d j : ℝ)*(t+i*d)/Q) =
      phase (((j*t)%d : ℕ)/ (d:ℝ) + binError Q d j*((t+i*d : ℕ):ℝ)/Q) := by
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hr : (((j*t)%d : ℕ):ℝ) + (d:ℝ)*(((j*t)/d : ℕ):ℝ) = (j:ℝ)*t := by
    exact_mod_cast Nat.mod_add_div (j*t) d
  have hjt : (j:ℝ)*t/d = (((j*t)%d : ℕ):ℝ)/d + (((j*t)/d : ℕ):ℝ) := by
    rw [← hr, add_div, mul_div_cancel_left₀ _ hd']
  have heq : (bin Q d j : ℝ)*(t+i*d)/Q =
      (((j*t)%d : ℕ):ℝ)/d + binError Q d j*((t+i*d : ℕ):ℝ)/Q +
      (((j*t/d+j*i : ℕ):ℤ):ℝ) := by
    calc
      _ = (j:ℝ)*t/d+(j:ℝ)*i + binError Q d j*((t+i*d : ℕ):ℝ)/Q := by
        unfold binError
        push_cast
        field_simp
        ring
      _ = _ := by
        rw [hjt]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_mul]
        ring
  rw [heq, phase_add_int]

lemma residueAmplitude_samples {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    residueAmplitude Q d j t = (Q:ℂ)⁻¹ *
      ∑ i ∈ Finset.range (sampleCount Q d t),
        phase (((j*t)%d : ℕ)/(d:ℝ) +
          binError Q d j*((t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q))) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  unfold residueAmplitude
  rw [← sum_progression (fun x => phase ((bin Q d j:ℝ)*x/Q)) hd hdQ ht]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_add, Nat.cast_mul, phase_bin_progression hQ hd]
  congr 1
  push_cast
  ring

lemma residueAmplitude_integral_error {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    ‖residueAmplitude Q d j t - residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖ ≤
      6/(Q:ℝ) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  let a : ℝ := t/Q
  let h : ℝ := d/Q
  let M := sampleCount Q d t
  let f : ℝ → ℂ := fun v => phase (((j*t)%d : ℕ)/(d:ℝ) + binError Q d j*v)
  have hh₀ : 0 ≤ h := div_nonneg hd'.le hQ'.le
  have hh₁ : h ≤ 1 := (div_le_one hQ').mpr (by exact_mod_cast hdQ)
  have ha₀ : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hQ'.le
  have ha₁ : a ≤ h := (div_le_div_iff_of_pos_right hQ').mpr (by exact_mod_cast ht.le)
  have he : a+(M:ℝ)*h = ((t+M*d : ℕ):ℝ)/Q := by dsimp [a,h]; push_cast <;> ring
  have hM := sampleCount_bounds hd hdQ ht
  have hM₀ : 1 ≤ a+(M:ℝ)*h := by
    rw [he]
    apply (one_le_div hQ').mpr
    exact_mod_cast hM.1
  have hM₁ : a+(M:ℝ)*h ≤ 1+h := by
    rw [he]
    have hsum : (1:ℝ)+h = ((Q+d : ℕ):ℝ)/Q := by dsimp [h]; push_cast; field_simp
    rw [hsum]
    apply (div_le_div_iff_of_pos_right hQ').mpr
    exact_mod_cast hM.2
  have hf : Continuous f := phase_continuous.comp (by fun_prop)
  have hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w| :=
    segment_phase_sub_le _ (binError_bound hd)
  have hb : ∀ v, ‖f v‖ ≤ 1 := fun v => phase_norm_le _
  have hr := rectangle_sum_unit_error hf hL hb hh₀ hh₁ ha₀ ha₁ M hM₀ hM₁
  have heq : residueAmplitude Q d j t - residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j) =
      (d:ℂ)⁻¹ * (h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in (0:ℝ)..1, f v) := by
    rw [residueAmplitude_samples hd hdQ ht]
    dsimp [residueIntegral, averagePhase, f, a, h, M]
    push_cast
    have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hQC : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
    field_simp
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (d:ℝ)⁻¹*(6*h) := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hd'.le)
    _ = 6/(Q:ℝ) := by dsimp [h]; field_simp

lemma residueAmplitude_norm_le {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    ‖residueAmplitude Q d j t‖ ≤ 1 := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  let s := (Finset.range Q).filter (fun x => x%d=t)
  have hc : (s.card:ℝ) ≤ Q := by exact_mod_cast (Finset.card_filter_le (s := Finset.range Q)
    (p := fun x => x%d=t) |>.trans_eq (Finset.card_range Q))
  rw [residueAmplitude, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Q:ℝ)⁻¹*∑ x ∈ s, ‖phase ((bin Q d j:ℝ)*x/Q)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hQ'.le)
    _ ≤ (Q:ℝ)⁻¹*∑ _x ∈ s, (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => phase_norm_le _))
        (inv_nonneg.mpr hQ'.le)
    _ ≤ (Q:ℝ)⁻¹*Q := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hQ'.le)
    _ = 1 := inv_mul_cancel₀ hQ'.ne'

lemma norm_square_difference_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |‖z‖^2-‖w‖^2| ≤ 2*‖z-w‖ := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have h := abs_norm_sub_norm_le z w
  exact mul_le_mul (show ‖z‖+‖w‖ ≤ 2 by linarith) h (abs_nonneg _) (by norm_num)

/-- The key approximation (majorant-integral-bounds), for the exact source P. -/
lemma residueProbability_integral_error {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    |residueProbability Q d j t -
      ‖residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖^2| ≤ 32/(Q:ℝ) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hI := (residueIntegral_bounds hd (((j*t)%d : ℕ):ℝ) (binError_bound (Q := Q) (j := j) hd)).2
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hI₁ : ‖residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖ ≤ 1 :=
    hI.trans ((div_le_one (lt_of_lt_of_le zero_lt_one hd')).mpr hd')
  have h := norm_square_difference_le (residueAmplitude_norm_le hQ d j t) hI₁
  have he := residueAmplitude_integral_error hd hdQ ht j
  unfold residueProbability
  calc
    _ ≤ 2*‖residueAmplitude Q d j t - residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖ := h
    _ ≤ 2*(6/(Q:ℝ)) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ 32/(Q:ℝ) := by apply (le_div_iff₀ hQ').mpr; field_simp <;> norm_num

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Topology
open Set Filter

lemma rampSq_hasDerivAt (x : ℝ) : HasDerivAt rampSq (2*max 0 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : rampSq =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [rampSq, max_eq_left hy.le]
    simpa only [max_eq_left hx.le, mul_zero] using!
      (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he
  · have hl : HasDerivWithinAt rampSq 0 (Iic 0) 0 := by
      apply (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr
      · intro y hy
        simp [rampSq, max_eq_left (show y ≤ 0 from hy)]
      · norm_num [rampSq]
    have hr : HasDerivWithinAt rampSq 0 (Ici 0) 0 := by
      have h : HasDerivAt (fun y : ℝ => y^2) 0 0 := by
        simpa using! (hasDerivAt_id (0:ℝ)).pow 2
      apply h.hasDerivWithinAt.congr
      · intro y hy
        simp only [rampSq, max_eq_right (show 0 ≤ y from hy)]
      · norm_num [rampSq]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ, max_self, mul_zero] using hl.union hr
  · have he : rampSq =ᶠ[𝓝 x] fun y => y^2 := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp only [rampSq, max_eq_right hy.le]
    simpa [max_eq_right hx.le] using!
      ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq he

lemma rampSq_shift_hasDerivAt (x a : ℝ) :
    HasDerivAt (fun y => rampSq (y-a)) (2*max 0 (x-a)) x := by
  simpa only [mul_one] using!
    (rampSq_hasDerivAt (x-a)).comp x ((hasDerivAt_id x).sub_const a)

lemma splineRe_hasDerivAt (x : ℝ) : HasDerivAt splineRe (splineReDeriv x) x := by
  have h := (hasDerivAt_id x).add_const (1/2:ℝ)
  have h₀ := rampSq_hasDerivAt x
  have h₁ := rampSq_shift_hasDerivAt x (1/2)
  have h₂ := rampSq_shift_hasDerivAt x 1
  convert! ((((h.neg.add ((h.pow 2).const_mul 2)).sub (h₀.const_mul 4)).add
    (h₁.const_mul 4)).sub (h₂.const_mul 4)) using 1
  all_goals try with_reducible_and_instances rfl
  simp [splineReDeriv]
  ring

lemma splineIm_hasDerivAt (x : ℝ) : HasDerivAt splineIm (splineImDeriv x) x := by
  have h := (hasDerivAt_id x).add_const (1/2:ℝ)
  have h₀ : HasDerivAt (fun y => rampSq (y+1/4)) (2*max 0 (x+1/4)) x := by
    simpa only [mul_one] using!
      (rampSq_hasDerivAt (x+1/4)).comp x ((hasDerivAt_id x).add_const (1/4:ℝ))
  have h₁ := rampSq_shift_hasDerivAt x (1/4)
  have h₂ := rampSq_shift_hasDerivAt x (3/4)
  have h₃ := rampSq_shift_hasDerivAt x (5/4)
  convert! ((((((h.pow 2).const_mul 2).sub (h₀.const_mul 4)).add (h₁.const_mul 4)).sub
    (h₂.const_mul 4)).add (h₃.const_mul 4)).sub_const (1/4:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  simp [splineImDeriv]
  ring

lemma spline_hasDerivAt (x : ℝ) :
    HasDerivAt spline ((splineReDeriv x : ℂ)+(splineImDeriv x : ℂ)*Complex.I) x :=
  (splineRe_hasDerivAt x).ofReal_comp.add ((splineIm_hasDerivAt x).ofReal_comp.mul_const _)

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open MeasureTheory intervalIntegral

lemma splineReDeriv_eq {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    splineReDeriv x = triangle x := by
  unfold splineReDeriv
  by_cases h₀ : x ≤ 0
  · rw [max_eq_left h₀, max_eq_left (by linarith : x-1/2 ≤ 0),
      max_eq_left (by linarith : x-1 ≤ 0), triangle_local (by rw [abs_le]; constructor <;> linarith),
      abs_of_nonpos h₀]
    ring
  · have h₀' := le_of_not_ge h₀
    rw [max_eq_right h₀']
    by_cases h₁ : x ≤ 1/2
    · rw [max_eq_left (by linarith : x-1/2 ≤ 0), max_eq_left (by linarith : x-1 ≤ 0),
        triangle_local (by rw [abs_le]; constructor <;> linarith), abs_of_nonneg h₀']
      ring
    · have ht : triangle x = triangle (x-1) := by
        convert triangle_add_int (x-1) 1 using 1
        all_goals try with_reducible_and_instances rfl
        norm_num
      rw [ht, triangle_local (by rw [abs_le]; constructor <;> linarith),
        max_eq_right (by linarith : 0 ≤ x-1/2)]
      by_cases h₂ : x ≤ 1
      · rw [max_eq_left (by linarith : x-1 ≤ 0), abs_of_nonpos (by linarith : x-1 ≤ 0)]
        ring
      · rw [max_eq_right (by linarith : 0 ≤ x-1), abs_of_nonneg (by linarith : 0 ≤ x-1)]
        ring

lemma splineImDeriv_eq {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    splineImDeriv x = -triangle (x-1/4) := by
  unfold splineImDeriv
  by_cases h₀ : x ≤ -(1/4)
  · have ht : triangle (x-1/4) = triangle (x+3/4) := by
      symm
      convert triangle_add_int (x-1/4) 1 using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
      congr 1
      ring
    rw [max_eq_left (by linarith : x+1/4 ≤ 0),
      max_eq_left (by linarith : x-1/4 ≤ 0), max_eq_left (by linarith : x-3/4 ≤ 0),
      max_eq_left (by linarith : x-5/4 ≤ 0), ht,
      triangle_local (by rw [abs_le]; constructor <;> linarith),
      abs_of_nonneg (by linarith : 0 ≤ x+3/4)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ x+1/4)]
    by_cases h₁ : x ≤ 1/4
    · rw [max_eq_left (by linarith : x-1/4 ≤ 0), max_eq_left (by linarith : x-3/4 ≤ 0),
        max_eq_left (by linarith : x-5/4 ≤ 0),
        triangle_local (by rw [abs_le]; constructor <;> linarith),
        abs_of_nonpos (by linarith : x-1/4 ≤ 0)]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ x-1/4)]
      by_cases h₂ : x ≤ 3/4
      · rw [max_eq_left (by linarith : x-3/4 ≤ 0), max_eq_left (by linarith : x-5/4 ≤ 0),
          triangle_local (by rw [abs_le]; constructor <;> linarith),
          abs_of_nonneg (by linarith : 0 ≤ x-1/4)]
        ring
      · have ht : triangle (x-1/4) = triangle (x-5/4) := by
          convert triangle_add_int (x-5/4) 1 using 1
          all_goals try with_reducible_and_instances rfl
          norm_num
          congr 1
          ring
        rw [max_eq_right (by linarith : 0 ≤ x-3/4), ht,
          triangle_local (by rw [abs_le]; constructor <;> linarith)]
        by_cases h₃ : x ≤ 5/4
        · rw [max_eq_left (by linarith : x-5/4 ≤ 0), abs_of_nonpos (by linarith : x-5/4 ≤ 0)]
          ring
        · rw [max_eq_right (by linarith : 0 ≤ x-5/4), abs_of_nonneg (by linarith : 0 ≤ x-5/4)]
          ring

lemma spline_derivative {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    HasDerivAt spline (phase x) x := by
  have h := spline_hasDerivAt x
  rw [splineReDeriv_eq hx₀ hx₁, splineImDeriv_eq hx₀ hx₁] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  apply Complex.ext <;> simp [phase]

lemma spline_integral {a b : ℝ} (ha₀ : -(1/2) ≤ a) (ha₁ : a ≤ 3/2)
    (hb₀ : -(1/2) ≤ b) (hb₁ : b ≤ 3/2) :
    (∫ v in a..b, phase v) = spline b-spline a := by
  apply integral_eq_sub_of_hasDerivAt _ (phase_continuous.intervalIntegrable _ _)
  intro x hx
  obtain ⟨hl,hu⟩ := hx
  apply spline_derivative
  · exact (le_min ha₀ hb₀).trans hl
  · exact hu.trans (max_le ha₁ hb₁)

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial MeasureTheory intervalIntegral

lemma evalReal_rampPiece (q a : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) :
    evalReal (rampPiece q a) x = rampSq (x-(a:ℝ)/4) := by
  by_cases h : a ≤ q
  · have h' : (a:ℝ) ≤ q := by exact_mod_cast h
    have hx : 0 ≤ x-(a:ℝ)/4 := by linarith
    simp only [rampPiece, ite_eq_left h, evalReal, Polynomial.eval₂_pow,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, rampSq, max_eq_right hx]
    norm_num
  · have h' : (q:ℝ)+1 ≤ a := by exact_mod_cast (show q+1 ≤ a by omega)
    have hx : x-(a:ℝ)/4 ≤ 0 := by linarith
    simp [rampPiece, h, evalReal, rampSq, max_eq_left hx]

lemma evalReal_splineRePiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (splineRePiece q) x = splineRe x := by
  have h0 := evalReal_rampPiece q 0 h₀ h₁
  have h2 := evalReal_rampPiece q 2 h₀ h₁
  have h4 := evalReal_rampPiece q 4 h₀ h₁
  simp only [evalReal, splineRePiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_neg, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  change -(x+(1/2:ℚ))+ (2:ℚ)*(x+(1/2:ℚ))^2 - (4:ℚ)*evalReal (rampPiece q 0) x +
    (4:ℚ)*evalReal (rampPiece q 2) x - (4:ℚ)*evalReal (rampPiece q 4) x = splineRe x
  rw [h0,h2,h4]
  norm_num [splineRe]

lemma evalReal_splineImPiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (splineImPiece q) x = splineIm x := by
  have hm1 := evalReal_rampPiece q (-1) h₀ h₁
  have h1 := evalReal_rampPiece q 1 h₀ h₁
  have h3 := evalReal_rampPiece q 3 h₀ h₁
  have h5 := evalReal_rampPiece q 5 h₀ h₁
  simp only [evalReal, splineImPiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  change (2:ℚ)*(x+(1/2:ℚ))^2 - (4:ℚ)*evalReal (rampPiece q (-1)) x +
    (4:ℚ)*evalReal (rampPiece q 1) x - (4:ℚ)*evalReal (rampPiece q 3) x +
    (4:ℚ)*evalReal (rampPiece q 5) x - (1/4:ℚ) = splineIm x
  rw [hm1,h1,h3,h5]
  norm_num [splineIm]

lemma poly_add_degree {p q : ℚ[X]} {k : ℕ} (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k) :
    (p+q).natDegree ≤ k := (natDegree_add_le _ _).trans (max_le hp hq)

lemma poly_sub_degree {p q : ℚ[X]} {k : ℕ} (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k) :
    (p-q).natDegree ≤ k := (natDegree_sub_le _ _).trans (max_le hp hq)

lemma rampPiece_natDegree_le (q a : ℤ) : (rampPiece q a).natDegree ≤ 2 := by
  unfold rampPiece
  split_ifs
  · apply le_trans (Polynomial.natDegree_pow_le)
    have h : (X-C ((a:ℚ)/4)).natDegree ≤ 1 :=
      le_trans (Polynomial.natDegree_sub_le _ _) (by simp)
    omega
  · simp

lemma splineRePiece_natDegree_le (q : ℤ) : (splineRePiece q).natDegree ≤ 2 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  have hSq : ((X+C (1/2:ℚ))^2).natDegree ≤ 2 :=
    (Polynomial.natDegree_pow_le).trans (by omega)
  unfold splineRePiece
  apply poly_sub_degree
  · apply poly_add_degree
    · apply poly_sub_degree
      · apply poly_add_degree
        · simpa only [natDegree_neg] using (hX.trans (by norm_num : 1 ≤ 2))
        · exact (natDegree_C_mul_le _ _).trans hSq
      · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
  · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)

lemma splineImPiece_natDegree_le (q : ℤ) : (splineImPiece q).natDegree ≤ 2 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  have hSq : ((X+C (1/2:ℚ))^2).natDegree ≤ 2 :=
    (Polynomial.natDegree_pow_le).trans (by omega)
  unfold splineImPiece
  apply poly_sub_degree
  · apply poly_add_degree
    · apply poly_sub_degree
      · apply poly_add_degree
        · apply poly_sub_degree
          · exact (natDegree_C_mul_le _ _).trans hSq
          · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
        · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
      · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
  · simp

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrialFurther
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial MeasureTheory intervalIntegral

lemma residueIntegral_eq_primitive {d : ℕ} (hd : 0 < d) {u η : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ d) (hη : |η| ≤ 1/2) (hη₀ : η ≠ 0) :
    residueIntegral d u η = (d:ℂ)⁻¹*(η:ℂ)⁻¹*(spline (u/d+η)-spline (u/d)) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have ha₀ : 0 ≤ u/d := div_nonneg hu₀ hd'.le
  have ha₁ : u/d ≤ 1 := (div_le_one hd').mpr hu₁
  obtain ⟨hηl,hηu⟩ := abs_le.mp hη
  unfold residueIntegral averagePhase
  rw [integral_comp_add_mul phase hη₀, mul_zero, add_zero, mul_one,
    spline_integral (by linarith) (by linarith) (by linarith) (by linarith),
    Complex.real_smul, Complex.ofReal_inv, mul_assoc]

lemma residueIntegral_zero (d : ℕ) (u : ℝ) :
    residueIntegral d u 0 = (d:ℂ)⁻¹*phase (u/d) := by
  simp [residueIntegral, averagePhase]

lemma evalReal_rampLinear (q a : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) :
    evalReal (rampLinear q a) x = max 0 (x-(a:ℝ)/4) := by
  by_cases h : a ≤ q
  · have h' : (a:ℝ) ≤ q := by exact_mod_cast h
    have hx : 0 ≤ x-(a:ℝ)/4 := by linarith
    simp only [rampLinear, ite_eq_left h, evalReal, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C, max_eq_right hx]
    norm_num
  · have h' : (q:ℝ)+1 ≤ a := by exact_mod_cast (show q+1 ≤ a by omega)
    have hx : x-(a:ℝ)/4 ≤ 0 := by linarith
    simp [rampLinear, h, evalReal, max_eq_left hx]

lemma evalReal_phaseRePiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (phaseRePiece q) x = splineReDeriv x := by
  have h0 := evalReal_rampLinear q 0 h₀ h₁
  have h2 := evalReal_rampLinear q 2 h₀ h₁
  have h4 := evalReal_rampLinear q 4 h₀ h₁
  simp only [evalReal, phaseRePiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_neg, Polynomial.eval₂_mul, Polynomial.eval₂_one,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  change -1 + (4:ℚ)*(x+(1/2:ℚ)) - (8:ℚ)*evalReal (rampLinear q 0) x +
    (8:ℚ)*evalReal (rampLinear q 2) x - (8:ℚ)*evalReal (rampLinear q 4) x = splineReDeriv x
  rw [h0,h2,h4]
  norm_num [splineReDeriv]

lemma evalReal_phaseImPiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (phaseImPiece q) x = splineImDeriv x := by
  have hm1 := evalReal_rampLinear q (-1) h₀ h₁
  have h1 := evalReal_rampLinear q 1 h₀ h₁
  have h3 := evalReal_rampLinear q 3 h₀ h₁
  have h5 := evalReal_rampLinear q 5 h₀ h₁
  simp only [evalReal, phaseImPiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  change (4:ℚ)*(x+(1/2:ℚ)) - (8:ℚ)*evalReal (rampLinear q (-1)) x +
    (8:ℚ)*evalReal (rampLinear q 1) x - (8:ℚ)*evalReal (rampLinear q 3) x +
    (8:ℚ)*evalReal (rampLinear q 5) x = splineImDeriv x
  rw [hm1,h1,h3,h5]
  norm_num [splineImDeriv]

lemma rampLinear_natDegree_le (q a : ℤ) : (rampLinear q a).natDegree ≤ 1 := by
  unfold rampLinear
  split_ifs
  · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · simp

lemma phaseRePiece_natDegree_le (q : ℤ) : (phaseRePiece q).natDegree ≤ 1 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  unfold phaseRePiece
  apply poly_sub_degree
  · apply poly_add_degree
    · apply poly_sub_degree
      · apply poly_add_degree
        · simp
        · exact (natDegree_C_mul_le _ _).trans hX
      · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
  · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)

lemma phaseImPiece_natDegree_le (q : ℤ) : (phaseImPiece q).natDegree ≤ 1 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  unfold phaseImPiece
  apply poly_add_degree
  · apply poly_sub_degree
    · apply poly_add_degree
      · apply poly_sub_degree
        · exact (natDegree_C_mul_le _ _).trans hX
        · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
      · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
  · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial

lemma linearArg_natDegree_le (d : ℕ) (η : ℚ) : (linearArg d η).natDegree ≤ 1 := by
  apply poly_add_degree
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · simp

lemma integralPiece_natDegree_le (d : ℕ) (η : ℚ) {A G₀ G₁ : ℚ[X]}
    (hA : A.natDegree ≤ 1) (h₀ : G₀.natDegree ≤ 2) (h₁ : G₁.natDegree ≤ 2) :
    (integralPiece d η A G₀ G₁).natDegree ≤ 2 := by
  unfold integralPiece
  split_ifs
  · apply (natDegree_C_mul_le _ _).trans
    rw [natDegree_comp]
    exact (Nat.mul_le_mul hA (linearArg_natDegree_le _ _)).trans (by norm_num)
  · apply (natDegree_C_mul_le _ _).trans
    apply poly_sub_degree
    · rw [natDegree_comp]
      simpa using Nat.mul_le_mul h₁ (linearArg_natDegree_le d η)
    · rw [natDegree_comp]
      simpa using Nat.mul_le_mul h₀ (linearArg_natDegree_le d 0)

lemma evalReal_integralPiece (d : ℕ) (η : ℚ) (A G₀ G₁ : ℚ[X]) (x : ℝ) :
    evalReal (integralPiece d η A G₀ G₁) x =
      if η=0 then (d:ℝ)⁻¹*evalReal A (x/d)
      else ((d:ℝ)*(η:ℝ))⁻¹*(evalReal G₁ (x/d+η)-evalReal G₀ (x/d)) := by
  unfold integralPiece
  split_ifs <;> simp

lemma massPiece_natDegree_le (d : ℕ) (η : ℚ) (q₀ q₁ : ℤ) :
    (massPiece d η q₀ q₁).natDegree ≤ 4 := by
  apply poly_add_degree
  · apply natDegree_pow_le.trans
    have h := integralPiece_natDegree_le d η (phaseRePiece_natDegree_le q₀)
      (splineRePiece_natDegree_le q₀) (splineRePiece_natDegree_le q₁)
    omega
  · apply natDegree_pow_le.trans
    have h := integralPiece_natDegree_le d η (phaseImPiece_natDegree_le q₀)
      (splineImPiece_natDegree_le q₀) (splineImPiece_natDegree_le q₁)
    omega

lemma massPiece_eq {d : ℕ} (hd : 0 < d) (η : ℚ) {u : ℝ} (hu₀ : 0 ≤ u)
    (hu₁ : u ≤ d) (hη : |(η:ℝ)| ≤ 1/2) (q₀ q₁ : ℤ)
    (hq₀l : (q₀:ℝ)/4 ≤ u/d) (hq₀u : u/d ≤ ((q₀:ℝ)+1)/4)
    (hq₁l : (q₁:ℝ)/4 ≤ u/d+η) (hq₁u : u/d+η ≤ ((q₁:ℝ)+1)/4) :
    evalReal (massPiece d η q₀ q₁) u = ‖residueIntegral d u η‖^2 := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have ha₀ : 0 ≤ u/d := div_nonneg hu₀ hd'.le
  have ha₁ : u/d ≤ 1 := (div_le_one hd').mpr hu₁
  simp only [massPiece, evalReal_add, evalReal_pow, evalReal_integralPiece]
  by_cases h : η=0
  · simp only [h, ite_true, if_true, Rat.cast_zero, residueIntegral_zero]
    rw [evalReal_phaseRePiece q₀ hq₀l hq₀u, evalReal_phaseImPiece q₀ hq₀l hq₀u,
      splineReDeriv_eq (by linarith) (by linarith),
      splineImDeriv_eq (by linarith) (by linarith), Complex.sq_norm]
    rw [show (d:ℂ)⁻¹ = (((d:ℝ)⁻¹:ℝ):ℂ) by simp]
    simp [phase, Complex.normSq_apply]
    ring
  · simp only [h, ite_false, if_false]
    rw [evalReal_splineRePiece q₀ hq₀l hq₀u, evalReal_splineImPiece q₀ hq₀l hq₀u,
      evalReal_splineRePiece q₁ hq₁l hq₁u, evalReal_splineImPiece q₁ hq₁l hq₁u,
      residueIntegral_eq_primitive hd hu₀ hu₁ hη (by exact_mod_cast h), Complex.sq_norm]
    rw [show (d:ℂ)⁻¹ = (((d:ℝ)⁻¹:ℝ):ℂ) by simp,
      show ((η:ℝ):ℂ)⁻¹ = (((η:ℝ)⁻¹:ℝ):ℂ) by simp]
    simp [spline, Complex.normSq_apply, mul_inv_rev]
    ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

lemma roundCoeff_error {D : ℕ} (hD : 0 < D) (a : ℚ) :
    0 ≤ roundCoeff D a-a ∧ roundCoeff D a-a ≤ 1/(D:ℚ) := by
  have hD' : (0:ℚ) < D := Nat.cast_pos.mpr hD
  have hl := Int.le_ceil ((D:ℚ)*a)
  have hu := Int.ceil_lt_add_one ((D:ℚ)*a)
  unfold roundCoeff
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hD').mpr
    linarith
  · rw [sub_le_iff_le_add]
    apply (div_le_iff₀ hD').mpr
    rw [add_mul, div_mul_cancel₀ _ hD'.ne']
    linarith

lemma roundCoeff_error_real {D : ℕ} (hD : 0 < D) (a : ℚ) :
    0 ≤ (roundCoeff D a:ℝ)-(a:ℝ) ∧ (roundCoeff D a:ℝ)-(a:ℝ) ≤ 1/(D:ℝ) := by
  rcases roundCoeff_error hD a with ⟨hl, hu⟩
  constructor
  · have h : (0:ℝ) ≤ ((roundCoeff D a-a:ℚ):ℝ) := Rat.cast_nonneg.mpr hl
    simpa using h
  · have h : ((roundCoeff D a-a:ℚ):ℝ) ≤ ((1/(D:ℚ):ℚ):ℝ) := Rat.cast_le.mpr hu
    simpa using h

lemma roundedValue_error {D : ℕ} (hD : 0 < D) (p : ℚ[X])
    (hp : p.natDegree ≤ 4) {u : ℚ} (hu : 0 ≤ u) :
    0 ≤ (roundedValue D p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ∧
      (roundedValue D p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ≤
        (∑ q ∈ Finset.range 5, (u:ℝ)^q)/(D:ℝ) := by
  have hu' : (0:ℝ) ≤ u := by exact_mod_cast hu
  have he : (roundedValue D p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) =
      ∑ q ∈ Finset.range 5, ((roundCoeff D (p.coeff q):ℝ)-(p.coeff q:ℝ))*(u:ℝ)^q := by
    rw [Polynomial.eval₂_eq_sum_range' _ (by omega : p.natDegree < 5)]
    simp only [roundedValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
      sub_mul, Finset.sum_sub_distrib]
    rfl
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun q _ => mul_nonneg (roundCoeff_error_real hD _).1 (pow_nonneg hu' _))
  · calc
      _ ≤ ∑ q ∈ Finset.range 5, (1/(D:ℝ))*(u:ℝ)^q :=
        Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_right
          (roundCoeff_error_real hD _).2 (pow_nonneg hu' _))
      _ = _ := by rw [← Finset.mul_sum]; ring

lemma five_powers_bound {u B : ℝ} (hB : 2 ≤ B) (hu₀ : 0 ≤ u) (huB : u ≤ B) :
    (∑ q ∈ Finset.range 5, u^q) ≤ B^8 := by
  have hB1 : 1 ≤ B := by linarith
  have hs : (∑ q ∈ Finset.range 5, u^q) ≤ 5*B^4 := by
    calc
      _ ≤ ∑ _q ∈ Finset.range 5, B^4 := by
        apply Finset.sum_le_sum
        intro q hq
        exact (pow_le_pow_left₀ hu₀ huB q).trans
          (pow_le_pow_right₀ hB1 (by simp only [Finset.mem_range] at hq; omega))
      _ = _ := by simp
  have hB4 : 16 ≤ B^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hB 4
    norm_num at h
    exact h
  have h48 : B^8 = (B^4)^2 := by ring
  rw [h48]
  nlinarith

lemma roundedValue_small_error {Q B : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (p : ℚ[X]) (hp : p.natDegree ≤ 4) {u : ℕ} (hu : u ≤ B) :
    0 ≤ (roundedValue (Q*B^8) p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ∧
      (roundedValue (Q*B^8) p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ≤ 1/(Q:ℝ) := by
  have hB₀ : 0 < B := by omega
  have hD := Nat.mul_pos hQ (pow_pos hB₀ 8)
  have h := roundedValue_error hD p hp (Nat.cast_nonneg u)
  simp only [Rat.cast_natCast] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hB' : (0:ℝ) < B := Nat.cast_pos.mpr hB₀
  have hg := five_powers_bound (by exact_mod_cast hB : (2:ℝ) ≤ B)
    (Nat.cast_nonneg u) (by exact_mod_cast hu)
  calc
    _ ≤ (B:ℝ)^8/(Q*B^8) := by
      push_cast
      exact div_le_div_of_nonneg_right hg (mul_nonneg hQ'.le (pow_nonneg hB'.le _))
    _ = 1/(Q:ℝ) := by field_simp

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

lemma quarterIndex_bounds (x : ℚ) :
    (quarterIndex x:ℝ)/4 ≤ (x:ℝ) ∧ (x:ℝ) ≤ ((quarterIndex x:ℝ)+1)/4 := by
  have hl := Int.floor_le (4*x)
  have hu := (Int.lt_floor_add_one (4*x)).le
  change (quarterIndex x:ℚ) ≤ 4*x at hl
  change 4*x ≤ (quarterIndex x:ℚ)+1 at hu
  have hl' : (quarterIndex x:ℝ) ≤ 4*(x:ℝ) := by exact_mod_cast hl
  have hu' : 4*(x:ℝ) ≤ (quarterIndex x:ℝ)+1 := by exact_mod_cast hu
  constructor <;> linarith

lemma selectedMass_natDegree_le (d : ℕ) (η u : ℚ) :
    (selectedMass d η u).natDegree ≤ 4 := massPiece_natDegree_le _ _ _ _

lemma selectedMass_eq {d : ℕ} (hd : 0 < d) (η : ℚ) {u : ℕ} (hu : u ≤ d)
    (hη : |(η:ℝ)| ≤ 1/2) :
    evalReal (selectedMass d η u) u = ‖residueIntegral d u η‖^2 := by
  have h₀ := quarterIndex_bounds ((u:ℚ)/d)
  have h₁ := quarterIndex_bounds ((u:ℚ)/d+η)
  push_cast at h₀ h₁
  exact massPiece_eq hd η (Nat.cast_nonneg u) (by exact_mod_cast hu) hη _ _
    h₀.1 h₀.2 h₁.1 h₁.2

lemma majorant_ideal_error {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) {u : ℕ} (hu : u ≤ d) :
    64/(Q:ℝ) ≤ (majorant Q B d j u:ℝ)-‖residueIntegral d u (binError Q d j)‖^2 ∧
      (majorant Q B d j u:ℝ)-‖residueIntegral d u (binError Q d j)‖^2 ≤ 65/(Q:ℝ) := by
  have h := roundedValue_small_error hQ hB (selectedMass d (binErrorRat Q d j) u)
    (selectedMass_natDegree_le _ _ _) (hu.trans hdB)
  change 0 ≤ _-evalReal _ _ ∧ _-evalReal _ _ ≤ _ at h
  rw [selectedMass_eq hd _ hu (by simpa using binError_bound (Q:=Q) (j:=j) hd),
    binErrorRat_cast] at h
  simp only [majorant, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  simp only [div_eq_mul_inv] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Source majorant-error, with the stronger explicit margin 32/Q..97/Q. -/
lemma majorant_probability_error {Q B d t : ℕ} (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (hdQ : d ≤ Q) (ht : t < d) (j : ℕ) :
    32/(Q:ℝ) ≤ (majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t ∧
      (majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t ≤ 97/(Q:ℝ) := by
  have he := residueProbability_integral_error hd hdQ ht j
  rw [abs_le] at he
  have hm := majorant_ideal_error (hd.trans_le hdQ) hB hd hdB j (Nat.mod_lt (j*t) hd).le
  simp only [div_eq_mul_inv] at he hm ⊢
  constructor <;> linarith [he.1, he.2, hm.1, hm.2]

lemma majorantSum_lower {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) :
    1/(128*(d:ℝ)) ≤ (majorantSum Q B d j:ℝ) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hs : (d:ℝ)*(1/(8*(d:ℝ)))^2 ≤
      ∑ u ∈ Finset.range d, (majorant Q B d j u:ℝ) := by
    calc
      _ = ∑ _u ∈ Finset.range d, (1/(8*(d:ℝ)))^2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        have hl := (residueIntegral_bounds hd (u:ℝ) (binError_bound (Q:=Q) (j:=j) hd)).1
        have hp : 0 ≤ 1/(8*(d:ℝ)) := by positivity
        have hl2 := sq_le_sq₀ hp (norm_nonneg _) |>.mpr hl
        have hm := (majorant_ideal_error hQ hB hd hdB j (u:=u) (by simp only [Finset.mem_range] at hu; omega)).1
        have hQ' : (0:ℝ) ≤ 64/(Q:ℝ) := by positivity
        linarith
  simp only [majorantSum, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat]
  have he : (d:ℝ)*(1/(8*(d:ℝ)))^2/2 = 1/(128*(d:ℝ)) := by field_simp <;> ring
  rw [← he]
  linarith

lemma majorantSum_upper {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) :
    (majorantSum Q B d j:ℝ) ≤ 1/(2*(d:ℝ))+65*d/(2*(Q:ℝ)) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hs : (∑ u ∈ Finset.range d, (majorant Q B d j u:ℝ)) ≤
      (d:ℝ)*((1/(d:ℝ))^2+65/(Q:ℝ)) := by
    calc
      _ ≤ ∑ _u ∈ Finset.range d, ((1/(d:ℝ))^2+65/(Q:ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        have hl := (residueIntegral_bounds hd (u:ℝ) (binError_bound (Q:=Q) (j:=j) hd)).2
        have hp : 0 ≤ 1/(d:ℝ) := by positivity
        have hl2 := (sq_le_sq₀ (norm_nonneg _) hp).mpr hl
        have hm := (majorant_ideal_error hQ hB hd hdB j (u:=u) (by simp only [Finset.mem_range] at hu; omega)).2
        linarith
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [majorantSum, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat]
  have he : (d:ℝ)*((1/(d:ℝ))^2+65/(Q:ℝ))/2 =
      1/(2*(d:ℝ))+65*d/(2*(Q:ℝ)) := by field_simp
  rw [← he]
  linarith

end ExactQuantumFactoring.OrderTrial



end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrialFurther2
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

lemma largeQ (B : ℕ) (hB : 2 ≤ B) : 65*B ≤ B^16 := by
  have h : 65 ≤ B^15 := by
    calc
      65 ≤ (2:ℕ)^15 := by norm_num
      _ ≤ B^15 := Nat.pow_le_pow_left hB 15
  calc
    _ ≤ B^15*B := Nat.mul_le_mul_right B h
    _ = B^16 := (pow_succ B 15).symm

/-- The literal majorant-sum estimate at the standing Q=B^16. -/
lemma majorantSum_bounds {B d : ℕ} (hB : 2 ≤ B) (hd : 0 < d) (hdB : d < B) (j : ℕ) :
    1/(128*(d:ℝ)) ≤ (majorantSum (B^16) B d j:ℝ) ∧
      (majorantSum (B^16) B d j:ℝ) ≤ 2 := by
  have hQ : 0 < B^16 := pow_pos (by omega) _
  refine ⟨majorantSum_lower hQ hB hd hdB.le j, (majorantSum_upper hQ hB hd hdB.le j).trans ?_⟩
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hQ' : (0:ℝ) < (B^16:ℕ) := Nat.cast_pos.mpr hQ
  have h65 : (65:ℝ)*d ≤ (B^16:ℕ) := by
    exact_mod_cast (Nat.mul_le_mul_left 65 hdB.le).trans (largeQ B hB)
  have h₁ : 1/(2*(d:ℝ)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*d)).mpr
    linarith
  have h₂ : 65*(d:ℝ)/(2*(B^16:ℕ)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(B^16:ℕ))).mpr
    linarith
  linarith

lemma roundedValue_numerator (D : ℕ) (p : ℚ[X]) (u : ℕ) :
    roundedValue D p u = (roundedNumerator D p u:ℚ)/D := by
  simp only [roundedValue, roundedNumerator, roundCoeff, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma majorant_numerator {Q B : ℕ} (hQ : 0 < Q) (hB : 0 < B) (d j u : ℕ) :
    majorant Q B d j u = (majorantNumerator Q B d j u:ℚ)/(Q*B^8) := by
  simp only [majorant, majorantNumerator, roundedValue_numerator, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow]
  have hQ' : (Q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hB' : (B:ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

lemma majorantSum_numerator {Q B : ℕ} (hQ : 0 < Q) (hB : 0 < B) (d j : ℕ) :
    majorantSum Q B d j =
      ((∑ u ∈ Finset.range d, majorantNumerator Q B d j u : ℤ):ℚ)/(2*(Q*B^8)) := by
  simp only [majorantSum, majorant_numerator hQ hB, Int.cast_sum, ← Finset.sum_div]
  ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma prescribedMass_pos (d : ℕ) : 0 < prescribedMass d := by
  unfold prescribedMass
  positivity

lemma prescribedMass_upper {d : ℕ} (hd : 0 < d) :
    prescribedMass d ≤ 1/(1024*(d:ℚ)) := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) d
  have h' : (d:ℚ) ≤ (2:ℚ)^(Nat.clog 2 d) := by exact_mod_cast h
  unfold prescribedMass
  rw [pow_add, show (2:ℚ)^10=1024 by norm_num]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

lemma modeCoeff_basic (n : ℕ) {lam S : ℚ} (hlam : 0 ≤ lam) (hS : 0 < S) :
    0 ≤ modeCoeff n lam S ∧ modeCoeff n lam S ≤ lam/S ∧
      lam/S-modeCoeff n lam S ≤ 1/(2:ℚ)^(10*n) := by
  have hD : (0:ℚ) < 2^(10*n) := by positivity
  have hx : 0 ≤ (2:ℚ)^(10*n)*(lam/S) := mul_nonneg hD.le (div_nonneg hlam hS.le)
  have hf := Int.floor_le ((2:ℚ)^(10*n)*(lam/S))
  have hu := (Int.lt_floor_add_one ((2:ℚ)^(10*n)*(lam/S))).le
  have hfn : (0:ℚ) ≤ (⌊(2:ℚ)^(10*n)*(lam/S)⌋:ℤ) := by
    exact_mod_cast (Int.floor_nonneg.mpr hx)
  unfold modeCoeff
  refine ⟨div_nonneg hfn hD.le, ?_, ?_⟩
  · apply (div_le_iff₀ hD).mpr
    nlinarith
  · apply (mul_le_mul_iff_right₀ hD).mp
    rw [mul_sub, mul_div_cancel₀ _ hD.ne', mul_div_cancel₀ _ hD.ne']
    linarith

lemma modeRemainder_basic (n : ℕ) {lam S : ℚ} (hlam : 0 ≤ lam) (hS : 0 < S) :
    0 ≤ modeRemainder n lam S ∧ modeRemainder n lam S ≤ S/(2:ℚ)^(10*n) := by
  have h := modeCoeff_basic n hlam hS
  have he : modeRemainder n lam S = (lam/S-modeCoeff n lam S)*S := by
    unfold modeRemainder
    rw [sub_mul, div_mul_cancel₀ _ hS.ne']
  rw [he]
  refine ⟨mul_nonneg (sub_nonneg.mpr h.2.1) hS.le, ?_⟩
  calc
    _ ≤ (1/(2:ℚ)^(10*n))*S := mul_le_mul_of_nonneg_right h.2.2 hS.le
    _ = _ := by ring

lemma modeCoeff_bounds (n : ℕ) {d : ℕ} (hd : 0 < d) {S : ℚ}
    (hSl : 1/(128*(d:ℚ)) ≤ S) (hSu : S ≤ 2) :
    0 ≤ modeCoeff n (prescribedMass d) S ∧ modeCoeff n (prescribedMass d) S ≤ 1/8 ∧
      0 ≤ modeRemainder n (prescribedMass d) S ∧
      modeRemainder n (prescribedMass d) S ≤ 2/(2:ℚ)^(10*n) := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hSl
  have hc := modeCoeff_basic n (prescribedMass_pos d).le hS
  have hr := modeRemainder_basic n (prescribedMass_pos d).le hS
  refine ⟨hc.1, hc.2.1.trans ?_, hr.1, hr.2.trans ?_⟩
  · apply (div_le_iff₀ hS).mpr
    have hl := prescribedMass_upper hd
    have he : 1/(1024*(d:ℚ)) = (1/8)*(1/(128*(d:ℚ))) := by ring
    rw [he] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left hSl (by norm_num))
  · exact div_le_div_of_nonneg_right hSu (by positivity)

lemma sum_residue_permutation {α : Type*} [AddCommMonoid α] {d j : ℕ}
    (hd : 0 < d) (hj : Nat.Coprime j d) (f : ℕ → α) :
    (∑ t ∈ Finset.range d, f ((j*t)%d)) = ∑ u ∈ Finset.range d, f u := by
  let g : Fin d → Fin d := fun t => ⟨(j*t.val)%d, Nat.mod_lt _ hd⟩
  have hi : Function.Injective g := by
    intro a b hab
    apply Fin.ext
    have he : Nat.ModEq d (j*a.val) (j*b.val) := congrArg Fin.val hab
    have h := he.cancel_left_of_coprime hj.symm
    change a.val % d = b.val % d at h
    simpa only [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h
  have hb : Function.Bijective g := ⟨hi, Finite.surjective_of_injective hi⟩
  have h := (Equiv.ofBijective g hb).sum_comp (fun u : Fin d => f u.val)
  change (∑ t : Fin d, f ((j*t.val)%d)) = ∑ u : Fin d, f u.val at h
  rw [Fin.sum_univ_eq_sum_range (fun t => f ((j*t)%d)) d,
    Fin.sum_univ_eq_sum_range f d] at h
  exact h

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Exact cancellation, not an estimate: Mode 2 fills precisely U-P. -/
lemma first_second_mass {n Q B d j : ℕ} (hB : 0 < B) (hd : 0 < d)
    (hj : Nat.Coprime j d) :
    firstModeMass n Q B d j + secondModeMass n Q B d j =
      (modeCoeff n (prescribedMass d) (majorantSum Q B d j):ℝ) *
      (majorantSum Q B d j:ℝ) := by
  have hB' : (B:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  let c : ℝ := modeCoeff n (prescribedMass d) (majorantSum Q B d j)
  have hs : ∀ t, (1/(B:ℝ)^3) * (2*(B:ℝ)^3 *
      ((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t)*c) =
      2*c*((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t) := by
    intro t
    field_simp
  unfold firstModeMass secondModeMass
  change c/2*(∑ t ∈ Finset.range d, residueProbability Q d j t) +
    1/4*(∑ t ∈ Finset.range d, (1/(B:ℝ)^3) * (2*(B:ℝ)^3 *
      ((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t)*c)) =
        c*(majorantSum Q B d j:ℝ)
  simp_rw [hs]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_residue_permutation hd hj (fun u => (majorant Q B d j u:ℝ))]
  simp only [majorantSum, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat]
  ring

lemma third_mode_mass {n Q B d j : ℕ} (hB : 0 < B) :
    thirdModeMass n Q B d j =
      (modeRemainder n (prescribedMass d) (majorantSum Q B d j):ℝ) := by
  have hB' : (B:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  unfold thirdModeMass
  field_simp

/-- The exact mass per reduced label, including the d=1, j=0 boundary case. -/
lemma three_mode_mass {n Q B d j : ℕ} (hB : 0 < B) (hd : 0 < d)
    (hj : Nat.Coprime j d) :
    firstModeMass n Q B d j + secondModeMass n Q B d j + thirdModeMass n Q B d j =
      (prescribedMass d:ℝ) := by
  rw [first_second_mass hB hd hj, third_mode_mass hB]
  simp only [modeRemainder, Rat.cast_sub, Rat.cast_mul]
  ring

lemma largeQ_cube (B : ℕ) (hB : 2 ≤ B) : 256*B^3 ≤ B^16 := by
  have h : 256 ≤ B^13 := (by norm_num : 256 ≤ (2:ℕ)^13).trans (Nat.pow_le_pow_left hB 13)
  calc
    _ ≤ B^13*B^3 := Nat.mul_le_mul_right (B^3) h
    _ = _ := by rw [← pow_add]

/-- The artificial discrepancy is a valid probability even at false labels. -/
lemma discrepancy_retention_bounds {B d t : ℕ} (hB : 2 ≤ B) (hd : 0 < d)
    (hdB : d < B) (ht : t < d) (j : ℕ) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    0 ≤ 2*(B:ℝ)^3*((majorant (B^16) B d j ((j*t)%d):ℝ)-
      residueProbability (B^16) d j t)*c ∧
    2*(B:ℝ)^3*((majorant (B^16) B d j ((j*t)%d):ℝ)-
      residueProbability (B^16) d j t)*c ≤ 1 := by
  have hB₀ : 0 < B := by omega
  have hQ₀ : 0 < B^16 := pow_pos hB₀ _
  have hBQ : B ≤ B^16 := (by omega : B ≤ 65*B).trans (largeQ B hB)
  have he := majorant_probability_error hB hd hdB.le (hdB.le.trans hBQ) ht j
  have he₀ : 0 ≤ (majorant (B^16) B d j ((j*t)%d):ℝ)-residueProbability (B^16) d j t :=
    (by positivity : (0:ℝ) ≤ 32/(B^16:ℕ)).trans he.1
  have hq : (256:ℝ)*(B:ℝ)^3 ≤ (B:ℝ)^16 := by exact_mod_cast largeQ_cube B hB
  have hq₀ : (0:ℝ) < (B:ℝ)^16 := by positivity
  have he₁ : (majorant (B^16) B d j ((j*t)%d):ℝ)-residueProbability (B^16) d j t ≤
      128/(B:ℝ)^16 := by
    refine he.2.trans ?_
    simp only [Nat.cast_pow]
    exact div_le_div_of_nonneg_right (by norm_num) hq₀.le
  constructor
  · positivity
  calc
    _ ≤ 2*(B:ℝ)^3*(128/(B:ℝ)^16)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left he₁ (by positivity)) hc₁ hc₀ (by positivity)
    _ = 256*(B:ℝ)^3/(B:ℝ)^16 := by ring
    _ ≤ 1 := (div_le_one hq₀).mpr hq

lemma remainder_retention_bounds {n : ℕ} (hn : 1 ≤ n) {rho : ℝ}
    (hr₀ : 0 ≤ rho) (hr₁ : rho ≤ 2/(2:ℝ)^(10*n)) :
    0 ≤ 4*((2:ℝ)^n)^2*rho ∧ 4*((2:ℝ)^n)^2*rho ≤ 1 := by
  have h : (8:ℝ) ≤ 2^(8*n) := by
    calc
      _ ≤ (2:ℝ)^8 := by norm_num
      _ ≤ 2^(8*n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have he : (2:ℝ)^(10*n) = ((2:ℝ)^n)^2*2^(8*n) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  constructor
  · positivity
  calc
    _ ≤ 4*((2:ℝ)^n)^2*(2/(2:ℝ)^(10*n)) :=
      mul_le_mul_of_nonneg_left hr₁ (by positivity)
    _ = 8/(2:ℝ)^(8*n) := by
      rw [he]
      field_simp
      norm_num
    _ ≤ 1 := (div_le_one (by positivity)).mpr h

end ExactQuantumFactoring.OrderTrial



end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_Exactness
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma minusI_cast : (minusI:ℂ) = -Complex.I := by
  simp [minusI, GaussianInt.toComplex_def]

lemma phase_grid_numerator {Q : ℕ} (hQ : 0 < Q) (y : ℕ) :
    phase ((y:ℝ)/Q) = (gridPhaseNumerator Q y:ℂ)/(Q:ℂ) := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hQc : (Q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hr : (4*y)%Q < Q := Nat.mod_lt _ hQ
  have hr' : (0:ℝ) ≤ ((4*y)%Q:ℕ) := Nat.cast_nonneg _
  have hle : (((4*y)%Q:ℕ):ℝ) ≤ Q := by exact_mod_cast hr.le
  have ht₀ : 0 ≤ (((4*y)%Q:ℕ):ℝ)/Q := div_nonneg hr' hQ'.le
  have ht₁ : (((4*y)%Q:ℕ):ℝ)/Q ≤ 1 := (div_le_one hQ').mpr hle
  have he : ((((4*y)/Q:ℕ):ℝ)+(((4*y)%Q:ℕ):ℝ)/Q)/4 = (y:ℝ)/Q := by
    have h := Nat.mod_add_div (4*y) Q
    have h' : (((4*y)%Q:ℕ):ℝ)+(Q:ℝ)*((4*y)/Q:ℕ) = 4*y := by exact_mod_cast h
    field_simp
    nlinarith
  have hg := phase_interpolates (((4*y)/Q:ℕ):ℤ) ht₀ ht₁
  rw [show (((4*y)/Q:ℕ):ℤ)+1 = (((4*y)/Q+1:ℕ):ℤ) by simp] at hg
  simp only [Int.cast_natCast, zpow_natCast] at hg
  rw [he] at hg
  rw [hg]
  simp only [gridPhaseNumerator, map_add, map_sub, map_mul, map_pow, map_natCast,
    minusI_cast, Nat.cast_sub hr.le, Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp

lemma residueAmplitude_gaussian {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    residueAmplitude Q d j t = (residueGaussianNumerator Q d j t:ℂ)/(Q:ℂ)^2 := by
  have hph : ∀ x : ℕ, phase ((bin Q d j:ℝ)*x/Q) =
      (gridPhaseNumerator Q (bin Q d j*x):ℂ)/(Q:ℂ) := by
    intro x
    simpa only [Nat.cast_mul] using phase_grid_numerator hQ (bin Q d j*x)
  unfold residueAmplitude
  simp_rw [hph]
  rw [← Finset.sum_div]
  simp only [residueGaussianNumerator, map_sum]
  ring

lemma residueProbabilityRat_cast {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    (residueProbabilityRat Q d j t:ℝ) = residueProbability Q d j t := by
  rw [residueProbability, residueAmplitude_gaussian hQ, norm_div, norm_pow,
    Complex.norm_natCast, div_pow, ← Complex.normSq_eq_norm_sq,
    ← GaussianInt.intCast_real_norm]
  simp only [residueProbabilityRat, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_intCast]
  ring

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma phaseLabel_mod (m y : ℕ) : phaseLabel m (y%(4*m)) = phaseLabel m y := by
  unfold phaseLabel
  rw [Nat.mod_mul_left_div_self, ← Complex.I_pow_eq_pow_mod]

lemma phaseLabel_tile {m : ℕ} (hm : 0 < m) (a : ℕ) {u : ℕ} (hu : u < m) :
    phaseLabel m (a*m+u) = Complex.I^a := by
  unfold phaseLabel
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hu, zero_add]

lemma phaseLabel_correlation {m : ℕ} (hm : 0 < m) (a q : ℕ) {u s : ℕ}
    (hu : u < m) (hs : s < m) :
    star (phaseLabel m ((a*m+u+(q*m+s))%(4*m))) * phaseLabel m (a*m+u) =
      if u+s < m then (-Complex.I)^q else (-Complex.I)^(q+1) := by
  rw [phaseLabel_mod, phaseLabel_tile hm a hu]
  have he : a*m+u+(q*m+s) = (a+q)*m+(u+s) := by ring
  rw [he]
  by_cases h : u+s < m
  · rw [ite_eq_left h, phaseLabel_tile hm (a+q) h, pow_add]
    simp only [star_mul, star_pow, Complex.star_def, Complex.conj_I]
    have hi : (-Complex.I)^a*Complex.I^a = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = ((-Complex.I)^a*Complex.I^a)*(-Complex.I)^q := by ring
      _ = _ := by rw [hi, one_mul]
  · have hb : u+s-m < m := by omega
    have he : (a+q)*m+(u+s) = (a+(q+1))*m+(u+s-m) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    rw [ite_eq_right h, he, phaseLabel_tile hm (a+(q+1)) hb, pow_add]
    simp only [star_mul, star_pow, Complex.star_def, Complex.conj_I]
    have hi : (-Complex.I)^a*Complex.I^a = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = ((-Complex.I)^a*Complex.I^a)*(-Complex.I)^(q+1) := by ring
      _ = _ := by rw [hi, one_mul]

lemma sum_range_tiles {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a m : ℕ) :
    (∑ y ∈ Finset.range (a*m), f y) =
      ∑ i ∈ Finset.range a, ∑ u ∈ Finset.range m, f (i*m+u) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma sum_if_carry {m s : ℕ} (hs : s ≤ m) (v w : ℂ) :
    (∑ u ∈ Finset.range m, if u+s < m then v else w) = (m-s:ℕ)*v+(s:ℂ)*w := by
  have he := Finset.sum_range_add (fun u => if u+s< m then v else w) (m-s) s
  rw [Nat.sub_add_cancel hs] at he
  rw [he]
  have h₁ : (∑ u ∈ Finset.range (m-s), if u+s< m then v else w) = (m-s:ℕ)*v := by
    calc
      _ = ∑ u ∈ Finset.range (m-s), v := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [ite_eq_left (by have := Finset.mem_range.mp hu; omega)]
      _ = _ := by simp
  have h₂ : (∑ u ∈ Finset.range s, if m-s+u+s< m then v else w) = (s:ℂ)*w := by
    calc
      _ = ∑ u ∈ Finset.range s, w := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [ite_eq_right (by omega)]
      _ = _ := by simp
  rw [h₁,h₂]

lemma phaseOverlapSum_eq {m : ℕ} (hm : 0 < m) (q : ℕ) {s : ℕ} (hs : s < m) :
    phaseOverlapSum m (q*m+s) =
      (4*(m-s):ℕ)*(-Complex.I)^q+(4*s:ℕ)*(-Complex.I)^(q+1) := by
  unfold phaseOverlapSum
  rw [sum_range_tiles]
  have h : ∀ a, (∑ u ∈ Finset.range m,
      star (phaseLabel m ((a*m+u+(q*m+s))%(4*m))) * phaseLabel m (a*m+u)) =
      (m-s:ℕ)*(-Complex.I)^q+(s:ℂ)*(-Complex.I)^(q+1) := by
    intro a
    calc
      _ = ∑ u ∈ Finset.range m, if u+s< m then (-Complex.I)^q else (-Complex.I)^(q+1) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact phaseLabel_correlation hm a q (Finset.mem_range.mp hu) hs
      _ = _ := sum_if_carry hs.le _ _
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Exact overlap, with its direction fixed by the forward shift. -/
lemma phaseOverlap_eq {m : ℕ} (hm : 0 < m) (D : ℕ) :
    phaseOverlapSum m D/(4*(m:ℂ)) = phase ((D:ℝ)/(4*(m:ℝ))) := by
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hmc : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hs : D%m < m := Nat.mod_lt _ hm
  have hD : D/m*m+D%m=D := by simpa only [Nat.mul_comm] using Nat.div_add_mod D m
  have hov := phaseOverlapSum_eq hm (D/m) hs
  rw [hD] at hov
  have hph := phase_interpolates ((D/m:ℕ):ℤ)
    (div_nonneg (Nat.cast_nonneg (D%m)) hm'.le)
    ((div_le_one hm').mpr (by exact_mod_cast hs.le))
  have he : ((((D/m:ℕ):ℝ)+((D%m:ℕ):ℝ)/m)/4) = (D:ℝ)/(4*(m:ℝ)) := by
    have he' : ((D/m:ℕ):ℝ)*m+((D%m:ℕ):ℝ)=D := by exact_mod_cast hD
    field_simp
    nlinarith
  rw [show ((D/m:ℕ):ℤ)+1 = ((D/m+1:ℕ):ℤ) by simp] at hph
  simp only [Int.cast_natCast, zpow_natCast] at hph
  rw [he] at hph
  rw [hov,hph]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hs.le,
    Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp

lemma phaseState_overlap {m : ℕ} (hm : 0 < m) (D : ℕ) :
    (∑ y ∈ Finset.range (4*m), star (phaseState m ((y+D)%(4*m))) * phaseState m y) =
      phase ((D:ℝ)/(4*(m:ℝ))) := by
  have hs : (Real.sqrt (4*(m:ℝ)):ℂ)^2 = 4*(m:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have h (y : ℕ) : star (phaseState m ((y+D)%(4*m))) * phaseState m y =
      (star (phaseLabel m ((y+D)%(4*m))) * phaseLabel m y)/(4*(m:ℂ)) := by
    unfold phaseState
    simp only [star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    rw [← hs]
    ring
  simp_rw [h]
  rw [← Finset.sum_div]
  exact phaseOverlap_eq hm D

end ExactQuantumFactoring.OrderTrial



end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SuperpositionGates
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma eq_update_iff {q : ℕ} (x y : Basis q) (t : Fin q) (b : Bool) :
    y = Function.update x t b ↔ y t = b ∧ ∀ i, i ≠ t → y i = x i := by
  classical
  constructor
  · rintro rfl
    exact ⟨Function.update_self _ _ _, fun i hi => Function.update_of_ne hi _ _⟩
  · rintro ⟨ht,ho⟩
    funext i
    by_cases hi : i = t
    · subst i; simpa using ht
    · simpa [Function.update_of_ne hi] using ho i hi

lemma phaseAt_matrix {q : ℕ} (t : Fin q) (x y : Basis q) :
    (phaseAt t).matrix y x = if y = x then (if x t then Complex.I else 1) else 0 := by
  classical
  change (if ∀ i : Fin q, (∀ _ : Fin 1, t ≠ i) → y i = x i then
      (plainGate .phase).matrix (List.ofFn (fun _ : Fin 1 => y t))
        (List.ofFn (fun _ : Fin 1 => x t)) else 0) = _
  simp only [Gate.matrix, Gate.baseMatrix, Bool.false_eq_true, ite_false, if_false, List.ofFn_succ,
    List.ofFn_zero, Primitive.matrix]
  by_cases he : y = x
  · subst y; simp
  · by_cases ht : y t = x t
    · have ho : ¬ ∀ i : Fin q, t ≠ i → y i = x i := by
        intro hh
        apply he
        funext i
        by_cases hi : t = i
        · subst i; exact ht
        · exact hh i hi
      simp [he, ho]
    · simp [he, ht]

lemma hadamardAt_matrix {q : ℕ} (t : Fin q) (x y : Basis q) :
    (hadamardAt t).matrix y x =
      if ∀ i, i ≠ t → y i = x i then
        (if y t && x t then (-1 : ℂ) else 1) / (Real.sqrt 2 : ℂ) else 0 := by
  classical
  change (if ∀ i : Fin q, (∀ _ : Fin 1, t ≠ i) → y i = x i then
      (plainGate .hadamard).matrix (List.ofFn (fun _ : Fin 1 => y t))
        (List.ofFn (fun _ : Fin 1 => x t)) else 0) = _
  simp only [Gate.matrix, Gate.baseMatrix, Bool.false_eq_true, ite_false, if_false, List.ofFn_succ,
    List.ofFn_zero, Primitive.matrix]
  have he : (∀ i, t ≠ i → y i = x i) ↔ (∀ i, i ≠ t → y i = x i) := by
    constructor <;> intro h i hi <;> exact h i (Ne.symm hi)
  simp only [forall_const, he]

lemma hadamardAt_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (hadamardAt t).matrix.mulVec (basisVector x) =
      (Real.sqrt 2 : ℂ)⁻¹ • (basisVector (Function.update x t false) +
        (if x t then (-1 : ℂ) else 1) • basisVector (Function.update x t true)) := by
  classical
  rw [matrix_basisVector]
  funext y
  rw [hadamardAt_matrix]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVector, eq_update_iff]
  by_cases ho : ∀ i, i ≠ t → y i = x i
  · cases hx : x t <;> cases hy : y t <;> simp_all [div_eq_mul_inv]
  · simp [ho]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhasePreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma hadamardAt_apply {q : ℕ} (t : Fin q) (ψ : State q) (y : Basis q) :
    (hadamardAt t).matrix.mulVec ψ y =
      (ψ (Function.update y t false) +
        (if y t then (-1 : ℂ) else 1) * ψ (Function.update y t true)) / (Real.sqrt 2 : ℂ) := by
  classical
  change (∑ x, (hadamardAt t).matrix y x * ψ x) = _
  have hne : Function.update y t false ≠ Function.update y t true := by
    intro h; have := congrFun h t; simp at this
  rw [Finset.sum_eq_add (Function.update y t false) (Function.update y t true) hne]
  · rw [hadamardAt_matrix, hadamardAt_matrix]
    have h₀ : ∀ i, i ≠ t → y i = Function.update y t false i := by
      intro i hi; simp [Function.update_of_ne hi]
    have h₁ : ∀ i, i ≠ t → y i = Function.update y t true i := by
      intro i hi; simp [Function.update_of_ne hi]
    rw [ite_eq_left h₀, ite_eq_left h₁]
    simp only [Function.update_self, Bool.and_false, Bool.false_eq_true, ite_false, if_false, Bool.and_true]
    ring
  · intro x _ hx
    rw [hadamardAt_matrix]
    suffices ¬ ∀ i, i ≠ t → y i = x i by rw [ite_eq_right this, zero_mul]
    intro ho
    have he : x = Function.update y t (x t) := by
      apply (eq_update_iff ..).2
      exact ⟨rfl, fun i hi => (ho i hi).symm⟩
    cases ht : x t
    · exact hx.1 (ht ▸ he)
    · exact hx.2 (ht ▸ he)
  · simp
  · simp

lemma phaseAt_apply {q : ℕ} (t : Fin q) (ψ : State q) (y : Basis q) :
    (phaseAt t).matrix.mulVec ψ y = (if y t then Complex.I else 1) * ψ y := by
  classical
  change (∑ x, (phaseAt t).matrix y x * ψ x) = _
  rw [Finset.sum_eq_single y]
  · simp [phaseAt_matrix]
  · intro x _ h; simp [phaseAt_matrix, Ne.symm h]
  · simp

lemma hadamardPrefix_zero (q k : ℕ) (h : k ≤ q) :
    (programMatrix (hadamardPrefix q k h)).mulVec (basisVector (fun _ => false)) =
      (fun y => if ∀ i : Fin q, k ≤ i.val → y i = false then (Real.sqrt 2 : ℂ)⁻¹ ^ k else 0) := by
  classical
  induction k with
  | zero =>
    rw [hadamardPrefix, programMatrix_nil, Matrix.one_mulVec]
    funext y
    simp only [basisVector, pow_zero, Nat.zero_le, forall_const]
    have : y = (fun _ => false) ↔ ∀ i, y i = false := by
      constructor
      · rintro rfl; simp
      · exact funext
    simp only [this]
  | succ k ih =>
    rw [hadamardPrefix, programMatrix_append, programMatrix_singleton,
      ← Matrix.mulVec_mulVec, ih (by omega)]
    funext y
    rw [hadamardAt_apply]
    have hfalse : (∀ i : Fin q, k ≤ i.val → Function.update y ⟨k, by omega⟩ false i = false) ↔
        (∀ i : Fin q, k+1 ≤ i.val → y i = false) := by
      constructor
      · intro hh i hi
        have hn : i ≠ (⟨k, by omega⟩ : Fin q) := by intro he; have hh := congrArg Fin.val he; change i.val = k at hh; omega
        simpa [Function.update_of_ne hn] using hh i (by omega)
      · intro hh i hi
        by_cases he : i.val = k
        · have he' : i = (⟨k, by omega⟩ : Fin q) := Fin.ext he
          simp [he']
        · rw [Function.update_of_ne (by intro he'; exact he (congrArg Fin.val he'))]
          exact hh i (by omega)
    have htrue : ¬ ∀ i : Fin q, k ≤ i.val → Function.update y ⟨k, by omega⟩ true i = false := by
      intro hh
      have := hh ⟨k, by omega⟩ le_rfl
      simp at this
    simp only [hfalse, ite_eq_right htrue, mul_zero, add_zero]
    split_ifs <;> simp [pow_succ, div_eq_mul_inv]

lemma hadamards_zero (q : ℕ) :
    (programMatrix (hadamardPrefix q q le_rfl)).mulVec (basisVector (fun _ => false)) =
      fun _ => (Real.sqrt 2 : ℂ)⁻¹ ^ q := by
  rw [hadamardPrefix_zero]
  funext y
  rw [ite_eq_left (by intro i hi; exact False.elim (Nat.not_le.mpr i.isLt hi))]

lemma preparePhase_correct (b : ℕ) (hb : 2 ≤ b) (y : Basis b) :
    (programMatrix (preparePhase b hb)).mulVec (basisVector (fun _ => false)) y =
      (Real.sqrt 2 : ℂ)⁻¹ ^ b *
        (if y ⟨b-1, by omega⟩ then (-1 : ℂ) else 1) *
        (if y ⟨b-2, by omega⟩ then Complex.I else 1) := by
  rw [preparePhase, programMatrix_append, ← Matrix.mulVec_mulVec, hadamards_zero]
  rw [programMatrix_cons, programMatrix_cons, programMatrix_singleton,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [phaseAt_apply, phaseAt_apply, phaseAt_apply]
  cases y ⟨b-1, by omega⟩ <;> cases y ⟨b-2, by omega⟩ <;> simp <;> ring_nf <;> simp [Complex.I_sq]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhasePreparationConnection
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma sqrt_two_pow (b : ℕ) : Real.sqrt ((2:ℝ)^b) = Real.sqrt 2 ^ b := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

lemma hadamard_normalization (b : ℕ) :
    (Real.sqrt 2 : ℂ)⁻¹ ^ b = (Real.sqrt ((2:ℝ)^b) : ℂ)⁻¹ := by
  rw [sqrt_two_pow, Complex.ofReal_pow, inv_pow]

lemma preparePhase_label (b : ℕ) (y : Basis (b+2)) :
    (programMatrix (preparePhase (b+2) (by omega))).mulVec
        (basisVector (fun _ => false)) y =
      OrderTrial.phaseState (2^b) (bitsValue y).toNat := by
  rw [preparePhase_correct, hadamard_normalization]
  unfold OrderTrial.phaseState OrderTrial.phaseLabel
  rw [bitsValue_quarter]
  have he : (4:ℝ)*(2^b:ℕ) = (2:ℝ)^(b+2) := by push_cast <;> ring
  rw [he]
  have h₁ : (⟨b+2-1, by omega⟩ : Fin (b+2)) = Fin.last (b+1) := Fin.ext (by simp)
  have h₂ : (⟨b+2-2, by omega⟩ : Fin (b+2)) = (Fin.last b).castSucc := Fin.ext (by simp)
  rw [h₁, h₂]
  cases y (Fin.last (b+1)) <;> cases y (Fin.last b).castSucc <;>
    simp

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitResidue
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

lemma finEquiv_val {n : ℕ} [NeZero n] (z : Fin n) :
    (ZMod.finEquiv n z).val = z.val := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n => rfl

lemma basisResidue_val (b : ℕ) (x : Basis b) :
    (basisResidue b x).val = (bitsValue x).toNat := by
  exact finEquiv_val _

lemma basisResidue_eq (b : ℕ) (x : Basis b) :
    basisResidue b x = ((bitsValue x).toNat : ZMod (2^b)) := by
  rw [← basisResidue_val, ZMod.natCast_zmod_val]

lemma bitsValue_residue (b : ℕ) (z : ZMod (2^b)) :
    (bitsValue ((basisResidue b).symm z)).toNat = z.val := by
  rw [← basisResidue_val, Equiv.apply_symm_apply]

lemma basisResidue_bits (b : ℕ) (v : BitVec b) :
    basisResidue b (fun i => v.getLsbD i.val) = (v.toNat : ZMod (2^b)) := by
  rw [basisResidue_eq, bitsValue_bits]

lemma bitsValue_residue_add (b : ℕ) (z : ZMod (2^b)) (d : Basis b) :
    (fun i : Fin b => (bitsValue ((basisResidue b).symm z)+bitsValue d).getLsbD i.val) =
      (basisResidue b).symm (z+basisResidue b d) := by
  apply (basisResidue b).injective
  rw [basisResidue_bits, Equiv.apply_symm_apply, BitVec.toNat_add]
  rw [ZMod.natCast_mod, Nat.cast_add, bitsValue_residue, ZMod.natCast_zmod_val,
    basisResidue_eq]

lemma basisResidue_zero (b : ℕ) : basisResidue b (fun _ => false) = 0 := by
  rw [basisResidue_eq]
  have h : bitsValue (fun _ : Fin b => false) = (0 : BitVec b) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (bitsValue (fun _ : Fin b => false)).getLsbD i = false from bitsValue_bit _ ⟨i,hi⟩]
    simp
  rw [h]
  simp

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanOracle
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace BoolNet

/-- Only the actual trace, not unrelated output registers, must start at zero. -/
lemma program_eval_range {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) (x : Basis q)
    (hfresh : ∀ i : Fin q, n ≤ i.val → i.val < k → x i = false) :
    (∀ i : Fin k, (BooleanProgram.eval (p.program h) x) (i.castLE h) =
      p.eval (fun j => x (j.castLE (p.input_le.trans h))) i) ∧
    (∀ i : Fin q, k ≤ i.val → (BooleanProgram.eval (p.program h) x) i = x i) := by
  induction p with
  | input => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | @add k p o ih =>
    have hk : k ≤ q := by omega
    obtain ⟨hpre, hrest⟩ := ih hk (fun i hi hik => hfresh i hi (by omega))
    have hy : (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩ = false := by
      rw [hrest _ (by simp)]
      exact hfresh _ p.input_le (by simp)
    have hv : (o.compileOp h).value (BooleanProgram.eval (p.program hk) x) =
        o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk)))) := by
      rw [BoolNode.compileOp_value]
      congr 1
      funext i
      exact hpre i
    have heval : BooleanProgram.eval ((p.add o).program h) x =
        Function.update (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩
          (o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk))))) := by
      simp only [program, BooleanProgram.eval, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (o.compileOp h).eval (BooleanProgram.eval (p.program hk) x) = _
      rw [BooleanOp.eval_fresh _ _ hy, hv]
      rfl
    rw [heval]
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [eval_add_last]
        exact Function.update_self _ _ _
      · rw [eval_add_castSucc]
        rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change j.val = k at hh; omega)]
        exact hpre j
    · intro i hi
      rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change i.val = k at hh; omega)]
      exact hrest i (by omega)

end BoolNet

namespace BooleanNetwork

lemma copyPrefix_eval {k m : ℕ} (source : Fin m → Fin k) (t : ℕ) (h : t ≤ m)
    (x : Basis (k+m)) (i : Fin (k+m)) :
    (copyPrefix source t h).eval x i =
      if hi : k ≤ i.val ∧ i.val < k+t then
        Bool.xor (x i) (x ((source ⟨i.val-k, by omega⟩).castAdd m)) else x i := by
  induction t generalizing i with
  | zero => simp [copyPrefix, BooleanProgram.eval]
  | succ t ih =>
    simp only [copyPrefix, BooleanProgram.eval, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (BooleanOp.copy ((source ⟨t, by omega⟩).castAdd m) _).eval
      ((copyPrefix source t (by omega)).eval x) i = _
    by_cases hit : i.val = k+t
    · have he : i = Fin.natAdd k ⟨t, Nat.lt_of_succ_le h⟩ := Fin.ext hit
      subst i
      rw [BooleanOp.eval_at]
      simp only [BooleanOp.value]
      rw [ih, ih]
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      rw [dite_eq_right (by omega), dite_eq_right (by have := (source ⟨t, by omega⟩).isLt; omega),
        dite_eq_left (by omega)]
      simp
    · rw [BooleanOp.eval_away _ _ (by intro he; exact hit (congrArg Fin.val he))]
      rw [ih]
      by_cases hn : k ≤ i.val ∧ i.val < k+t
      · rw [dite_eq_left hn, dite_eq_left (by omega)]
      · rw [dite_eq_right hn, dite_eq_right (by omega)]

lemma oracle_basis {n m : ℕ} (c : BooleanNetwork n m) (x : Basis (c.width+m))
    (hfresh : ∀ i : Fin (c.width+m), n ≤ i.val → i.val < c.width → x i = false) :
    (programMatrix c.oracle).mulVec (basisVector x) = basisVector (c.oracleOutput x) := by
  let p := c.net.program (Nat.le_add_right c.width m)
  have hx := c.net.program_eval_range (Nat.le_add_right c.width m) x hfresh
  have hout (i : Fin (c.width+m)) (hi : i.val < c.width) : c.oracleOutput x i = x i := by
    simp only [oracleOutput, dite_eq_right (Nat.not_le.mpr hi)]
  have hy := c.net.program_eval_range (Nat.le_add_right c.width m) (c.oracleOutput x)
    (fun i hin hik => (hout i hik).trans (hfresh i hin hik))
  have hin : (fun j : Fin n => c.oracleOutput x
      (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _)))) =
      (fun j => x (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _)))) := by
    funext j
    apply hout
    change j.val < c.width
    exact j.isLt.trans_le c.net.input_le
  rw [hin] at hy
  have he : (copyPrefix c.output m le_rfl).eval (p.eval x) = p.eval (c.oracleOutput x) := by
    funext i
    rw [copyPrefix_eval]
    by_cases hi : c.width ≤ i.val
    · rw [dite_eq_left ⟨hi, i.isLt⟩, hx.2 i hi, hy.2 i hi]
      have hs : p.eval x ((c.output ⟨i.val-c.width, by omega⟩).castAdd m) =
          c.net.eval (fun j => x (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _))))
            (c.output ⟨i.val-c.width, by omega⟩) := hx.1 _
      rw [hs]
      simp only [oracleOutput, dite_eq_left hi, eval, Function.comp_apply]
    · rw [dite_eq_right (by tauto)]
      have hik : i.val < c.width := by omega
      exact (hx.1 ⟨i.val,hik⟩).trans (hy.1 ⟨i.val,hik⟩).symm
  change (programMatrix (p.compile ++ (copyPrefix c.output m le_rfl).compile ++
    p.compile.reverse.map Instruction.reverse)).mulVec (basisVector x) = _
  rw [programMatrix_append, programMatrix_append, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, BooleanProgram.compile_basis, BooleanProgram.compile_basis, he,
    BooleanProgram.uncompute]

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OracleLayout
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_assign _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_band _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bit _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bnot _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bxor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_constant _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_mux _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_rewire _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_band _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_bit _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_bnot _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_bor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_bxor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_constant _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_mux _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_rewire _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_vector _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma packed_input {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin n) :
    packed r x y ⟨i.val,by omega⟩ = x i := by simp [packed, i.isLt]

lemma packed_target {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin m) :
    packed r x y ⟨n+i.val,by omega⟩ = y i := by simp [packed, i.isLt]

lemma packed_work {n m r : ℕ} (x : Basis n) (y : Basis m) (i : Fin (n+m+r))
    (hi : n+m ≤ i.val) : packed r x y i = false := by
  simp [packed, show ¬ i.val<n by omega, show ¬ i.val<n+m by omega]

lemma oraclePlacement_val {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin (c.width+m)) :
    (oraclePlacement c hr i).val = oracleIndex n m c.width i.val := rfl

lemma oraclePlacement_input {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin n) :
    oraclePlacement c hr (i.castLE (c.net.input_le.trans (Nat.le_add_right _ _))) =
      ⟨i.val,by omega⟩ := by
  apply Fin.ext
  simp [oraclePlacement_val, oracleIndex, i.isLt]

lemma oraclePlacement_target {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin m) :
    oraclePlacement c hr ⟨c.width+i.val,by omega⟩ = ⟨n+i.val,by omega⟩ := by
  have hn := c.net.input_le
  apply Fin.ext
  simp [oraclePlacement_val, oracleIndex, show ¬c.width+i.val<n by omega]

lemma oraclePlacement_work {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (i : Fin (c.width+m)) (hin : n ≤ i.val) (hiw : i.val < c.width) :
    n+m ≤ (oraclePlacement c hr i).val := by
  rw [oraclePlacement_val]
  simp only [oracleIndex, ite_eq_right (Nat.not_lt.mpr hin), ite_eq_left hiw]
  omega

lemma oracleOn_basis {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (x : Basis n) (y : Basis m) :
    (programMatrix (oracleOn c hr)).mulVec (basisVector (packed r x y)) =
      basisVector (packed r x (fun i => Bool.xor (y i) (c.eval x i))) := by
  let w := oraclePlacement c hr
  have hz : ∀ i : Fin (c.width+m), n ≤ i.val → i.val < c.width →
      (packed r x y ∘ w) i = false := by
    intro i hin hiw
    exact packed_work x y _ (oraclePlacement_work c hr i hin hiw)
  rw [oracleOn, placed_basis w c.oracle (packed r x y) _ (oracle_basis c _ hz)]
  congr 1
  have heval : (fun j : Fin n => (packed r x y ∘ w)
      (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _)))) = x := by
    funext j
    rw [Function.comp_apply, oraclePlacement_input, packed_input]
  funext i
  by_cases hi : ∃ j, w j = i
  · obtain ⟨j,rfl⟩ := hi
    rw [Register.replace_inside]
    unfold oracleOutput
    rw [heval]
    by_cases hj : c.width ≤ j.val
    · rw [dite_eq_left hj]
      have hw : w j = (⟨n+(j.val-c.width),by have := j.isLt; omega⟩ : Fin (n+m+r)) := by
        apply Fin.ext
        simp only [w, oraclePlacement_val, oracleIndex,
          ite_eq_right (show ¬j.val<n by have := c.net.input_le; omega),
          ite_eq_right (Nat.not_lt.mpr hj)]
      change ((packed r x y) (w j) ^^ c.eval x ⟨j.val-c.width,by omega⟩) = _
      rw [hw, packed_target x y ⟨j.val-c.width,by omega⟩,
        packed_target x (fun i => y i ^^ c.eval x i) ⟨j.val-c.width,by omega⟩]
    · rw [dite_eq_right hj]
      by_cases hn : j.val < n
      · have hj' : j = (⟨j.val,hn⟩ : Fin n).castLE
          (c.net.input_le.trans (Nat.le_add_right _ _)) := rfl
        rw [hj', Function.comp_apply, oraclePlacement_input, packed_input, packed_input]
      · rw [Function.comp_apply, packed_work x y _ (oraclePlacement_work c hr j (by omega) (by omega)),
          packed_work x _ _ (oraclePlacement_work c hr j (by omega) (by omega))]
  · have hout : ∀ j, w j ≠ i := by simpa only [not_exists] using hi
    rw [Register.replace_outside w _ _ ⟨i,hout⟩]
    have hir : n+m ≤ i.val := by
      by_contra hn
      by_cases hin : i.val < n
      · exact hi ⟨(⟨i.val,hin⟩ : Fin n).castLE
          (c.net.input_le.trans (Nat.le_add_right _ _)), by
            rw [oraclePlacement_input]⟩
      · exact hi ⟨⟨c.width+(i.val-n),by omega⟩, by
          rw [oraclePlacement_target c hr ⟨i.val-n,by omega⟩]
          apply Fin.ext; dsimp; omega⟩
    rw [packed_work x y i hir, packed_work x _ i hir]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CleanPermutation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_assign _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_band _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bit _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bnot _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bxor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_constant _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_mux _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_rewire _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_band _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_bit _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_bnot _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_bor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_bxor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_constant _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_mux _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_rewire _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_vector _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma packed_single_swap {n r : ℕ} (x y : Basis n) (j : Fin n) :
    packed r x y ∘ Equiv.swap (⟨j.val,by omega⟩ : Fin (n+n+r)) ⟨n+j.val,by omega⟩ =
      packed r (Function.update x j (y j)) (Function.update y j (x j)) := by
  funext i
  by_cases ha : i.val = j.val
  · have hi : i = (⟨j.val,by omega⟩ : Fin (n+n+r)) := Fin.ext ha
    simp only [hi]
    rw [Function.comp_apply, Equiv.swap_apply_left, packed_target]
    simp [packed, j.isLt]
  · by_cases hb : i.val = n+j.val
    · have hi : i = (⟨n+j.val,by omega⟩ : Fin (n+n+r)) := Fin.ext hb
      simp only [hi]
      rw [Function.comp_apply, Equiv.swap_apply_right, packed_input]
      simp [packed, j.isLt]
    · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
        (by intro h; exact ha (congrArg Fin.val h))
        (by intro h; exact hb (congrArg Fin.val h))]
      unfold packed
      split_ifs with hn hnn
      · rw [Function.update_of_ne]
        intro h; exact ha (congrArg Fin.val h)
      · rw [Function.update_of_ne]
        intro h
        have hh := congrArg Fin.val h
        dsimp at hh
        omega
      · rfl

lemma swapPrefix_basis {n r : ℕ} (x y : Basis n) (k : ℕ) (hk : k ≤ n) :
    (programMatrix (swapPrefix n r k hk)).mulVec (basisVector (packed r x y)) =
      basisVector (packed r (fun i => if i.val<k then y i else x i)
        (fun i => if i.val<k then x i else y i)) := by
  induction k with
  | zero => simp [swapPrefix, programMatrix_nil]
  | succ k ih =>
    rw [swapPrefix, programMatrix_append, ← Matrix.mulVec_mulVec, ih (by omega),
      swapAt_basis, packed_single_swap _ _ (⟨k,by omega⟩ : Fin n)]
    congr 1
    congr 1 <;> funext i
    all_goals
      by_cases hi : i.val=k
      · have he : i = (⟨k,by omega⟩ : Fin n) := Fin.ext hi
        simp only [he]
        simp
      · rw [Function.update_of_ne (by intro he; exact hi (congrArg Fin.val he))]
        have he : (i.val < k+1) ↔ i.val<k := by omega
        simp only [he]

lemma swapBlocks_basis {n r : ℕ} (x y : Basis n) :
    (programMatrix (swapPrefix n r n le_rfl)).mulVec (basisVector (packed r x y)) =
      basisVector (packed r y x) := by
  rw [swapPrefix_basis]
  congr 1
  congr 1 <;> funext i <;> simp [i.isLt]

lemma cleanPermutation_basis {n r : ℕ} (f g : BooleanNetwork n n)
    (hf : f.net.count ≤ r) (hg : g.net.count ≤ r) (x : Basis n)
    (hfg : g.eval (f.eval x) = x) :
    (programMatrix (cleanPermutation f g hf hg)).mulVec
        (basisVector (packed r x (fun _ => false))) =
      basisVector (packed r (f.eval x) (fun _ => false)) := by
  rw [cleanPermutation, programMatrix_append, programMatrix_append,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oracleOn_basis]
  simp only [Bool.false_xor]
  rw [swapBlocks_basis, oracleOn_basis, hfg]
  simp

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PackedPrograms
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma packed_first {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y ∘ firstRegister n m r = x := by
  funext i
  exact packed_input x y i

lemma packed_replace_first {n m r : ℕ} (x u : Basis n) (y : Basis m) :
    (firstRegister n m r).replace (packed r x y) u = packed r u y := by
  funext i
  by_cases hi : i.val<n
  · have he : i = firstRegister n m r ⟨i.val,hi⟩ := rfl
    rw [he, Register.replace_inside]
    exact (packed_input u y ⟨i.val,hi⟩).symm
  · have hout : ∀ j : Fin n, firstRegister n m r j ≠ i := by
      intro j he
      have hh := congrArg Fin.val he
      change j.val = i.val at hh
      omega
    rw [Register.replace_outside _ _ _ ⟨i,hout⟩]
    simp [packed,hi]

lemma firstProgram_state {n m r : ℕ} (ops : List (Instruction n)) (y : Basis m)
    (ψ : State n) :
    (programMatrix (firstProgram m r ops)).mulVec (encodeState (fun x => packed r x y) ψ) =
      encodeState (fun x => packed r x y) ((programMatrix ops).mulVec ψ) := by
  refine matrix_encodeState (fun x => packed r x y) (fun x => packed r x y)
    (programMatrix (firstProgram m r ops)) (programMatrix ops) ?_ ψ
  intro x
  rw [firstProgram, Register.placed_basis_state, packed_first]
  have he : (fun u => (firstRegister n m r).replace (packed r x y) u) =
      (fun u => packed r u y) := funext (fun u => packed_replace_first x u y)
  exact congrArg₂ (fun (e : Basis n → Basis (n+m+r)) (v : State n) => encodeState e v)
    he (matrix_basisVector (programMatrix ops) x)

lemma firstProgram_basis {n m r : ℕ} (ops : List (Instruction n)) (y : Basis m)
    (x : Basis n) :
    (programMatrix (firstProgram m r ops)).mulVec (basisVector (packed r x y)) =
      encodeState (fun z => packed r z y) ((programMatrix ops).mulVec (basisVector x)) := by
  rw [← encodeState_basis (fun z => packed r z y) x]
  exact firstProgram_state ops y _

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PackedEncoding
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

lemma packed_injective {n m r : ℕ} :
    Function.Injective (fun xy : Basis n × Basis m => packed r xy.1 xy.2) := by
  intro x y h
  apply Prod.ext
  · funext i
    have hh := congrFun h (⟨i.val,by omega⟩ : Fin (n+m+r))
    simpa only [packed_input] using hh
  · funext i
    have hh := congrFun h (⟨n+i.val,by omega⟩ : Fin (n+m+r))
    simpa only [packed_target] using hh

lemma packed_update_input {n m r : ℕ} (x : Basis n) (y : Basis m) (j : Fin n) (c : Bool) :
    Function.update (packed r x y) (⟨j.val,by omega⟩ : Fin (n+m+r)) c =
      packed r (Function.update x j c) y := by
  funext i
  by_cases hi : i.val=j.val
  · have he : i = (⟨j.val,by omega⟩ : Fin (n+m+r)) := Fin.ext hi
    simp only [he, Function.update_self, packed_input]
  · rw [Function.update_of_ne (by intro h; exact hi (congrArg Fin.val h))]
    unfold packed
    split_ifs with hn hm
    · rw [Function.update_of_ne]
      intro h; exact hi (congrArg Fin.val h)
    · rfl
    · rfl

lemma append_update_left {p b : ℕ} (d : Basis p) (z : Basis b) (j : Fin p) (c : Bool) :
    Function.update (Fin.append d z) (j.castAdd b) c = Fin.append (Function.update d j c) z := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · by_cases hk : k = j
    · subst k; simp
    · rw [Function.update_of_ne (by intro h; apply hk; apply Fin.ext; exact congrArg (fun i : Fin (p+b) => i.val) h),
        Fin.append_left, Fin.append_left, Function.update_of_ne hk]
  · rw [Function.update_of_ne (by intro h; have hh := congrArg Fin.val h; simp at hh; omega),
      Fin.append_right, Fin.append_right]

/-- Taking an adjoint and reading a basis outcome implements exactly the
correlation with the prepared state, without an idealized projection gate. -/
lemma encoded_adjoint_test {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (he : Function.Injective e)
    (U : Matrix (Basis q) (Basis q) ℂ) (v : Basis q) (χ ψ : α → ℂ)
    (h : U.mulVec (basisVector v) = encodeState e χ) :
    U.conjTranspose.mulVec (encodeState e ψ) v = ∑ a, star (χ a)*ψ a := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    matrix_basisVector, Matrix.conjTranspose_apply]
  rw [matrix_basisVector] at h
  apply Finset.sum_congr rfl
  intro a _
  have ha := congrFun h (e a)
  rw [encodeState_at e he] at ha
  rw [ha]
  ring

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CoherentSampling
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma packed_eq_iff {n m r : ℕ} (x z : Basis n) (y u : Basis m) :
    packed r x y = packed r z u ↔ x=z ∧ y=u := by
  constructor
  · intro h
    have hh := BooleanNetwork.packed_injective (n := n) (m := m) (r := r)
      (a₁ := (x,y)) (a₂ := (z,u)) h
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  · rintro ⟨rfl,rfl⟩
    rfl

lemma encoded_packed_coordinate {n m r : ℕ} (y u : Basis m) (ψ : State n)
    (z : Basis n) :
    encodeState (fun x => packed r x y) ψ (packed r z u) = if u=y then ψ z else 0 := by
  classical
  rw [encodeState_apply]
  simp only [packed_eq_iff]
  by_cases hu : u=y
  · simp [hu]
  · simp [hu]

/-- Coherent sampling on an explicitly encoded logical subspace. Inactive
quantum registers stay present; normalization need not be inferred by analogy
with a stochastic oracle. -/
lemma sampleProgram_encoded_amplitude {α : Type*} [Fintype α]
    {n m r : ℕ} (e : α → Basis n) (c : BooleanNetwork n m)
    (hr : c.net.count ≤ r) (ops : List (Instruction n)) (ψ : α → ℂ)
    (z : Basis n) (u : Basis m) :
    (programMatrix (sampleProgram c hr ops)).mulVec
      (encodeState (fun x => packed r (e x) (fun _ => false)) ψ) (packed r z u) =
      ∑ x, if c.eval (e x)=u then programMatrix ops z (e x) * ψ x else 0 := by
  classical
  rw [sampleProgram,programMatrix_append,← Matrix.mulVec_mulVec]
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,firstProgram_basis]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,encoded_packed_coordinate,
    matrix_basisVector]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : c.eval (e x)=u
  · simp only [h,ite_true, if_true]
    ring
  · simp only [h,ite_false, if_false,show u ≠ c.eval (e x) from Ne.symm h,mul_zero]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ControlledTranslation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

namespace ControlledTranslation

lemma input_words {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    BitArithmetic.leftWord ((addInput δ).eval x) = bitsValue (phasePart x) ∧
      BitArithmetic.rightWord ((addInput δ).eval x) = bitsValue (δ.eval (dataPart x)) := by
  simp only [addInput, eval_pair, eval_comp, eval_select, BitArithmetic.leftWord,
    BitArithmetic.rightWord, Function.comp_apply, Fin.append_left, Fin.append_right]
  exact ⟨rfl,rfl⟩

lemma forward_correct {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (forward δ).eval x = translate (fun d => bitsValue (δ.eval d)) x := by
  rw [forward, eval_pair, eval_comp]
  unfold translate
  congr 1
  funext i
  rw [BitArithmetic.add_correct, (input_words δ x).1, (input_words δ x).2]

lemma backward_correct {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (backward δ).eval x = untranslate (fun d => bitsValue (δ.eval d)) x := by
  rw [backward, eval_pair, eval_comp]
  unfold untranslate
  congr 1
  funext i
  rw [BitArithmetic.sub_correct, (input_words δ x).1, (input_words δ x).2]

lemma untranslate_translate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) :
    untranslate δ (translate δ x) = x := by
  simp only [untranslate, translate, dataPart_append, phasePart_append, bitsValue_bits,
    BitVec.add_sub_cancel, bitsValue_bit]
  exact Fin.append_castAdd_natAdd

lemma forward_backward {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (backward δ).eval ((forward δ).eval x) = x := by
  rw [backward_correct, forward_correct, untranslate_translate]

end ControlledTranslation
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorGuess
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BitArithmetic BooleanNetwork Exactness

lemma fairState_mass (b : ℕ) (x : Basis b) :
    Complex.normSq (fairState b x)=(2:ℝ)⁻¹^b := by
  simp only [fairState,map_pow,Complex.normSq_inv,Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)]

lemma fairState_normalized (b : ℕ) : ∑ x, Complex.normSq (fairState b x)=1 := by
  simp only [fairState_mass,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RecordedHistory
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! The same-history deferred-filter argument of Section 6, at the level of
finite complex amplitudes with all old registers retained.  These are proved
lemmas for the main construction, not assumptions replacing that construction. -/
namespace ExactQuantumFactoring.RecordedHistory
open scoped BigOperators
open ExactQuantumFactoring.Exactness

lemma append_mass {H Y : Type*} [Fintype H] [Fintype Y]
    (ψ : H → ℂ) (fresh : H → Y → ℂ) (passed : H → Prop) [DecidablePred passed]
    (pass : H → Y → Prop) :
    outcomeMass (fun hy : H × Y => passed hy.1 ∧ pass hy.1 hy.2) (appendState ψ fresh) =
      ∑ h, if passed h then Complex.normSq (ψ h) * outcomeMass (pass h) (fresh h) else 0 := by
  classical
  unfold outcomeMass appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : passed h
  · simp only [hh, true_and, Complex.normSq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  · simp [hh]

/-- The normalized state of idle old work need not be known; exact local mass
on each passing passed suffices. No conditioning on future verification occurs. -/
lemma append_constant_mass {H Y : Type*} [Fintype H] [Fintype Y]
    (ψ : H → ℂ) (fresh : H → Y → ℂ) (passed : H → Prop) (pass : H → Y → Prop)
    (z : ℝ) (hlocal : ∀ h, passed h → outcomeMass (pass h) (fresh h) = z) :
    outcomeMass (fun hy : H × Y => passed hy.1 ∧ pass hy.1 hy.2) (appendState ψ fresh) =
      outcomeMass passed ψ * z := by
  classical
  rw [append_mass]
  unfold outcomeMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : passed h
  · have hl : (∑ y, if pass h y then Complex.normSq (fresh h y) else 0) = z :=
      hlocal h hh
    simp [hh, hl]
  · simp [hh]

lemma append_normalized {H Y : Type*} [Fintype H] [Fintype Y]
    (ψ : H → ℂ) (fresh : H → Y → ℂ)
    (hψ : ∑ h, Complex.normSq (ψ h) = 1)
    (hfresh : ∀ h, ∑ y, Complex.normSq (fresh h y) = 1) :
    ∑ hy, Complex.normSq (appendState ψ fresh hy) = 1 := by
  simp only [appendState, Complex.normSq_mul, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hfresh, mul_one]
  exact hψ

end ExactQuantumFactoring.RecordedHistory


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ParallelPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

lemma independent_mass {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α→ℂ) (χ : β→ℂ) (P : α→Prop) (R : β→Prop) :
    outcomeMass (fun xy : α×β => P xy.1 ∧ R xy.2) (independentState ψ χ)=
      outcomeMass P ψ*outcomeMass R χ := by
  exact RecordedHistory.append_constant_mass ψ (fun _ => χ) P (fun _ => R) _ (fun _ _ => rfl)

lemma independent_mass_right {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α→ℂ) (χ : β→ℂ) (R : β→Prop) (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    outcomeMass (fun xy : α×β => R xy.2) (independentState ψ χ)=outcomeMass R χ := by
  have hh := independent_mass ψ χ (fun _ => True) R
  have he : (fun xy : α×β => True ∧ R xy.2)=(fun xy => R xy.2) := by funext xy; simp
  have hn : outcomeMass (fun _ : α => True) ψ=1 := by
    unfold outcomeMass
    simpa only [ite_true, if_true] using hψ
  rw [he,hn,one_mul] at hh
  exact hh

lemma fair_normalized (b : ℕ) : ∑ x : Basis b, Complex.normSq (fairState b x)=1 := by
  exact fairState_normalized b

lemma basis_preparation_normalized {q : ℕ} (A : List (Instruction q)) (x : Basis q) :
    ∑ y, Complex.normSq ((programMatrix A).mulVec (basisVector x) y)=1 := by
  rw [unitary_mass _ (programMatrix_unitary _)]
  simp [basisVector]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetentionDenominators
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Explicit, uniform O(n) fair-bit lengths for every order-trial retention.
Mere dyadicity would not bound the worst-case circuit cost. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

namespace DyadicAt
lemma mono {k l : ℕ} {x : ℚ} (h : DyadicAt k x) (hkl : k≤l) : DyadicAt l x := by
  obtain ⟨z,rfl⟩ := h
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hkl
  refine ⟨z*2^c,?_⟩
  push_cast
  rw [pow_add]
  field_simp
lemma sub {k : ℕ} {x y : ℚ} (hx : DyadicAt k x) (hy : DyadicAt k y) : DyadicAt k (x-y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b,by push_cast <;> ring⟩
lemma mul {k l : ℕ} {x y : ℚ} (hx : DyadicAt k x) (hy : DyadicAt l y) : DyadicAt (k+l) (x*y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  refine ⟨a*b,?_⟩
  push_cast
  rw [pow_add]
  ring
lemma int_mul {k : ℕ} {x : ℚ} (z : ℤ) (hx : DyadicAt k x) : DyadicAt k ((z:ℚ)*x) := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨z*a,by push_cast <;> ring⟩
end DyadicAt

lemma majorant_at (n d j u : ℕ) : DyadicAt (24*n) (majorant ((2^n)^16) (2^n) d j u) := by
  refine ⟨majorantNumerator ((2^n)^16) (2^n) d j u,?_⟩
  rw [majorant_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_mul,← pow_mul,← pow_add]
  congr 1
  omega
lemma majorantSum_at (n d j : ℕ) : DyadicAt (24*n+1) (majorantSum ((2^n)^16) (2^n) d j) := by
  refine ⟨∑ u ∈ Finset.range d, majorantNumerator ((2^n)^16) (2^n) d j u,?_⟩
  rw [majorantSum_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_mul,← pow_mul,← pow_add,pow_succ]
  ring_nf
lemma probability_at (n d j t : ℕ) : DyadicAt (64*n) (residueProbabilityRat ((2^n)^16) d j t) := by
  refine ⟨(residueGaussianNumerator ((2^n)^16) d j t).norm,?_⟩
  rw [residueProbabilityRat]
  congr 1
  push_cast
  rw [← pow_mul,← pow_mul]
  congr 1
  omega
lemma coefficient_at (n : ℕ) (lam S : ℚ) : DyadicAt (10*n) (modeCoeff n lam S) := ⟨_,rfl⟩
lemma lambda_at {n d : ℕ} (hd : d≤2^n) : DyadicAt (n+10) (prescribedMass d) := by
  have h : DyadicAt (Nat.clog 2 d+10) (prescribedMass d) := ⟨1,by simp [prescribedMass]⟩
  exact h.mono (Nat.add_le_add_right (Nat.clog_le_of_le_pow hd) 10)
lemma remainder_at {n d : ℕ} (hn : 1≤n) (hd : d≤2^n) (j : ℕ) :
    DyadicAt (34*n+1) (modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)) := by
  unfold modeRemainder
  apply DyadicAt.sub
  · exact (lambda_at hd).mono (by omega)
  · have h := (coefficient_at n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)).mul
      (majorantSum_at n d j)
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (omega)

lemma discrepancy_at (n d j t : ℕ) : DyadicAt (74*n) (discrepancyRetention n d j t) := by
  have h := ((majorant_at n d j ((j*t)%d)).mono (show 24*n≤64*n by omega)).sub (probability_at n d j t)
  have h' := (h.int_mul (2*(2^n)^3)).mul
    (coefficient_at n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j))
  push_cast at h'
  convert h' using 1 <;> first | rfl | omega
lemma remainderRetention_at {n d : ℕ} (hn : 1≤n) (hd : d≤2^n) (j : ℕ) :
    DyadicAt (34*n+1) (remainderRetention n d j) := by
  have h := (remainder_at hn hd j).int_mul (4*(2^n)^2)
  simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_pow,remainderRetention] using h

lemma retentions_fixedDenominator {n d : ℕ} (hn : 1≤n) (hd : d≤2^n) (j t : ℕ) :
    DyadicAt (retentionBits n) (modeCoeff n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)) ∧
    DyadicAt (retentionBits n) (discrepancyRetention n d j t) ∧
    DyadicAt (retentionBits n) (remainderRetention n d j) := by
  exact ⟨(coefficient_at n _ _).mono (by unfold retentionBits; omega),
    (discrepancy_at n d j t).mono (by unfold retentionBits; omega),
    (remainderRetention_at hn hd j).mono (by unfold retentionBits; omega)⟩

lemma retained_numerator {T : ℕ} {x : ℚ} (hx : DyadicAt T x) (h₀ : 0≤x) (h₁ : x≤1) :
    ∃ z : ℕ, z≤2^T ∧ x=(z:ℚ)/2^T ∧ (Int.floor (x*2^T)).toNat=z := by
  obtain ⟨a,ha⟩ := hx
  have hp : (0:ℚ)<2^T := by positivity
  have ha₀ : 0≤a := by
    rw [ha,div_nonneg_iff] at h₀
    rcases h₀ with h | h
    · exact_mod_cast h.1
    · exact False.elim ((not_le_of_gt hp) h.2)
  have ha₁ : a≤(2:ℤ)^T := by
    rw [ha,div_le_one hp] at h₁
    exact_mod_cast h₁
  refine ⟨a.toNat,?_,?_,?_⟩
  · simpa using Int.toNat_le_toNat ha₁
  · have he : (a.toNat:ℚ)=(a:ℚ) := by exact_mod_cast (Int.toNat_of_nonneg ha₀)
    rw [he]; exact ha
  · rw [ha,div_mul_cancel₀ _ hp.ne',Int.floor_intCast]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ThresholdRetention
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Exact threshold thinning by a FIXED (not rejection-sampled) block of fair
bits. The complete block is retained in the physical history. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BooleanNetwork BitArithmetic

lemma fair_threshold_mass {b z : ℕ} (hz : z≤2^b) :
    outcomeMass (fun x : Basis b => (bitsValue x).toNat<z) (fairState b)=
      (z:ℝ)/2^b := by
  classical
  unfold outcomeMass
  simp only [fairState_mass]
  rw [Fintype.sum_equiv (bitsNatEquiv b)
    (fun x => if (bitsValue x).toNat<z then (2:ℝ)⁻¹^b else 0)
    (fun i => if i.val<z then (2:ℝ)⁻¹^b else 0) (fun _ => rfl)]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i<z then (2:ℝ)⁻¹^b else 0) (2^b)]
  have he : (∑ i ∈ Finset.range (2^b), if i<z then (2:ℝ)⁻¹^b else 0)=
      ∑ i ∈ Finset.range z, (2:ℝ)⁻¹^b := by
    rw [← Finset.sum_subset (Finset.range_mono hz)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left (Finset.mem_range.mp hi)]
    · intro i _ hi
      rw [ite_eq_right (by simpa using hi)]
  rw [he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,inv_pow,div_eq_mul_inv]

lemma dyadic_fair_threshold {b : ℕ} {p : ℚ} (h : OrderTrial.DyadicAt b p)
    (h₀ : 0≤p) (h₁ : p≤1) :
    outcomeMass (fun x : Basis b => (bitsValue x).toNat<(Int.floor (p*(2:ℚ)^b)).toNat)
      (fairState b)=(p:ℝ) := by
  obtain ⟨z,hz,hp,hfloor⟩ := OrderTrial.retained_numerator h h₀ h₁
  rw [hfloor,fair_threshold_mass hz,hp]
  push_cast
  rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FairLabelMass
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma fair_value_mass {b k : ℕ} (hk : k<2^b) :
    outcomeMass (fun x : Basis b => (bitsValue x).toNat=k) (fairState b)=1/(2:ℝ)^b := by
  classical
  unfold outcomeMass
  simp only [fairState_mass]
  rw [Fintype.sum_equiv (bitsNatEquiv b)
    (fun x => if (bitsValue x).toNat=k then (2:ℝ)⁻¹^b else 0)
    (fun i => if i.val=k then (2:ℝ)⁻¹^b else 0) (fun _ => rfl)]
  have he : ∀ i : Fin (2^b), i.val=k ↔ i=⟨k,hk⟩ := by
    intro i
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,one_div,inv_pow]

lemma fair_variable_append {b d : ℕ} {α : Type*} [Fintype α]
    (hd : d≤2^b) (χ : α→ℂ) (P : ℕ→α→Prop) :
    outcomeMass (fun xu : Basis b × α => (bitsValue xu.1).toNat<d ∧ P (bitsValue xu.1).toNat xu.2)
      (independentState (fairState b) χ)=
      (1/(2:ℝ)^b)*∑ t ∈ Finset.range d, outcomeMass (P t) χ := by
  classical
  change outcomeMass (fun xu : Basis b × α => (bitsValue xu.1).toNat<d ∧ P (bitsValue xu.1).toNat xu.2)
    (RecordedHistory.appendState (fairState b) (fun _ => χ))=_
  rw [RecordedHistory.append_mass (fairState b) (fun _ => χ)
    (fun x => (bitsValue x).toNat<d) (fun x => P (bitsValue x).toNat)]
  simp only [fairState_mass]
  rw [Fintype.sum_equiv (bitsNatEquiv b)
    (fun x => if (bitsValue x).toNat<d then (2:ℝ)⁻¹^b*outcomeMass (P (bitsValue x).toNat) χ else 0)
    (fun i => if i.val<d then (2:ℝ)⁻¹^b*outcomeMass (P i.val) χ else 0) (fun _ => rfl)]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if i<d then (2:ℝ)⁻¹^b*outcomeMass (P i) χ else 0) (2^b)]
  have he : (∑ i ∈ Finset.range (2^b), if i<d then (2:ℝ)⁻¹^b*outcomeMass (P i) χ else 0)=
      ∑ i ∈ Finset.range d, (2:ℝ)⁻¹^b*outcomeMass (P i) χ := by
    rw [← Finset.sum_subset (Finset.range_mono hd)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left (Finset.mem_range.mp hi)]
    · intro i _ hi
      rw [ite_eq_right (by simpa using hi)]
  rw [he,← Finset.mul_sum]
  simp only [one_div,inv_pow]

lemma outcomeMass_disjoint_or {α : Type*} [Fintype α] (ψ : α→ℂ) (P R : α→Prop)
    (h : ∀ x, ¬(P x ∧ R x)) :
    outcomeMass (fun x => P x ∨ R x) ψ=outcomeMass P ψ+outcomeMass R ψ := by
  classical
  unfold outcomeMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x <;> by_cases hr : R x
  · exact False.elim (h x ⟨hp,hr⟩)
  all_goals simp [hp,hr]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_HadamardAction
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma hadamardAt_symmetric {q : ℕ} (j : Fin q) (x y : Basis q) :
    (hadamardAt j).matrix x y = (hadamardAt j).matrix y x := by
  rw [hadamardAt_matrix, hadamardAt_matrix]
  have h : (∀ i, i ≠ j → x i = y i) ↔ (∀ i, i ≠ j → y i = x i) := by
    constructor <;> intro h i hi <;> exact (h i hi).symm
  simp only [h, Bool.and_comm]

lemma hadamardAt_apply_direct_sum {q : ℕ} (j : Fin q) (ψ : State q) (x : Basis q) :
    (hadamardAt j).matrix.mulVec ψ x =
      (ψ (Function.update x j false) +
        (if x j then (-1:ℂ) else 1)*ψ (Function.update x j true)) / (Real.sqrt 2:ℂ) := by
  classical
  have h (y : Basis q) := congrFun (hadamardAt_basis j x) y
  rw [matrix_basisVector] at h
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVector] at h
  change (∑ y, (hadamardAt j).matrix x y * ψ y) = _
  simp_rw [hadamardAt_symmetric j x, h]
  simp only [mul_add, add_mul, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  cases x j <;> simp <;> ring

lemma localHadamard_apply {A : Type*} [Fintype A] {b : ℕ} (j : Fin b)
    (ψ : Basis b × A → ℂ) (v : Basis b × A) :
    (localHadamard (A:=A) j).mulVec ψ v =
      (ψ (Function.update v.1 j false,v.2) +
        (if v.1 j then (-1:ℂ) else 1)*ψ (Function.update v.1 j true,v.2)) /
          (Real.sqrt 2:ℂ) := by
  classical
  change (∑ u : Basis b × A, (if v.2=u.2 then (hadamardAt j).matrix v.1 u.1 else 0) * ψ u) = _
  simp only [Fintype.sum_prod_type, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  simpa only [Matrix.mulVec, dotProduct, ite_mul] using
    hadamardAt_apply_direct_sum j (fun d => ψ (d,v.2)) v.1

lemma localHadamard_basis {A : Type*} [Fintype A] [DecidableEq A] {b : ℕ} (j : Fin b)
    (u : Basis b × A) :
    (fun v => localHadamard (A:=A) j v u) =
      (Real.sqrt 2:ℂ)⁻¹ • (basisVector (Function.update u.1 j false,u.2) +
        (if u.1 j then (-1:ℂ) else 1) • basisVector (Function.update u.1 j true,u.2)) := by
  classical
  funext v
  have h := congrFun (hadamardAt_basis j u.1) v.1
  rw [matrix_basisVector] at h
  simp only [localHadamard, Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVector,
    Prod.ext_iff] at h ⊢
  by_cases hv : v.2=u.2
  · simp only [hv, and_true, ite_true, if_true]
    exact h
  · simp [hv]

/-- Logical H on data is physically H on the corresponding encoded wire,
provided the embedding preserves that bit and its two updates. -/
lemma encoded_hadamard {A : Type*} [Fintype A] [DecidableEq A] {b q : ℕ}
    (e : Basis b × A → Basis q) (j : Fin b) (t : Fin q)
    (hbit : ∀ u, e u t = u.1 j)
    (hupdate : ∀ u c, Function.update (e u) t c = e (Function.update u.1 j c,u.2))
    (ψ : Basis b × A → ℂ) :
    (hadamardAt t).matrix.mulVec (encodeState e ψ) =
      encodeState e ((localHadamard (A:=A) j).mulVec ψ) := by
  apply matrix_encodeState
  intro u
  rw [hadamardAt_basis, localHadamard_basis, hbit, hupdate, hupdate,
    encodeState_smul, encodeState_add, encodeState_smul, encodeState_basis, encodeState_basis]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RowNetwork
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

lemma rowIndex_val {b : ℕ} (j e : Fin b) (h : j.val ≤ e.val) :
    (rowIndex j e).val = b-1+j.val-e.val := by
  apply Nat.mod_eq_of_lt
  have := j.isLt
  omega

lemma rowNetwork_bit {b : ℕ} (j e : Fin b) (z : Bits b) :
    (rowNetwork j).eval z e = if j.val ≤ e.val ∧ e.val < b-1 then
      z (rowIndex j e) && z j else false := by
  rw [rowNetwork, eval_vector]
  split_ifs <;> simp_all

lemma rowNetwork_number {b : ℕ} (j : Fin b) (z : Bits b) :
    (bitsValue ((rowNetwork j).eval z)).toNat = rowShift j z := by
  classical
  rw [bitsValue_toNat]
  unfold rowShift
  simp_rw [rowNetwork_bit]
  have hand (a c : Bool) : (a && c).toNat = a.toNat*c.toNat := by
    cases a <;> cases c <;> rfl
  simp only [apply_ite Bool.toNat, Bool.toNat_false, mul_ite, mul_zero, hand, ← mul_assoc]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun e _ => rowIndex j e)
  · intro e he
    have h := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rowIndex_val j e h.1]
    omega
  · intro e he f hf hef
    have h₁ := (Finset.mem_filter.mp he).2
    have h₂ := (Finset.mem_filter.mp hf).2
    have hv := congrArg Fin.val hef
    rw [rowIndex_val j e h₁.1, rowIndex_val j f h₂.1] at hv
    exact Fin.ext (by omega)
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    let e : Fin b := ⟨b-1-i.val+j.val,by have := i.isLt; omega⟩
    have he : j.val ≤ e.val ∧ e.val < b-1 := by dsimp [e]; have := i.isLt; omega
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩, ?_⟩
    apply Fin.ext
    rw [rowIndex_val j e he.1]
    dsimp [e]
    have := i.isLt
    omega
  · intro e he
    have h := (Finset.mem_filter.mp he).2
    rw [rowIndex_val j e h.1]
    have hw : b-1-(b-1+j.val-e.val)+j.val = e.val := by
      have := e.isLt
      omega
    rw [hw]

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

lemma encode_injective (b : ℕ) : Function.Injective (encode b) := by
  intro u v h
  have he : Fin.append u.1 ((basisResidue b).symm u.2) =
      Fin.append v.1 ((basisResidue b).symm v.2) := by
    funext i
    have hh := congrFun h (⟨i.val,by dsimp [width,work]; omega⟩ : Fin (width b))
    simpa only [encode, packed_input] using hh
  apply Prod.ext
  · funext i
    have hh := congrFun he (i.castAdd b)
    simpa only [Fin.append_left] using hh
  · apply (basisResidue b).symm.injective
    funext i
    have hh := congrFun he (Fin.natAdd b i)
    simpa only [Fin.append_right] using hh

lemma encode_bit {b : ℕ} (u : Bits b × ZMod (2^b)) (j : Fin b) :
    encode b u (dataWire j) = u.1 j := by
  change packed (work b) (Fin.append u.1 ((basisResidue b).symm u.2)) (fun _ => false)
    (⟨(j.castAdd b).val,by dsimp [width,work]; omega⟩ : Fin (width b)) = _
  rw [packed_input, Fin.append_left]

lemma encode_update {b : ℕ} (u : Bits b × ZMod (2^b)) (j : Fin b) (c : Bool) :
    Function.update (encode b u) (dataWire j) c = encode b (Function.update u.1 j c,u.2) := by
  unfold encode
  rw [show dataWire j = (⟨(j.castAdd b).val,by dsimp [width,work]; omega⟩ : Fin (width b)) by rfl,
    packed_update_input, append_update_left]

lemma translate_encode {b : ℕ} (j : Fin b) (u : Bits b × ZMod (2^b)) :
    ControlledTranslation.translate (fun d => bitsValue ((rowNetwork j).eval d))
      (Fin.append u.1 ((basisResidue b).symm u.2)) =
      Fin.append u.1 ((basisResidue b).symm (u.2+(rowShift j u.1 : ZMod (2^b)))) := by
  simp only [ControlledTranslation.translate, ControlledTranslation.dataPart_append,
    ControlledTranslation.phasePart_append, bitsValue_residue_add]
  rw [basisResidue_eq, rowNetwork_number]

lemma translation_basis {b : ℕ} (j : Fin b) (u : Bits b × ZMod (2^b)) :
    (programMatrix (translation j)).mulVec (basisVector (encode b u)) =
      basisVector (encode b (rowPerm j u)) := by
  unfold translation encode
  rw [cleanPermutation_basis _ _ _ _ _ (ControlledTranslation.forward_backward _ _),
    ControlledTranslation.forward_correct, translate_encode]
  rfl

lemma translation_apply {b : ℕ} (j : Fin b) (ψ : Bits b × ZMod (2^b) → ℂ) :
    (programMatrix (translation j)).mulVec (encodeState (encode b) ψ) =
      encodeState (encode b) (ψ ∘ (rowPerm j).symm) :=
  matrix_encode_permutation _ _ _ (translation_basis j) ψ

lemma rowCircuit_apply {b : ℕ} (j : Fin b) (ψ : Bits b × ZMod (2^b) → ℂ) :
    (programMatrix (rowCircuit j)).mulVec (encodeState (encode b) ψ) =
      encodeState (encode b) (fun u =>
        (ψ (Function.update u.1 j false,u.2-(rowShift j u.1 : ZMod (2^b))) +
          (if u.1 j then (-1:ℂ) else 1)*
            ψ (Function.update u.1 j true,u.2-(rowShift j u.1 : ZMod (2^b)))) /
              (Real.sqrt 2:ℂ)) := by
  rw [rowCircuit, programMatrix_append, programMatrix_singleton, ← Matrix.mulVec_mulVec,
    encoded_hadamard (encode b) j (dataWire j) (fun u => encode_bit u j)
      (fun u c => encode_update u j c), translation_apply]
  congr 1
  funext u
  exact localHadamard_apply j ψ ((rowPerm j).symm u)

lemma triPrefix_apply {b : ℕ} (x : Bits b) (χ : ZMod (2^b) → ℂ) (k : ℕ) (hk : k ≤ b) :
    (programMatrix (triPrefix b k hk)).mulVec
        (encodeState (encode b) (fun u => if u.1=x then χ u.2 else 0)) =
      encodeState (encode b) (fun u =>
        evolve (fun j z => (rowShift j z : ZMod (2^b))) x χ k hk u.1 u.2) := by
  induction k with
  | zero => rw [triPrefix, programMatrix_nil, Matrix.one_mulVec]; rfl
  | succ k ih =>
    rw [triPrefix, programMatrix_append, ← Matrix.mulVec_mulVec, ih (by omega), rowCircuit_apply]
    rfl

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularKernel
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open OrderTrial

lemma phase_half (x : ℝ) : phase (x+1/2) = -phase x := by
  rw [show x+1/2 = (x+1/4)+1/4 by ring, phase_quarter, phase_quarter]
  simp only [neg_mul, mul_neg, neg_neg, ← mul_assoc, Complex.I_mul_I]
  ring

lemma phase_nat_half (x : ℝ) (h : ℕ) :
    phase (x+(h:ℝ)/2) = (-1:ℂ)^h*phase x := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show x+((h+1:ℕ):ℝ)/2 = (x+(h:ℝ)/2)+1/2 by push_cast; ring,
      phase_half, ih, pow_succ]
    ring

lemma phase_product {b : ℕ} (hb : 1 ≤ b) (x y : Bits b) :
    phase ((inputNumber x : ℝ)*outputNumber y/(2:ℝ)^b) =
      (-1:ℂ)^dot x y * phase ((∑ i, ∑ j, lowTerm x y i j : ℕ)/(2:ℝ)^b) := by
  have hq : (2:ℝ)^b ≠ 0 := by positivity
  have hh : 2*(2:ℝ)^(b-1) = (2:ℝ)^b := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hb]
  have hd := congrArg (Nat.cast : ℕ → ℝ) (product_decomposition x y)
  push_cast at hd
  have he : (inputNumber x : ℝ)*outputNumber y/(2:ℝ)^b =
      (∑ i, ∑ j, lowTerm x y i j : ℕ)/(2:ℝ)^b + (dot x y : ℝ)/2 +
        (∑ i, ∑ j, highTerm x y i j : ℕ) := by
    push_cast
    rw [hd]
    field_simp
    nlinarith [hh]
  rw [he]
  have hp := phase_add_int
    ((∑ i, ∑ j, lowTerm x y i j : ℕ)/(2:ℝ)^b + (dot x y : ℝ)/2)
    ((∑ i, ∑ j, highTerm x y i j : ℕ) : ℤ)
  simp only [Int.cast_natCast] at hp
  rw [hp, phase_nat_half]

lemma residuePhase_correlation (a D : ℕ) :
    (∑ z : ZMod (2^(a+2)), star (residuePhase a (z+(D:ZMod (2^(a+2))))) *
      residuePhase a z) = phase ((D:ℝ)/(2:ℝ)^(a+2)) := by
  have hQ : 2^(a+2) = 4*2^a := by ring
  rw [← Equiv.sum_comp (ZMod.finEquiv (2^(a+2))).toEquiv]
  have hv {n : ℕ} [NeZero n] (z : Fin n) : ((ZMod.finEquiv n).toEquiv z).val = z.val := by
    cases n with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ n => rfl
  simp only [residuePhase, ZMod.val_add, ZMod.val_natCast,
    hv, Nat.add_mod_mod]
  change (∑ x : Fin (2^(a+2)), (fun t : ℕ => star (phaseState (2^a)
    ((t+D) % 2^(a+2))) * phaseState (2^a) t) x.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => star (phaseState (2^a)
    ((t+D) % 2^(a+2))) * phaseState (2^a) t) (2^(a+2)), hQ,
    phaseState_overlap (by positivity)]
  congr 1
  push_cast
  ring

/-- The full triangular coherent path expansion has exactly the manuscript's
selected kernel, after the phase register is tested in its prepared state. -/
theorem selected_kernel (a : ℕ) (x y : Bits (a+2)) :
    (∑ z : ZMod (2^(a+2)), star (residuePhase a z) *
      evolve (fun j v => (rowShift j v : ZMod (2^(a+2)))) x (residuePhase a)
        (a+2) le_rfl y z) =
      (Real.sqrt ((2:ℝ)^(a+2)) : ℂ)⁻¹ *
        phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(a+2)) := by
  rw [selected_evolve, pathWeight_full, pathShift_rows,
    residuePhase_correlation, phase_product (by omega), hadamard_normalization]
  ring

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

lemma encode_phase {b : ℕ} (u : Bits b × ZMod (2^b)) :
    encode b u ∘ phaseRegister b = (basisResidue b).symm u.2 := by
  funext i
  change packed (work b) (Fin.append u.1 ((basisResidue b).symm u.2)) (fun _ => false)
    (⟨(Fin.natAdd b i).val,by dsimp [width,work]; omega⟩ : Fin (width b)) = _
  rw [packed_input, Fin.append_right]

lemma encode_outside_phase {b : ℕ} (x : Bits b) (z z' : ZMod (2^b))
    (i : (phaseRegister b).Unused) : encode b (x,z) i.val = encode b (x,z') i.val := by
  by_cases hi : i.val.val < b+b
  · have hlo : i.val.val < b := by
      by_contra hn
      have hv : phaseRegister b ⟨i.val.val-b,by omega⟩ = i.val := by
        apply Fin.ext
        change b+(i.val.val-b) = i.val.val
        omega
      exact i.property _ hv
    have he : i.val = (⟨(Fin.castAdd b (⟨i.val.val,hlo⟩ : Fin b)).val,
        by dsimp [width,work]; omega⟩ : Fin (width b)) := Fin.ext rfl
    rw [he]
    simp only [encode, packed_input, Fin.append_left]
  · simp [encode, packed, hi]

lemma encode_replace_phase {b : ℕ} (x : Bits b) (z : ZMod (2^b)) (v : Basis b) :
    (phaseRegister b).replace (encode b (x,z)) v = encode b (x,basisResidue b v) := by
  apply (phaseRegister b).split.injective
  apply Prod.ext
  · rw [Register.replace, Equiv.apply_symm_apply]
    change v = encode b (x,basisResidue b v) ∘ phaseRegister b
    rw [encode_phase, Equiv.symm_apply_apply]
  · funext i
    change (phaseRegister b).replace (encode b (x,z)) v i.val = _
    rw [Register.replace_outside]
    exact encode_outside_phase x z _ i

lemma preparation_basis (a : ℕ) (x : Bits (a+2)) :
    (programMatrix (preparation a)).mulVec (basisVector (encode (a+2) (x,0))) =
      encodeState (encode (a+2)) (fun u => if u.1=x then residuePhase a u.2 else 0) := by
  classical
  rw [preparation, Register.placed_basis_state, encode_phase]
  have hz : (basisResidue (a+2)).symm 0 = (fun _ => false) := by
    apply (basisResidue (a+2)).injective
    rw [Equiv.apply_symm_apply, basisResidue_zero]
  rw [hz]
  unfold encodeState
  simp only [preparePhase_label, encode_replace_phase, Fintype.sum_prod_type,
    ite_smul, zero_smul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [← Equiv.sum_comp (basisResidue (a+2))]
  apply Finset.sum_congr rfl
  intro v _
  rw [residuePhase, basisResidue_val]

/-- The exact selected matrix entry of an actual fixed-gate circuit. -/
theorem transform_selected (a : ℕ) (x y : Bits (a+2)) :
    (programMatrix (transform a)).mulVec (basisVector (encode (a+2) (x,0)))
      (encode (a+2) (y,0)) =
      (Real.sqrt ((2:ℝ)^(a+2)) : ℂ)⁻¹ *
        OrderTrial.phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(a+2)) := by
  classical
  rw [transform, programMatrix_append, programMatrix_append,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    preparation_basis, triPrefix_apply, programMatrix_reverse]
  change (programMatrix (preparation a)).conjTranspose.mulVec _ _ = _
  rw [encoded_adjoint_test (encode (a+2)) (encode_injective (a+2)) _ _ _ _
    (preparation_basis a y)]
  simp only [Fintype.sum_prod_type, apply_ite, star_zero, zero_mul, ite_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  exact selected_kernel a x y

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSampleCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Actual modular-power/triangular-transform order sampler. All arithmetic
inputs are read-only wires; the modular output remains coherent. -/
namespace ExactQuantumFactoring.OrderSample
open scoped BigOperators
open BooleanNetwork Triangular

lemma powerInputs_eval {w b : ℕ} (a m : Basis w) (x : Basis b) :
    (powerInputs w b).eval (inputWord a m x) = Fin.append (Fin.append a m) x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [powerInputs,eval_select,Function.comp_apply,Fin.addCases_left,inputWord,
      Fin.append_left]
  · simp only [powerInputs,eval_select,Function.comp_apply,Fin.addCases_right,inputWord,
      Fin.append_right,Triangular.encode_bit]

lemma powerNetwork_value {w b : ℕ} (a m : Basis w) (x : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (bitsValue ((powerNetwork w b).eval (inputWord a m x))).toNat =
      (bitsValue a).toNat^inputNumber x % (bitsValue m).toNat := by
  rw [powerNetwork,eval_comp,powerInputs_eval,BitArithmetic.modularPower_value _ _ _ hm,
    BitArithmetic.horner_full]

lemma powerNetwork_eq {w b : ℕ} (a m : Basis w) (x : Basis b) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (powerNetwork w b).eval (inputWord a m x)=u ↔
      (bitsValue a).toNat^inputNumber x % (bitsValue m).toNat=(bitsValue u).toNat := by
  rw [← powerNetwork_value a m x hm]
  constructor
  · intro h; rw [h]
  · intro h
    exact (bitsEquiv w).injective (BitVec.eq_of_toNat_eq h)

lemma transform_entry {w s : ℕ} (a m : Basis w) (x y : Basis (s+2)) :
    programMatrix (rightProgram (w+w) (Triangular.transform s))
      (inputWord a m y) (inputWord a m x) =
    (Real.sqrt ((2:ℝ)^(s+2)):ℂ)⁻¹ *
      OrderTrial.phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(s+2)) := by
  rw [inputWord,inputWord,rightProgram_entry]
  have hh := Triangular.transform_selected s x y
  simpa only [matrix_basisVector] using hh

/-- The physically produced selected amplitude, expressed as a finite word sum. -/
lemma program_amplitude {w s : ℕ} (a m : Basis w) (y : Basis (s+2)) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (programMatrix (program w s)).mulVec (uniformInput w (s+2) a m) (word a m y u) =
      ((2:ℂ)^(s+2))⁻¹ * ∑ x : Basis (s+2),
        if (bitsValue a).toNat^inputNumber x % (bitsValue m).toNat=(bitsValue u).toNat
        then OrderTrial.phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(s+2)) else 0 := by
  classical
  rw [program,uniformInput]
  change (programMatrix (sampleProgram _ _ _)).mulVec
    (encodeState (fun x : Basis (s+2) => packed _ (inputWord a m x) (fun _ => false)) _)
    (packed _ (inputWord a m y) u) = _
  rw [sampleProgram_encoded_amplitude]
  simp_rw [powerNetwork_eq a m _ u hm,transform_entry]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · have hh : (Real.sqrt ((2:ℝ)^(s+2)):ℂ)^2 = (2:ℂ)^(s+2) := by
      rw [← Complex.ofReal_pow,Real.sq_sqrt (by positivity),Complex.ofReal_pow]
      rfl
    rw [← hh]
    ring
  · simp

lemma inputNumber_sum (b : ℕ) (f : ℕ → ℂ) :
    (∑ x : Basis b, f (inputNumber x)) = ∑ x ∈ Finset.range (2^b), f x := by
  let e : Basis b ≃ Fin (2^b) := Equiv.ofBijective _ (Triangular.inputNumber_bijective b)
  rw [← Fin.sum_univ_eq_sum_range]
  exact e.sum_comp (fun x => f x.val)

/-- Exactly 1/Q times the coherent modular-power residue sum of Section3. -/
theorem program_amplitude_range {w s : ℕ} (a m : Basis w) (y : Basis (s+2)) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (programMatrix (program w s)).mulVec (uniformInput w (s+2) a m) (word a m y u) =
      ((2^(s+2):ℕ):ℂ)⁻¹ * ∑ x ∈ Finset.range (2^(s+2)),
        if (bitsValue a).toNat^x % (bitsValue m).toNat=(bitsValue u).toNat
        then OrderTrial.phase ((outputNumber y:ℝ)*x/(2^(s+2):ℕ)) else 0 := by
  rw [program_amplitude a m y u hm]
  push_cast
  simp_rw [mul_comm (inputNumber _ : ℝ) (outputNumber y : ℝ)]
  congr 1
  exact inputNumber_sum (s+2) (fun x =>
    if (bitsValue a).toNat^x % (bitsValue m).toNat=(bitsValue u).toNat
    then OrderTrial.phase ((outputNumber y:ℝ)*x/(2:ℝ)^(s+2)) else 0)

end ExactQuantumFactoring.OrderSample


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_InitialOrderState
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma encodeState_comp {α : Type*} [Fintype α] {p q : ℕ}
    (e : α → Basis p) (f : Basis p → Basis q) (ψ : α → ℂ) :
    encodeState f (encodeState e ψ) = encodeState (f ∘ e) ψ := by
  classical
  change encodeState f (∑ a, ψ a • basisVector (e a)) = _
  rw [encodeState_sum]
  simp_rw [encodeState_smul,encodeState_basis]
  rfl

namespace Triangular

lemma encode_data {b : ℕ} (u : Bits b × ZMod (2^b)) :
    encode b u ∘ dataRegister b = u.1 := by
  funext i
  exact encode_bit u i

lemma encode_outside_data {b : ℕ} (x y : Bits b) (z : ZMod (2^b))
    (i : (dataRegister b).Unused) : encode b (x,z) i.val = encode b (y,z) i.val := by
  have hi : ¬i.val.val < b := by
    intro hi
    exact i.property ⟨i.val.val,hi⟩ rfl
  by_cases hh : i.val.val < b+b
  · have he : i.val = (⟨(Fin.natAdd b (⟨i.val.val-b,by omega⟩ : Fin b)).val,
        by dsimp [width,work]; omega⟩ : Fin (width b)) := by
      apply Fin.ext
      change i.val.val = b+(i.val.val-b)
      omega
    rw [he]
    simp only [encode,packed_input,Fin.append_right]
  · simp [encode,packed,hh]

lemma encode_replace_data {b : ℕ} (x y : Bits b) (z : ZMod (2^b)) :
    (dataRegister b).replace (encode b (x,z)) y = encode b (y,z) := by
  apply (dataRegister b).split.injective
  apply Prod.ext
  · rw [Register.replace,Equiv.apply_symm_apply]
    exact (encode_data (y,z)).symm
  · funext i
    change (dataRegister b).replace (encode b (x,z)) y i.val = _
    rw [Register.replace_outside]
    exact encode_outside_data x y z i

lemma uniformPreparation_zero (b : ℕ) :
    (programMatrix (uniformPreparation b)).mulVec
      (basisVector (encode b ((fun _ => false),0))) =
    encodeState (fun x => encode b (x,0))
      (fun _ => (Real.sqrt ((2:ℝ)^b):ℂ)⁻¹) := by
  rw [uniformPreparation,Register.placed_basis_state,encode_data,hadamards_zero]
  change encodeState (fun y => (dataRegister b).replace (encode b ((fun _ => false),0)) y)
    (fun _ => (Real.sqrt 2:ℂ)⁻¹^b) = _
  simp_rw [encode_replace_data,hadamard_normalization]

end Triangular
namespace OrderSample

lemma initial_zero (w b : ℕ) (a m : Basis w) :
    (programMatrix (initial w b)).mulVec
      (basisVector (word a m (fun _ => false) (fun _ => false))) = uniformInput w b a m := by
  rw [initial,word,firstProgram_basis,inputWord,rightProgram_basis,
    Triangular.uniformPreparation_zero,encodeState_comp,encodeState_comp]
  rfl

/-- Physical sampler starts from a computational basis vector, not an assumed
uniform state. Its selected entry is the exact residue-class interference sum. -/
theorem completeSampler_amplitude {w s : ℕ} (a m : Basis w) (y : Basis (s+2)) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (programMatrix (completeSampler w s)).mulVec
      (basisVector (word a m (fun _ => false) (fun _ => false))) (word a m y u) =
      ((2^(s+2):ℕ):ℂ)⁻¹ * ∑ x ∈ Finset.range (2^(s+2)),
        if (bitsValue a).toNat^x % (bitsValue m).toNat=(bitsValue u).toNat
        then OrderTrial.phase ((Triangular.outputNumber y:ℝ)*x/(2^(s+2):ℕ)) else 0 := by
  rw [completeSampler,programMatrix_append,← Matrix.mulVec_mulVec,initial_zero]
  exact program_amplitude_range a m y u hm

end OrderSample
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LabelRecoveryCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

lemma scanPairs_success {Q B k K : ℕ} :
    (scanPairs Q B k K).1≠0 ↔ ∃ i<K, (checkedPair Q B k i).1≠0 := by
  induction K with
  | zero => simp [scanPairs]
  | succ K ih =>
    simp only [scanPairs]
    split_ifs with h
    · exact ⟨fun _ => ⟨K,by omega,h⟩,fun _ => h⟩
    · rw [ih]
      constructor
      · rintro ⟨i,hi,hx⟩; exact ⟨i,by omega,hx⟩
      · rintro ⟨i,hi,hx⟩
        refine ⟨i,?_,hx⟩
        by_contra hh
        have he : i=K := by omega
        exact h (he ▸ hx)

lemma scanPairs_sound {Q B k K : ℕ} (h : (scanPairs Q B k K).1≠0) :
    IsBinLabel Q B k (scanPairs Q B k K) := by
  induction K with
  | zero => simp [scanPairs] at h
  | succ K ih =>
    simp only [scanPairs] at h ⊢
    split_ifs at h ⊢ with hh
    · exact checkedPair_sound hh
    · exact ih h

lemma scanPairs_complete {s Q B k : ℕ} {l : ℕ×ℕ} (hQ : B^2≤Q) (hsize : Q<2^s)
    (hl : IsBinLabel Q B k l) : scanPairs Q B k (2*s+1)=l := by
  obtain ⟨_,i,hi,he⟩ := mem_recoveredLabels.mp (recoveredLabels_complete hQ hsize hl)
  rw [convergentPair_label] at he
  have hh : (checkedPair Q B k i).1≠0 := checkedPair_nonzero_iff.mpr (he ▸ hl)
  have hs := scanPairs_success.mpr (⟨i,by omega,hh⟩ : ∃ i<2*s+1, (checkedPair Q B k i).1≠0)
  exact (scanPairs_sound hs).unique hQ hl

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma selectedSampleAmplitude_residue {G : Type*} [Group G]
    (Q j : ℕ) (a : G) {t : ℕ} (ht : t < orderOf a) :
    selectedSampleAmplitude Q (bin Q (orderOf a) j) a (a^t) =
      residueAmplitude Q (orderOf a) j t := by
  classical
  unfold selectedSampleAmplitude residueAmplitude
  congr 1
  simp_rw [pow_inj_mod, Nat.mod_eq_of_lt ht]
  exact (Finset.sum_filter _ _).symm

lemma selectedSampleProbability_residue {G : Type*} [Group G]
    (Q j : ℕ) (a : G) {t : ℕ} (ht : t < orderOf a) :
    Complex.normSq (selectedSampleAmplitude Q (bin Q (orderOf a) j) a (a^t)) =
      residueProbability Q (orderOf a) j t := by
  rw [selectedSampleAmplitude_residue Q j a ht]
  exact Complex.normSq_eq_norm_sq _

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSamplerMass
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness
namespace OrderTrial

lemma powerOrbit_injective {G : Type*} [Group G] (a : G) : Function.Injective (powerOrbit a) := by
  intro s t h
  apply Fin.ext
  exact pow_injOn_Iio_orderOf s.isLt t.isLt h

lemma selectedSampleAmplitude_outside {G : Type*} [Group G] [Finite G]
    (Q k : ℕ) (a u : G) (hu : u ∉ Set.range (powerOrbit a)) :
    selectedSampleAmplitude Q k a u=0 := by
  have h : ∀ x : ℕ, a^x≠u := by
    intro x hx
    apply hu
    refine ⟨⟨x%orderOf a,Nat.mod_lt _ (orderOf_pos a)⟩,?_⟩
    exact (pow_mod_orderOf a x).trans hx
  simp [selectedSampleAmplitude,h]

lemma selectedSampleProbability_sum {G : Type*} [Group G] [Fintype G]
    (Q j : ℕ) (a : G) :
    (∑ u : G, Complex.normSq (selectedSampleAmplitude Q (bin Q (orderOf a) j) a u))=
      ∑ t : Fin (orderOf a), residueProbability Q (orderOf a) j t.val := by
  classical
  let e := powerOrbit a
  have he : Function.Injective e := powerOrbit_injective a
  have hz : ∀ u ∈ (Finset.univ : Finset G), u∉Finset.univ.image e →
      Complex.normSq (selectedSampleAmplitude Q (bin Q (orderOf a) j) a u)=0 := by
    intro u _ hu
    rw [selectedSampleAmplitude_outside Q _ a u]
    · exact map_zero _
    · rintro ⟨t,rfl⟩
      exact hu (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  apply Finset.sum_congr rfl
  intro t _
  exact selectedSampleProbability_residue Q j a t.isLt

lemma natBasis_value (w z : ℕ) : (bitsValue (natBasis w z)).toNat=z%2^w := by
  change (bitsValue (fun i : Fin w => (BitVec.ofNat w z).getLsbD i.val)).toNat=z%2^w
  exact congrArg BitVec.toNat (bitsValue_bits (BitVec.ofNat w z))
lemma unitWord_value {m w : ℕ} [NeZero m] (hm : m<2^w) (u : (ZMod m)ˣ) :
    (bitsValue (unitWord (w:=w) u)).toNat=(u : ZMod m).val := by
  rw [unitWord,natBasis_value,Nat.mod_eq_of_lt ((ZMod.val_lt _).trans hm)]
lemma unitWord_injective {m w : ℕ} [NeZero m] (hm : m<2^w) :
    Function.Injective (unitWord (m:=m) (w:=w)) := by
  intro u v h
  apply Units.ext
  apply ZMod.val_injective
  have hh := congrArg (fun x : Basis w => (bitsValue x).toNat) h
  simpa only [unitWord_value hm] using hh

lemma nat_pow_eq_unit {m a : ℕ} [NeZero m] (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (x : ℕ) :
    a^x%m=((u^x : (ZMod m)ˣ) : ZMod m).val := by
  rw [Units.val_pow_eq_pow_val,← ha,← Nat.cast_pow,ZMod.val_natCast]

lemma nat_pow_eq_word_iff {m w a : ℕ} [NeZero m] (hm : m<2^w)
    (u v : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) (x : ℕ) :
    a^x%m=(bitsValue (unitWord (w:=w) v)).toNat ↔ u^x=v := by
  rw [unitWord_value hm,nat_pow_eq_unit u ha]
  exact ⟨fun h => Units.ext (ZMod.val_injective _ h),fun h => by rw [h]⟩

/-- The physical amplitude, at any encoded unit, equals the group-theoretic
coherent residue sum. No early classical measurement is used here. -/
theorem sampler_unit_amplitude {w s : ℕ} (a m : Basis w) (y : Basis (s+2))
    (hm : 2≤(bitsValue m).toNat) (u v : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat)) :
    (programMatrix (OrderSample.completeSampler w s)).mulVec
      (basisVector (OrderSample.word a m (fun _=>false) (fun _=>false)))
      (OrderSample.word a m y (unitWord (w:=w) v))=
      selectedSampleAmplitude (2^(s+2)) (Triangular.outputNumber y) u v := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  rw [OrderSample.completeSampler_amplitude _ _ _ _ hm]
  simp only [selectedSampleAmplitude,nat_pow_eq_word_iff (bitsValue m).isLt u v ha]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl


lemma outcomeMass_range {α β : Type*} [Fintype α] [Fintype β]
    (e : α→β) (he : Function.Injective e) (ψ : β→ℂ) :
    outcomeMass (fun y => y∈Set.range e) ψ=∑ a, Complex.normSq (ψ (e a)) := by
  classical
  let f : β→ℝ := fun y => if y∈Set.range e then Complex.normSq (ψ y) else 0
  have hh : outcomeMass (fun y => y∈Set.range e) ψ=Finset.univ.sum f := by
    unfold outcomeMass
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [f]
    split_ifs <;> rfl
  rw [hh]
  have hz : ∀ y∈(Finset.univ : Finset β), y∉Finset.univ.image e → f y=0 := by
    intro y _ hy
    dsimp only [f]
    rw [ite_eq_right]
    rintro ⟨a,rfl⟩
    exact hy (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  apply Finset.sum_congr rfl
  intro t _
  exact ite_eq_left ⟨t,rfl⟩

lemma sampler_word_injective {w b : ℕ} (a m : Basis w) (y : Basis b) :
    Function.Injective (OrderSample.word a m y) := by
  intro u v h
  have hh := BooleanNetwork.packed_injective
    (a₁:=(OrderSample.inputWord a m y,u)) (a₂:=(OrderSample.inputWord a m y,v)) h
  exact congrArg Prod.snd hh

lemma sampler_outside_units {w s : ℕ} (a m : Basis w) (y : Basis (s+2))
    (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (z : Basis w) (hz : z∉Set.range (unitWord (m:=(bitsValue m).toNat) (w:=w))) :
    samplerState a m (OrderSample.word a m y z)=0 := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  have hh : ∀ x : ℕ, (bitsValue a).toNat^x%(bitsValue m).toNat≠(bitsValue z).toNat := by
    intro x hx
    apply hz
    refine ⟨u^x,?_⟩
    apply (bitsEquiv w).injective
    apply BitVec.eq_of_toNat_eq
    change (bitsValue (unitWord (w:=w) (u^x))).toNat=(bitsValue z).toNat
    rw [unitWord_value (bitsValue m).isLt,← nat_pow_eq_unit u ha]
    exact hx
  rw [samplerState,OrderSample.completeSampler_amplitude _ _ _ _ hm]
  simp only [hh,ite_false, if_false,Finset.sum_const_zero,mul_zero]

/-- The complete physical selected-bin probability is the sum of the literal
residue probabilities at the TRUE order. False labels are not identified with
artificial probabilities. -/
theorem sampler_selected_bin_mass {w s : ℕ} (a m : Basis w) (y : Basis (s+2))
    (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (j : ℕ) (hy : Triangular.outputNumber y=bin (2^(s+2)) (orderOf u) j) :
    outcomeMass (fun z => z∈Set.range (OrderSample.word a m y)) (samplerState a m)=
      ∑ t : Fin (orderOf u), residueProbability (2^(s+2)) (orderOf u) j t.val := by
  classical
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  rw [outcomeMass_range _ (sampler_word_injective a m y)]
  let e := unitWord (m:=(bitsValue m).toNat) (w:=w)
  have he : Function.Injective e := unitWord_injective (bitsValue m).isLt
  have hz : ∀ z∈(Finset.univ : Finset (Basis w)), z∉Finset.univ.image e →
      Complex.normSq (samplerState a m (OrderSample.word a m y z))=0 := by
    intro z _ hz
    rw [sampler_outside_units a m y hm u ha z]
    · exact map_zero _
    · rintro ⟨v,rfl⟩
      exact hz (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  simp only [e,samplerState,sampler_unit_amplitude a m y hm u _ ha,hy]
  exact selectedSampleProbability_sum _ j u

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SamplerLabels
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork

lemma sampleY_word {w b : ℕ} (a m u : Basis w) (y : Basis b) :
    sampleY (OrderSample.word a m y u)=y := by
  funext i
  change (OrderSample.word a m y u) _=y i
  exact (packed_input (OrderSample.inputWord a m y) u (Fin.natAdd (w+w) (Triangular.dataWire i))).trans
    (by simp only [OrderSample.inputWord,Fin.append_right,Triangular.encode_bit])
lemma sampleU_word {w b : ℕ} (a m u : Basis w) (y : Basis b) :
    sampleU (OrderSample.word a m y u)=u := by
  funext i
  exact packed_target _ _ i

lemma sampleSelected_word {w b : ℕ} (a m u : Basis w) (y : Basis b) :
    SampleSelected a m (OrderSample.word a m y u) := by
  rw [SampleSelected,sampleY_word,sampleU_word]

lemma sampleY_number_injective (b : ℕ) : Function.Injective (@Triangular.outputNumber b) := by
  intro x y h
  apply (bitsEquiv b).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue x).toNat=(bitsValue y).toNat
  simpa only [bitsValue_toNat,Triangular.outputNumber] using h

lemma natBasis_outputNumber (b k : ℕ) : Triangular.outputNumber (natBasis b k)=k%2^b := by
  rw [Triangular.outputNumber,← bitsValue_toNat,natBasis_value]

lemma scanPairs_eq_iff {s Q B k : ℕ} (hQ : B^2≤Q) (hsize : Q<2^s)
    {d j : ℕ} (hd : 0<d) (hdB : d<B) (hj : j<d) (hcop : Nat.Coprime j d) :
    scanPairs Q B k (2*s+1)=(d,j) ↔ bin Q d j=k := by
  constructor
  · intro h
    have hh : (scanPairs Q B k (2*s+1)).1≠0 := by rw [h]; omega
    have hs := scanPairs_sound hh
    rw [h] at hs
    exact hs.2.2.2.2
  · intro h
    exact scanPairs_complete hQ hsize ⟨hd,hdB,hj,hcop,h⟩

lemma selected_recovered_label {w b s B d j : ℕ} (a m : Basis w)
    (hB : B^2≤2^b) (hs : 2^b<2^s) (hd : 0<d) (hdB : d<B)
    (hj : j<d) (hcop : Nat.Coprime j d) :
    (fun x : Basis (OrderSample.width w b) => SampleSelected a m x ∧
      scanPairs (2^b) B (Triangular.outputNumber (sampleY x)) (2*s+1)=(d,j))=
    (fun x => x∈Set.range (OrderSample.word a m (natBasis b (bin (2^b) d j)))) := by
  funext x
  apply propext
  rw [scanPairs_eq_iff hB hs hd hdB hj hcop]
  have hdQ : d≤2^b := by
    have hbpos : 1≤B := by omega
    have hsq : B≤B*B := by simpa using Nat.mul_le_mul_left B hbpos
    nlinarith
  have hk : bin (2^b) d j<2^b := bin_lt hd hdQ hj
  constructor
  · rintro ⟨hx,hy⟩
    refine ⟨sampleU x,?_⟩
    have he : natBasis b (bin (2^b) d j)=sampleY x := by
      apply sampleY_number_injective b
      rw [natBasis_outputNumber,Nat.mod_eq_of_lt hk,hy]
    rw [he]
    exact hx.symm
  · rintro ⟨u,rfl⟩
    refine ⟨sampleSelected_word a m u _,?_⟩
    rw [sampleY_word,natBasis_outputNumber,Nat.mod_eq_of_lt hk]

/-- Recovery and selected-block checking are now linked to the ACTUAL physical
bin mass, without enumerating bins or residues in the circuit. -/
theorem sampler_recovered_label_mass {w b s B : ℕ} (a m : Basis w)
    (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hB : B^2≤2^(b+2)) (hs : 2^(b+2)<2^s) (hdB : orderOf u<B)
    (j : ℕ) (hj : j<orderOf u) (hcop : Nat.Coprime j (orderOf u)) :
    Exactness.outcomeMass (fun x : Basis (OrderSample.width w (b+2)) => SampleSelected a m x ∧
      scanPairs (2^(b+2)) B (Triangular.outputNumber (sampleY x)) (2*s+1)=(orderOf u,j))
      (samplerState (s:=b) a m)=
      ∑ t : Fin (orderOf u), residueProbability (2^(b+2)) (orderOf u) j t.val := by
  have hd : 0<orderOf u := orderOf_pos u
  rw [selected_recovered_label a m hB hs hd hdB hj hcop]
  apply sampler_selected_bin_mass a m _ hm u ha j
  have hdQ : orderOf u≤2^(b+2) := by
    have hbpos : 1≤B := by omega
    have hsq : B≤B*B := by simpa using Nat.mul_le_mul_left B hbpos
    nlinarith
  rw [natBasis_outputNumber,Nat.mod_eq_of_lt (bin_lt hd hdQ hj)]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialRetentionBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial

lemma first_remainder_bounds {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n) (j : ℕ) :
    0≤firstRetention n d j ∧ firstRetention n d j≤1 ∧
      0≤ modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j) ∧
      modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)≤2/(2:ℚ)^(10*n) := by
  have hB : 2≤2^n := by simpa using Nat.pow_le_pow_right (show 0<2 by decide) hn
  have hs := majorantSum_bounds hB hd hdB j
  have hsl : 1/(128*(d:ℚ))≤ majorantSum ((2^n)^16) (2^n) d j := by
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_one] using hs.1
  have hsu : majorantSum ((2^n)^16) (2^n) d j≤2 := by exact_mod_cast hs.2
  have hc := modeCoeff_bounds n hd hsl hsu
  exact ⟨hc.1,by change modeCoeff n _ _≤1; linarith [hc.2.1],hc.2.2⟩

lemma all_retention_bounds {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n) (j : ℕ)
    {t : ℕ} (ht : t<d) :
    (0≤firstRetention n d j ∧ firstRetention n d j≤1) ∧
      (0≤discrepancyRetention n d j t ∧ discrepancyRetention n d j t≤1) ∧
      (0 ≤ remainderRetention n d j ∧ remainderRetention n d j≤1) := by
  have hc := first_remainder_bounds hn hd hdB j
  have hB : 2≤2^n := by simpa using Nat.pow_le_pow_right (show 0<2 by decide) hn
  have hc₀ : (0:ℝ)≤(firstRetention n d j:ℝ) := by exact_mod_cast hc.1
  have hc₁ : (firstRetention n d j:ℝ)≤1 := by exact_mod_cast hc.2.1
  have hdisc := discrepancy_retention_bounds hB hd hdB ht j hc₀ hc₁
  have hdc : (discrepancyRetention n d j t:ℝ)=
      2*((2^n:ℕ):ℝ)^3*((majorant ((2^n)^16) (2^n) d j ((j*t)%d):ℝ)-
        residueProbability ((2^n)^16) d j t)*(firstRetention n d j:ℝ) := by
    simp only [discrepancyRetention,firstRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
      Rat.cast_sub,residueProbabilityRat_cast (by positivity : 0<(2^n)^16),Nat.cast_pow,Nat.cast_ofNat]
  rw [← hdc] at hdisc
  have hr₀ : (0:ℝ)≤(modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j):ℝ) := by
    exact_mod_cast hc.2.2.1
  have hr₁ : (modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j):ℝ)≤
      2/(2:ℝ)^(10*n) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hc.2.2.2
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hrem := remainder_retention_bounds hn hr₀ hr₁
  have hrc : (remainderRetention n d j:ℝ)=
      4*((2:ℝ)^n)^2*(modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j):ℝ) := by
    simp only [remainderRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
  rw [← hrc] at hrem
  exact ⟨⟨hc.1,hc.2.1⟩,by exact_mod_cast hdisc,by exact_mod_cast hrem⟩

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialGuessLaw
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness

lemma guess_normalized (n : ℕ) : ∑ x : Guesses n, Complex.normSq (guessState n x)=1 := by
  have h₁ := RecordedHistory.append_normalized (fairState n) (fun _ => fairState (retentionBits n))
    (fair_normalized n) (fun _ => fair_normalized _)
  have h₂ := RecordedHistory.append_normalized (fairState n)
    (fun _ => independentState (fairState n) (fairState (retentionBits n)))
    (fair_normalized n) (fun _ => h₁)
  exact RecordedHistory.append_normalized (fairState n)
    (fun _ => independentState (fairState n) (independentState (fairState n) (fairState (retentionBits n))))
    (fair_normalized n) (fun _ => h₂)

lemma firstPass_mass {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n) (j : ℕ) :
    outcomeMass (firstPass n d j) (guessState n)=(firstRetention n d j:ℝ) := by
  unfold firstPass guessState
  rw [independent_mass_right (fairState n) (independentState (fairState n)
      (independentState (fairState n) (fairState (retentionBits n))))
      (fun x => Retains (firstRetention n d j) x.2.2) (fair_normalized n),
    independent_mass_right (fairState n) (independentState (fairState n) (fairState (retentionBits n)))
      (fun x => Retains (firstRetention n d j) x.2) (fair_normalized n),
    independent_mass_right (fairState n) (fairState (retentionBits n)) (Retains (n:=n) (firstRetention n d j)) (fair_normalized n)]
  exact dyadic_fair_threshold (retentions_fixedDenominator hn hdB.le j 0).1
    (first_remainder_bounds hn hd hdB j).1 (first_remainder_bounds hn hd hdB j).2.1

lemma secondPass_mass {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n)
    (j : ℕ) (hj : j<d) :
    outcomeMass (secondPass n d j) (guessState n)=
      (1/((2:ℝ)^n)^3)*∑ t ∈ Finset.range d, (discrepancyRetention n d j t:ℝ) := by
  unfold secondPass guessState
  rw [
    independent_mass (fairState n) (independentState (fairState n)
      (independentState (fairState n) (fairState (retentionBits n))))
      (fun x => (bitsValue x).toNat=d)
      (fun x => (bitsValue x.1).toNat=j ∧ (bitsValue x.2.1).toNat<d ∧
        Retains (discrepancyRetention n d j (bitsValue x.2.1).toNat) x.2.2),fair_value_mass hdB,
    independent_mass (fairState n) (independentState (fairState n) (fairState (retentionBits n)))
      (fun x => (bitsValue x).toNat=j)
      (fun x => (bitsValue x.1).toNat<d ∧ Retains (discrepancyRetention n d j (bitsValue x.1).toNat) x.2),
    fair_value_mass (hj.trans hdB),
    fair_variable_append hdB.le (fairState (retentionBits n))
      (fun t => Retains (n:=n) (discrepancyRetention n d j t))]
  have he : (∑ t ∈ Finset.range d,
      outcomeMass (Retains (n:=n) (discrepancyRetention n d j t)) (fairState (retentionBits n)))=
      ∑ t ∈ Finset.range d, (discrepancyRetention n d j t:ℝ) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact dyadic_fair_threshold (retentions_fixedDenominator hn hdB.le j t).2.1
      (all_retention_bounds hn hd hdB j (Finset.mem_range.mp ht)).2.1.1
      (all_retention_bounds hn hd hdB j (Finset.mem_range.mp ht)).2.1.2
  rw [he]
  ring

lemma thirdPass_mass {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n)
    (j : ℕ) (hj : j<d) :
    outcomeMass (thirdPass n d j) (guessState n)=
      (1/((2:ℝ)^n)^2)*(remainderRetention n d j:ℝ) := by
  unfold thirdPass guessState
  rw [
    independent_mass (fairState n) (independentState (fairState n)
      (independentState (fairState n) (fairState (retentionBits n))))
      (fun x => (bitsValue x).toNat=d)
      (fun x => (bitsValue x.1).toNat=j ∧ Retains (remainderRetention n d j) x.2.2),fair_value_mass hdB,
    independent_mass (fairState n) (independentState (fairState n) (fairState (retentionBits n)))
      (fun x => (bitsValue x).toNat=j)
      (fun x => Retains (remainderRetention n d j) x.2),fair_value_mass (hj.trans hdB),
    independent_mass_right (fairState n) (fairState (retentionBits n)) (Retains (n:=n) (remainderRetention n d j)) (fair_normalized n)]
  have he : outcomeMass (Retains (n:=n) (remainderRetention n d j)) (fairState (retentionBits n))=
      (remainderRetention n d j:ℝ) :=
    dyadic_fair_threshold (retentions_fixedDenominator hn hdB.le j 0).2.2
      (all_retention_bounds hn hd hdB j hd).2.2.1
      (all_retention_bounds hn hd hdB j hd).2.2.2
  rw [he]
  ring

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialRawPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

namespace OrderTrial

lemma raw_normalized {w : ℕ} (s n : ℕ) (a m : Basis w) :
    ∑ x, Complex.normSq (rawState s n a m x)=1 := by
  have h := RecordedHistory.append_normalized (samplerState (s:=s) a m) (fun _ => guessState n)
    (basis_preparation_normalized (OrderSample.completeSampler w s) _) (fun _ => guess_normalized n)
  exact RecordedHistory.append_normalized (fairState 2)
    (fun _ => independentState (samplerState (s:=s) a m) (guessState n))
    (fair_normalized 2) (fun _ => h)

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTrialLaw
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness

lemma phaseScale_bounds {n s : ℕ} (_hn : 1≤n) (hs : 2^(s+2)=(2^n)^16) :
    (2^n)^2≤2^(s+2) ∧ 2^(s+2)<2^(s+3) := by
  constructor
  · rw [hs]
    exact Nat.pow_le_pow_right (by positivity) (by decide)
  · exact Nat.pow_lt_pow_right (by decide) (by omega)

lemma first_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (j : ℕ) (hj : j<orderOf u) (hcop : Nat.Coprime j (orderOf u)) :
    outcomeMass (modeFirst s n a m (orderOf u) j) (rawState s n a m)=
      firstModeMass n ((2^n)^16) (2^n) (orderOf u) j := by
  have hd : 0<orderOf u := orderOf_pos u
  have hsamp := sampler_recovered_label_mass (b:=s) (s:=s+3) a m hm u ha
    (phaseScale_bounds hn hs).1 (phaseScale_bounds hn hs).2 hdB j hj hcop
  have hsmass : outcomeMass (recovered (s:=s) a m n (orderOf u) j) (samplerState (s:=s) a m)=
      ∑ t : Fin (orderOf u), residueProbability (2^(s+2)) (orderOf u) j t.val := hsamp
  unfold modeFirst rawState
  rw [
    independent_mass (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))
      (fun x => (bitsValue x).toNat<2)
      (fun x => recovered a m n (orderOf u) j x.1 ∧ firstPass n (orderOf u) j x.2),
    fair_threshold_mass (by decide : 2≤2^2),
    independent_mass (samplerState (s:=s) a m) (guessState n) (recovered a m n (orderOf u) j) (firstPass n (orderOf u) j),
    firstPass_mass hn hd hdB j]
  rw [hsmass,Fin.sum_univ_eq_sum_range,hs]
  unfold firstModeMass firstRetention
  norm_num
  ring

lemma second_mass {w n s : ℕ} (hn : 1≤n) (a m : Basis w)
    {d : ℕ} (hd : 0<d) (hdB : d<2^n) (j : ℕ) (hj : j<d) :
    outcomeMass (modeSecond (w:=w) s n d j) (rawState s n a m)=
      secondModeMass n ((2^n)^16) (2^n) d j := by
  unfold modeSecond rawState
  rw [
    independent_mass (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))
      (fun x => (bitsValue x).toNat=2) (fun x => secondPass n d j x.2),
    fair_value_mass (by decide : 2<2^2),
    independent_mass_right (samplerState (s:=s) a m) (guessState n) (secondPass n d j)
      (basis_preparation_normalized (OrderSample.completeSampler w s) _),
    secondPass_mass hn hd hdB j hj]
  unfold secondModeMass
  rw [Finset.mul_sum]
  simp only [discrepancyRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_sub,
    residueProbabilityRat_cast (by positivity : 0<(2^n)^16),Nat.cast_pow,Nat.cast_ofNat]
  norm_num

lemma third_mass {w n s : ℕ} (hn : 1≤n) (a m : Basis w)
    {d : ℕ} (hd : 0<d) (hdB : d<2^n) (j : ℕ) (hj : j<d) :
    outcomeMass (modeThird (w:=w) s n d j) (rawState s n a m)=
      thirdModeMass n ((2^n)^16) (2^n) d j := by
  unfold modeThird rawState
  rw [
    independent_mass (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))
      (fun x => (bitsValue x).toNat=3) (fun x => thirdPass n d j x.2),
    fair_value_mass (by decide : 3<2^2),
    independent_mass_right (samplerState (s:=s) a m) (guessState n) (thirdPass n d j)
      (basis_preparation_normalized (OrderSample.completeSampler w s) _),
    thirdPass_mass hn hd hdB j hj]
  simp only [thirdModeMass,remainderRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
    Nat.cast_pow,Nat.cast_ofNat]
  norm_num
  ring

/-- True-order cancellation for the ACTUAL physical finite-gate experiment,
with all unselected sampler amplitudes, guesses, and retention coins retained. -/
theorem labelEvent_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (j : ℕ) (hj : j<orderOf u) (hcop : Nat.Coprime j (orderOf u)) :
    outcomeMass (labelEvent s n a m (orderOf u) j) (rawState s n a m)=
      (prescribedMass (orderOf u):ℝ) := by
  have hd : 0<orderOf u := orderOf_pos u
  unfold labelEvent
  rw [outcomeMass_disjoint_or _ _ _ (by
    intro x h
    rcases h with ⟨h0,h1|h2⟩
    · have h0 := h0.1; have h1 := h1.1; omega
    · have h0 := h0.1; have h2 := h2.1; omega),
    outcomeMass_disjoint_or _ _ _ (by
      intro x h
      have h1 := h.1.1; have h2 := h.2.1; omega),
    first_mass hn hs a m hm u ha hdB j hj hcop,
    second_mass hn a m hd hdB j hj,third_mass hn a m hd hdB j hj,← add_assoc]
  exact three_mode_mass (by positivity) hd hcop

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderCandidateLaw
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma outcomeMass_finite_union {α β : Type*} [Fintype α] [DecidableEq β]
    (ψ : α→ℂ) (S : Finset β) (E : β→α→Prop)
    (h : ∀ x j k, j∈S → k∈S → E j x → E k x → j=k) :
    outcomeMass (fun x => ∃ j∈S, E j x) ψ=∑ j∈S, outcomeMass (E j) ψ := by
  classical
  unfold outcomeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∃ j∈S, E j x
  · obtain ⟨j,hj,he⟩ := hx
    rw [ite_eq_left ⟨j,hj,he⟩,Finset.sum_eq_single j]
    · rw [ite_eq_left he]
    · intro k hk hkj
      exact ite_eq_right (fun hek => hkj (h x k j hk hj hek he))
    · exact fun hj' => False.elim (hj' hj)
  · rw [ite_eq_right hx]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun he => hx ⟨j,hj,he⟩)

namespace OrderTrial

lemma labelEvent_pair {w s n d j : ℕ} (a m : Basis w) (x : Raw w s n)
    (h : labelEvent s n a m d j x) : labelPair s n x=(d,j) := by
  rcases h with h|h|h
  · rw [labelPair,ite_eq_left h.1]
    exact h.2.1.2
  · have hm := h.1
    rw [labelPair,ite_eq_right (by omega)]
    exact Prod.ext h.2.1 h.2.2.1
  · have hm := h.1
    rw [labelPair,ite_eq_right (by omega)]
    exact Prod.ext h.2.1 h.2.2.1

lemma labelEvent_unique {w s n d j d' j' : ℕ} (a m : Basis w) (x : Raw w s n)
    (h : labelEvent s n a m d j x) (h' : labelEvent s n a m d' j' x) :
    d=d' ∧ j=j' := by
  have he := (labelEvent_pair a m x h).symm.trans (labelEvent_pair a m x h')
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

lemma trialResult_some {w s n d : ℕ} (a m : Basis w) (x : Raw w s n) :
    trialResult s n a m x=some d ↔ ∃ j,
      ValidLabel n (bitsValue a).toNat (bitsValue m).toNat d j ∧ labelEvent s n a m d j x := by
  classical
  unfold trialResult
  dsimp only
  split_ifs with h
  · constructor
    · intro hd
      have he := Option.some.inj hd
      exact ⟨(labelPair s n x).2,he ▸ h⟩
    · rintro ⟨j,hv,hl⟩
      rw [labelEvent_pair a m x hl]
  · constructor
    · intro hh; cases hh
    · rintro ⟨j,hv,hl⟩
      have he := labelEvent_pair a m x hl
      exact False.elim (h (by simpa only [he] using And.intro hv hl))

lemma validLabel_order_dvd {n a m d j : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (h : ValidLabel n a m d j) : orderOf u∣d := by
  let : NeZero m := ⟨by omega⟩
  apply orderOf_dvd_of_pow_eq_one
  apply Units.ext
  apply ZMod.val_injective
  rw [← nat_pow_eq_unit u ha d,h.2.2.2.2]
  exact (ZMod.val_one'' (by omega : m≠1)).symm

lemma true_validLabel {n a m : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (hdB : orderOf u<2^n)
    (j : ℕ) (hj : j<orderOf u) (hc : Nat.Coprime j (orderOf u)) :
    ValidLabel n a m (orderOf u) j := by
  let : NeZero m := ⟨by omega⟩
  refine ⟨orderOf_pos u,hdB,hj,hc,?_⟩
  rw [nat_pow_eq_unit u ha,pow_orderOf_eq_one,Units.val_one,ZMod.val_one'' (by omega : m≠1)]

lemma trialResult_multiple {w s n d : ℕ} (a m : Basis w) (hm : 2≤(bitsValue m).toNat)
    (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (x : Raw w s n) (h : trialResult s n a m x=some d) :
    0<d ∧ d<2^n ∧ orderOf u∣d := by
  obtain ⟨j,hv,_⟩ := (trialResult_some a m x).mp h
  exact ⟨hv.1,hv.2.1,validLabel_order_dvd hm u ha hv⟩

/-- The physical, validated order trial has the manuscript's exact true-order
mass phi(r)*lambda(r). False candidates remain in the recorded history. -/
theorem trialResult_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) :
    outcomeMass (fun x => trialResult s n a m x=some (orderOf u)) (rawState s n a m)=
      (Nat.totient (orderOf u):ℝ)*(prescribedMass (orderOf u):ℝ) := by
  classical
  let S := (Finset.range (orderOf u)).filter (fun j => Nat.Coprime j (orderOf u))
  have he : (fun x : Raw w s n => trialResult s n a m x=some (orderOf u))=
      (fun x => ∃ j∈S, labelEvent s n a m (orderOf u) j x) := by
    funext x
    apply propext
    rw [trialResult_some]
    constructor
    · rintro ⟨j,hv,hl⟩
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv.2.2.1,hv.2.2.2.1⟩,hl⟩
    · rintro ⟨j,hj,hl⟩
      have hj' := Finset.mem_filter.mp hj
      exact ⟨j,true_validLabel hm u ha hdB j (Finset.mem_range.mp hj'.1) hj'.2,hl⟩
  rw [he,outcomeMass_finite_union _ S _ (by
    intro x j k _ _ hj hk
    exact (labelEvent_unique a m x hj hk).2)]
  have hr : ∀ j∈S, outcomeMass (labelEvent s n a m (orderOf u) j) (rawState s n a m)=
      (prescribedMass (orderOf u):ℝ) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact labelEvent_mass hn hs a m hm u ha hdB j (Finset.mem_range.mp hj'.1) hj'.2
  rw [Finset.sum_congr rfl hr,Finset.sum_const,nsmul_eq_mul]
  congr 1
  norm_cast
  simp [S,Nat.totient,Nat.coprime_comm]

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RepeatedTrials
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


/-! Exact independent-trial laws and the source's K=n^5 success guarantee. -/
namespace ExactQuantumFactoring.RepeatedTrials
open scoped BigOperators
open ExactQuantumFactoring.Exactness

lemma tensor_normalized {α : Type*} [Fintype α] (ψ : α→ℂ) (K : ℕ)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    ∑ x : Fin K→α, Complex.normSq (tensorState ψ K x)=1 := by
  classical
  simp only [tensorState,map_prod]
  calc
    _ = (∑ x, Complex.normSq (ψ x))^K := (Fintype.sum_pow (fun x => Complex.normSq (ψ x)) K).symm
    _ = 1 := by rw [hψ,one_pow]

lemma tensor_all_mass {α : Type*} [Fintype α] (ψ : α→ℂ) (K : ℕ) (P : α→Prop) :
    outcomeMass (fun x : Fin K→α => ∀ i, P (x i)) (tensorState ψ K) = (outcomeMass P ψ)^K := by
  classical
  unfold outcomeMass tensorState
  calc
    _ = ∑ x : Fin K→α, ∏ i, if P (x i) then Complex.normSq (ψ (x i)) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ∀ i, P (x i)
      · simp [hx,map_prod]
      · obtain ⟨i,hi⟩ := not_forall.mp hx
        rw [ite_eq_right hx]
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    _ = _ := (Fintype.sum_pow (fun x => if P x then Complex.normSq (ψ x) else 0) K).symm

lemma mass_compl {α : Type*} [Fintype α] (ψ : α→ℂ) (P : α→Prop)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    outcomeMass (fun x => ¬P x) ψ=1-outcomeMass P ψ := by
  classical
  have he : outcomeMass (fun x => ¬P x) ψ + outcomeMass P ψ = 1 := by
    unfold outcomeMass
    rw [← Finset.sum_add_distrib,← hψ]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x <;> simp [hx]
  linarith

lemma tensor_some_mass {α : Type*} [Fintype α] (ψ : α→ℂ) (K : ℕ) (P : α→Prop)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    outcomeMass (fun x : Fin K→α => ∃ i, P (x i)) (tensorState ψ K) =
      1-(1-outcomeMass P ψ)^K := by
  classical
  have he : (fun x : Fin K→α => ∃ i, P (x i)) =
      (fun x => ¬∀ i, ¬P (x i)) := by funext x; simp
  rw [he,mass_compl _ _ (tensor_normalized ψ K hψ)]
  rw [tensor_all_mass ψ K (fun x => ¬P x),mass_compl ψ P hψ]

end ExactQuantumFactoring.RepeatedTrials


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTransition
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness RepeatedTrials

lemma minOption_some_mem {a b : Option ℕ} {d : ℕ} (h : minOption a b=some d) :
    a=some d ∨ b=some d := by
  cases a with
  | none => exact Or.inr h
  | some a =>
    cases b with
    | none => exact Or.inl h
    | some b =>
      have he : min a b=d := Option.some.inj h
      by_cases hab : a≤b
      · exact Or.inl (congrArg some ((min_eq_left hab).symm.trans he))
      · exact Or.inr (congrArg some ((min_eq_right (by omega)).symm.trans he))

lemma minimumCandidate_mem {as : List (Option ℕ)} {d : ℕ} (h : minimumCandidate as=some d) :
    some d∈as := by
  induction as with
  | nil => cases h
  | cons a as ih =>
    rcases minOption_some_mem h with hd|hd
    · exact List.mem_cons.mpr (Or.inl hd.symm)
    · exact List.mem_cons.mpr (Or.inr (ih hd))

lemma minimumCandidate_lower {as : List (Option ℕ)} {d r : ℕ}
    (h : ∀ a, some a∈as → r≤a) (hd : minimumCandidate as=some d) : r≤d :=
  h d (minimumCandidate_mem hd)

lemma minOption_eq_low {a b : Option ℕ} {r : ℕ}
    (ha : ∀ d, a=some d → r≤d) (hb : ∀ d, b=some d → r≤d) :
    minOption a b=some r ↔ a=some r ∨ b=some r := by
  constructor
  · exact minOption_some_mem
  · rintro (he|he)
    · subst a
      cases b with
      | none => rfl
      | some d => simp only [minOption,min_eq_left (hb d rfl)]
    · subst b
      cases a with
      | none => rfl
      | some d => simp only [minOption,min_eq_right (ha d rfl)]

lemma minimumCandidate_eq_low {as : List (Option ℕ)} {r : ℕ}
    (h : ∀ a, some a∈as → r≤a) : minimumCandidate as=some r ↔ some r∈as := by
  induction as with
  | nil => simp [minimumCandidate]
  | cons a as ih =>
    have ht : ∀ b, some b∈as → r≤b := fun b hb => h b (List.mem_cons_of_mem a hb)
    rw [minimumCandidate,minOption_eq_low (by
      intro d hd
      exact h d (List.mem_cons.mpr (Or.inl hd.symm))) (fun d hd => minimumCandidate_lower ht hd),ih ht]
    simp only [List.mem_cons,eq_comm]

lemma orderResult_eq_order {w s n K : ℕ} (a m : Basis w) (hm : 2≤(bitsValue m).toNat)
    (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (x : Fin K→Raw w s n) :
    orderResult s n a m K x=orderOf u ↔ ∃ i, trialResult s n a m (x i)=some (orderOf u) := by
  have hlow : ∀ d, some d∈List.ofFn (fun i => trialResult s n a m (x i)) → orderOf u≤d := by
    intro d hd
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hd
    have hh := trialResult_multiple a m hm u ha (x i) hi
    exact Nat.le_of_dvd hh.1 hh.2.2
  have he := minimumCandidate_eq_low hlow
  have hr : 0<orderOf u := orderOf_pos u
  have hd : ∀ c : Option ℕ, c.getD 0=orderOf u ↔ c=some (orderOf u) := by
    intro c
    cases c <;> simp [Ne.symm hr.ne']
  rw [orderResult,hd,he]
  simp only [List.mem_ofFn]

/-- Physical repeated law (before the deterministic minimum oracle). -/
theorem orderResult_mass_oai {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (K : ℕ) :
    outcomeMass (fun x => orderResult s n a m K x=orderOf u) (tensorState (rawState s n a m) K)=
      1-(1-(Nat.totient (orderOf u):ℝ)*(prescribedMass (orderOf u):ℝ))^K := by
  have he : (fun x : Fin K→Raw w s n => orderResult s n a m K x=orderOf u)=
      (fun x => ∃ i, trialResult s n a m (x i)=some (orderOf u)) := by
    funext x
    exact propext (orderResult_eq_order a m hm u ha x)
  rw [he,tensor_some_mass (rawState s n a m) K (fun x => trialResult s n a m x=some (orderOf u)) (raw_normalized s n a m),trialResult_mass hn hs a m hm u ha hdB]

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.OrderTrial.orderResult_mass_oai := @OAI.ExactQuantumFactoring.OrderTrial.orderResult_mass_oai
