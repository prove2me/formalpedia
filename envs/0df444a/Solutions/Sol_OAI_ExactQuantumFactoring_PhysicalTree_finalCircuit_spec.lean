-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:15:23.461643+00:00
-- url     : https://prove2.me/submissions/4b2d1527-37b2-4ce6-beb1-3f69874fa831

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
import Theorems.Thm_OAI_ExactQuantumFactoring_Completion_orderSuccess_lower
import Theorems.Thm_OAI_ExactQuantumFactoring_OrderTrial_orderResult_mass
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTree_accepted_iff_passed
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTree_quarterFlag_eval

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExactnessFurther
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma finiteInner_goodPart {ι : Type*} [Fintype ι] (good : ι → Prop) (v : ι → ℂ) :
    finiteInner v (goodPart good v) = (outcomeMass good v:ℂ) := by
  classical
  unfold finiteInner goodPart outcomeMass
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [Complex.normSq_eq_conj_mul_self]

lemma finiteInner_sub {ι : Type*} [Fintype ι] (u v w : ι → ℂ) :
    finiteInner u (fun x => v x-w x) = finiteInner u v-finiteInner u w := by
  simp only [finiteInner, mul_sub, Finset.sum_sub_distrib]

lemma finiteInner_mul {ι : Type*} [Fintype ι] (u v : ι → ℂ) (c : ℂ) :
    finiteInner u (fun x => c*v x) = c*finiteInner u v := by
  simp only [finiteInner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Literal one-reflection identity (6.9). The amplitude is not renormalized by fiat. -/
lemma one_reflection {ι : Type*} [Fintype ι] (good : ι → Prop) (ψ : ι → ℂ)
    (hψ : (∑ x, Complex.normSq (ψ x))=1) (hg : outcomeMass good ψ=1/4) :
    stateReflection ψ (fun x => ψ x-2*goodPart good ψ x) = fun x => 2*goodPart good ψ x := by
  have h := finiteInner_goodPart good ψ
  rw [hg] at h
  have hn := finiteInner_self ψ
  rw [hψ] at hn
  ext x
  simp only [stateReflection, finiteInner_sub, finiteInner_mul, h, hn]
  norm_num

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

lemma Circuit.apply_eq_matrix (c : Circuit) (ψ : State c.qubits) :
    c.apply ψ = (programMatrix c.instructions).mulVec ψ := by
  suffices ∀ (ops : List (Instruction c.qubits)) (ψ : State c.qubits),
      ops.foldl (fun v o => o.matrix.mulVec v) ψ = (programMatrix ops).mulVec ψ from
    this c.instructions ψ
  intro ops
  induction ops with
  | nil => intro ψ; simp [programMatrix]
  | cons o ops ih =>
    intro ψ
    rw [List.foldl_cons, ih]
    change _ = (ops.foldl (fun A (o : Instruction _) => o.matrix * A) (o.matrix * 1)).mulVec ψ
    rw [programMatrix_fold, Matrix.mul_one, Matrix.mulVec_mulVec]

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

lemma encodeState_outside {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ : α → ℂ) (x : Basis q) (hx : x ∉ Set.range e) :
    encodeState e ψ x = 0 := by
  classical
  rw [encodeState_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [ite_eq_right]
  intro h
  exact hx ⟨a,h.symm⟩

lemma encodeState_basis {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (e : α → Basis q) (a : α) : encodeState e (basisVector a) = basisVector (e a) := by
  classical
  simp [encodeState, basisVector, ite_smul]

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
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

lemma Register.replace_injective {p q : ℕ} (w : Register p q) (x : Basis q) :
    Function.Injective (w.replace x) := by
  intro u v h
  funext i
  have hh := congrFun h (w i)
  simpa only [Register.replace_inside] using hh

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

lemma packed_injective {n m r : ℕ} (y : Basis m) :
    Function.Injective (fun x : Basis n => packed r x y) := by
  intro x z h
  have hh := congrArg (fun t => t ∘ firstRegister n m r) h
  simpa only [packed_first] using hh

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

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordNetworks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

lemma setWidth_toNat_of_le {w t : ℕ} (h : w ≤ t) (x : BitVec w) :
    (x.setWidth t).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)

lemma wordConstant_eval {n w : ℕ} (v : BitVec w) (x : Basis n) :
    bitsValue ((wordConstant v).eval x) = v := by
  have he : (wordConstant (n := n) v).eval x = fun i => v.getLsbD i.val := by
    funext i
    simp [wordConstant]
  rw [he, bitsValue_bits]

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_Exactness
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Exactness
open scoped BigOperators

lemma completion_rounding (E : ℕ) {z A : ℚ} (hz : 0 ≤ z) (hA : 0 < A)
    (hzA : z ≤ A) :
    0 ≤ completionCoeff E z A ∧ completionCoeff E z A ≤ 1 ∧
      0 ≤ completionRemainder E z A ∧ completionRemainder E z A < A/2^E := by
  have hD : (0:ℚ) < 2^E := by positivity
  have hx : 0 ≤ (2:ℚ)^E*(z/A) := mul_nonneg hD.le (div_nonneg hz hA.le)
  have hf := Int.floor_le ((2:ℚ)^E*(z/A))
  have hu := Int.lt_floor_add_one ((2:ℚ)^E*(z/A))
  have hfn : (0:ℚ) ≤ (⌊(2:ℚ)^E*(z/A)⌋ : ℤ) :=
    Int.cast_nonneg (Int.floor_nonneg.mpr hx)
  have hc₀ : 0 ≤ completionCoeff E z A := div_nonneg hfn hD.le
  have hc₁ : completionCoeff E z A ≤ z/A := by
    unfold completionCoeff
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have herr : z/A-completionCoeff E z A < 1/(2:ℚ)^E := by
    apply (mul_lt_mul_iff_right₀ hD).mp
    unfold completionCoeff
    rw [mul_sub, mul_div_cancel₀ _ hD.ne', mul_div_cancel₀ _ hD.ne']
    linarith
  have he : completionRemainder E z A = (z/A-completionCoeff E z A)*A := by
    unfold completionRemainder
    rw [sub_mul, div_mul_cancel₀ _ hA.ne']
  refine ⟨hc₀, hc₁.trans ((div_le_one hA).mpr hzA), ?_, ?_⟩
  · rw [he]
    exact mul_nonneg (sub_nonneg.mpr hc₁) hA.le
  · rw [he]
    calc
      _ < (1/(2:ℚ)^E)*A := mul_lt_mul_of_pos_right herr hA
      _ = _ := by ring

/-- Both branch masses include the choice of branch and the guessing probability. -/
lemma completion_mass (W t : ℕ) (s z : ℚ) :
    (1-1/(2:ℚ)^t)*s * completionCoeff (W+t+2) z ((1-1/(2:ℚ)^t)*s) +
    (1/(2:ℚ)^t)*(1/(2:ℚ)^W)*
      (completionRemainder (W+t+2) z ((1-1/(2:ℚ)^t)*s)*(2:ℚ)^W/(1/(2:ℚ)^t)) = z := by
  unfold completionRemainder
  field_simp
  ring

lemma completion_retention_bounds (W t : ℕ) {s z : ℚ}
    (hs₀ : 0 < s) (hs₁ : s ≤ 1) (ht : 0 < t)
    (hz : 0 < z) (hzA : z ≤ (1-1/(2:ℚ)^t)*s) :
    let A := (1-1/(2:ℚ)^t)*s
    let C := completionCoeff (W+t+2) z A
    let R := completionRemainder (W+t+2) z A
    0 ≤ C ∧ C ≤ 1 ∧ 0 ≤ R*(2:ℚ)^W/(1/(2:ℚ)^t) ∧
      R*(2:ℚ)^W/(1/(2:ℚ)^t) < 1/4 := by
  let A := (1-1/(2:ℚ)^t)*s
  have hδ₀ : (0:ℚ) < 1/2^t := by positivity
  have hδ₁ : (1:ℚ)/2^t < 1 := by
    apply (div_lt_one (by positivity : (0:ℚ) < 2^t)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hA : 0 < A := mul_pos (sub_pos.mpr hδ₁) hs₀
  have hA₁ : A ≤ 1 := by
    calc
      _ ≤ 1*s := mul_le_mul_of_nonneg_right (by linarith : 1-1/(2:ℚ)^t ≤ 1) hs₀.le
      _ ≤ 1 := by simpa using hs₁
  have h := completion_rounding (W+t+2) hz.le hA hzA
  dsimp only
  refine ⟨h.1, h.2.1, div_nonneg (mul_nonneg h.2.2.1 (by positivity)) hδ₀.le, ?_⟩
  have hR : completionRemainder (W+t+2) z A < 1/(2:ℚ)^(W+t+2) :=
    h.2.2.2.trans_le (div_le_div_of_nonneg_right hA₁ (by positivity))
  calc
    _ < (1/(2:ℚ)^(W+t+2))*(2:ℚ)^W/(1/(2:ℚ)^t) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hR (by positivity)) hδ₀
    _ = 1/4 := by rw [pow_add, pow_add]; norm_num; field_simp

lemma quarter_retention_bounds (J : ℕ) {p : ℚ} (hp₀ : 1/2 < p) (hp₁ : p ≤ 1) :
    0 ≤ quarterCoeff J p ∧ quarterCoeff J p ≤ 1 ∧
      0 ≤ (2:ℚ)^(J+1)*quarterRemainder J p ∧
      (2:ℚ)^(J+1)*quarterRemainder J p < 1/4 := by
  have h := completion_rounding (J+2) (by norm_num : (0:ℚ) ≤ 1/2)
    (by linarith : 0 < p) hp₀.le
  have he : quarterRemainder J p = completionRemainder (J+2) (1/2) p/2 := by
    unfold quarterRemainder quarterCoeff completionRemainder
    ring
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [he]
    exact mul_nonneg (by positivity) (div_nonneg h.2.2.1 (by norm_num))
  · rw [he]
    have hR : completionRemainder (J+2) (1/2) p < 1/(2:ℚ)^(J+2) :=
      h.2.2.2.trans_le (div_le_div_of_nonneg_right hp₁ (by positivity))
    calc
      _ < (2:ℚ)^(J+1)*(1/(2:ℚ)^(J+2)/2) :=
        mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hR (by norm_num)) (by positivity)
      _ = 1/4 := by rw [pow_add, pow_add]; norm_num; field_simp

lemma quarter_mass (J : ℕ) (p : ℚ) :
    (1/2)*p*quarterCoeff J p +
      (1/2)*(1/(2:ℚ)^J)*((2:ℚ)^(J+1)*quarterRemainder J p)=1/4 := by
  unfold quarterRemainder
  rw [pow_succ]
  field_simp
  ring

/-- An explicit elementary discrete bound eliminates a real-calculus asymptotic. -/
lemma step_tenth_power_bound {n : ℕ} (hn : 128 ≤ n) : (n+1)^10 ≤ 2*n^10 := by
  have h₀ : 128*(n+1) ≤ 129*n := by omega
  have h₁ := Nat.pow_le_pow_left h₀ 10
  rw [mul_pow,mul_pow] at h₁
  have hc : 129^10 ≤ 2*128^10 := by norm_num
  have h₂ : 128^10*(n+1)^10 ≤ 128^10*(2*n^10) := by
    calc
      _ ≤ 129^10*n^10 := h₁
      _ ≤ (2*128^10)*n^10 := Nat.mul_le_mul_right _ hc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h₂ (by norm_num)

lemma tenth_power_exponential {n : ℕ} (hn : 128 ≤ n) : 2*n^10 < 2^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hs := step_tenth_power_bound hn
    calc
      _ ≤ 2*(2*n^10) := Nat.mul_le_mul_left 2 hs
      _ < 2*2^n := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; omega

lemma knownProbability_bounds {n : ℕ} (hn : 128 ≤ n) :
    1/2 < knownProbability n ∧ knownProbability n ≤ 1 := by
  have hD : (0:ℚ) < 2^n := by positivity
  have hD₁ : (1:ℚ) ≤ 2^n := one_le_pow₀ (by norm_num)
  have hδ : (1:ℚ)/2^n ≤ 1 := (div_le_one hD).mpr hD₁
  have hbin := one_add_mul_le_pow (R:=ℚ)
    (show -2 ≤ -(1/(2:ℚ)^n) by linarith) (n^10)
  have hexp : (2:ℚ)*(n:ℚ)^10 < 2^n := by exact_mod_cast tenth_power_exponential hn
  have hsmall : (n:ℚ)^10/(2:ℚ)^n < 1/2 := by
    apply (div_lt_iff₀ hD).mpr
    linarith
  unfold knownProbability
  constructor
  · simp only [Nat.cast_pow, ← sub_eq_add_neg, mul_neg, mul_one_div] at hbin
    linarith
  · calc
      _ ≤ (1:ℚ)^(n^10) := pow_le_pow_left₀ (by linarith : 0 ≤ 1-1/(2:ℚ)^n)
        (by linarith [le_of_lt (show (0:ℚ) < 1/(2:ℚ)^n by positivity)]) _
      _ = 1 := one_pow _

end ExactQuantumFactoring.Exactness



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
-- module Solutions.OAIQ222_QF.QuantumFactoring_InitialOrderState
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
open BooleanNetwork

lemma encodeState_comp {α : Type*} [Fintype α] {p q : ℕ}
    (e : α → Basis p) (f : Basis p → Basis q) (ψ : α → ℂ) :
    encodeState f (encodeState e ψ) = encodeState (f ∘ e) ψ := by
  classical
  change encodeState f (∑ a, ψ a • basisVector (e a)) = _
  rw [encodeState_sum]
  simp_rw [encodeState_smul,encodeState_basis]
  rfl

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_PreparedOracle
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork Exactness

lemma targetRegister_val (n m r : ℕ) (i : Fin m) :
    (targetRegister n m r i).val=n+i.val := rfl

lemma packed_targetRegister {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y ∘ targetRegister n m r=y := by
  funext i
  exact packed_target x y i

lemma packed_replace_target {n m r : ℕ} (x : Basis n) (y z : Basis m) :
    (targetRegister n m r).replace (packed r x y) z=packed r x z := by
  funext i
  by_cases hin : n ≤ i.val
  · by_cases hi : i.val<n+m
    · let j : Fin m := ⟨i.val-n,by omega⟩
      have he : targetRegister n m r j=i := Fin.ext (by rw [targetRegister_val]; dsimp [j]; omega)
      rw [←he,Register.replace_inside]
      exact (packed_target x z j).symm
    · have ho : ∀ j,targetRegister n m r j≠i := by
        intro j hh
        have he := congrArg Fin.val hh
        rw [targetRegister_val] at he
        have := j.isLt
        omega
      rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
      change packed r x y i=packed r x z i
      rw [packed_work _ _ _ (by omega),packed_work _ _ _ (by omega)]
  · have ho : ∀ j,targetRegister n m r j≠i := by
      intro j hh
      have he := congrArg Fin.val hh
      rw [targetRegister_val] at he
      omega
    rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
    simp only [packed,dite_eq_left (show i.val<n by omega)]

lemma targetProgram_basis {n m r : ℕ} (ops : List (Instruction m)) (x : Basis n) (y : Basis m) :
    (programMatrix (targetProgram n r ops)).mulVec (basisVector (packed r x y))=
      encodeState (fun z => packed r x z) ((programMatrix ops).mulVec (basisVector y)) := by
  rw [targetProgram,Register.placed_basis_state,packed_targetRegister]
  congr 1
  funext z
  exact packed_replace_target x y z

lemma preparedOracle_basis {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) (x : Basis n) :
    (programMatrix (preparedOracle c hr ops)).mulVec (basisVector (packed r x (fun _ => false)))=
      encodeState (fun z => packed r x z) ((programMatrix ops).mulVec (basisVector (c.eval x))) := by
  rw [preparedOracle,programMatrix_append,←Matrix.mulVec_mulVec,oracleOn_basis]
  simp only [Bool.false_xor]
  exact targetProgram_basis ops x _

lemma packed_pair_injective (n m r : ℕ) :
    Function.Injective (fun xy : Basis n×Basis m => packed r xy.1 xy.2) := by
  intro x y h
  apply Prod.ext
  · have he := congrArg (fun a => a ∘ firstRegister n m r) h
    simpa only [packed_first] using he
  · have he := congrArg (fun a => a ∘ targetRegister n m r) h
    simpa only [packed_targetRegister] using he

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AdaptivePrepared
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open BooleanNetwork

/-- A coherent fresh launch on an encoded old history. The local law refers
only to the actually computed Boolean initializer, never to a selected outcome. -/
lemma preparedOracle_encode {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (c : BooleanNetwork p q) (hc : c.net.count ≤ r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=encodeState f (F a)) :
    (programMatrix (preparedOracle c hc ops)).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.2)) (RecordedHistory.appendState ψ F) := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,preparedOracle_basis,hlocal,encodeState_comp]
  unfold encodeState RecordedHistory.appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_smul]
  rfl

lemma appendPrepared_state {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (A : List (Instruction p)) (v : Basis p)
    (hA : (programMatrix A).mulVec (basisVector v)=encodeState e ψ)
    (c : BooleanNetwork p q) (hc : c.net.count ≤ r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=encodeState f (F a)) :
    (programMatrix (appendPrepared A c hc ops)).mulVec (basisVector (packed r v (fun _=>false)))=
      encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.2)) (RecordedHistory.appendState ψ F) := by
  rw [appendPrepared,programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hA,encodeState_comp]
  exact preparedOracle_encode e f ψ F c hc ops hlocal

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ArithmeticBounds
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

/-- The telescoping estimate for any distinct integers at least two. -/
theorem prod_le_card_mul_pred_prod (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (∏ p ∈ s, p) ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
    have ha2 : 2 ≤ a := hs a (Finset.mem_insert_self _ _)
    have hs2 : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hc : s.card + 2 ≤ a := by
      have hass : s ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨hs2 p hp, hmax p hp⟩
      have := Finset.card_le_card hass
      rw [Nat.card_Ico] at this
      omega
    have hstep : a * (s.card + 1) ≤ (s.card + 2) * (a - 1) := by
      have : a - 1 + 1 = a := by omega
      nlinarith
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      a * ∏ p ∈ s, p ≤ a * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
        Nat.mul_le_mul_left _ (ih hs2)
      _ ≤ (s.card + 1 + 1) * (a - 1) * ∏ p ∈ s, (p - 1) := by
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (∏ p ∈ s, (p - 1)) hstep
      _ = (s.card + 1 + 1) * ((a - 1) * ∏ p ∈ s, (p - 1)) := by ring

/-- The number of distinct prime factors is less than a strict binary cutoff. -/
theorem primeFactors_card_lt {d n : ℕ} (hd : 0 < d) (hb : d < 2 ^ n) :
    d.primeFactors.card < n := by
  have hp : 2 ^ d.primeFactors.card ≤ ∏ p ∈ d.primeFactors, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod'
      (fun prime hprime => (Nat.prime_of_mem_primeFactors hprime).two_le)
  have hp' : (∏ p ∈ d.primeFactors, p) ≤ d :=
    Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hp.trans_lt (hp'.trans_lt hb))

/-- Integer form of (5.2), retaining the original global binary cutoff. -/
theorem le_succ_mul_totient {d n : ℕ} (hd : 0 < d) (hb : d < 2 ^ n) :
    d ≤ (n + 1) * Nat.totient d := by
  have hp := prod_le_card_mul_pred_prod d.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hprodpos : 0 < ∏ p ∈ d.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hx := Nat.mul_le_mul_left (Nat.totient d) hp
  rw [Nat.totient_mul_prod_primeFactors] at hx
  have hbase : d ≤ (d.primeFactors.card + 1) * Nat.totient d := by
    apply Nat.le_of_mul_le_mul_right (c := ∏ p ∈ d.primeFactors, (p - 1)) _ hprodpos
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hx
  exact hbase.trans (Nat.mul_le_mul_right _ (by have := primeFactors_card_lt hd hb; omega))

/-- Real ratio version, ready for the exact transition-probability bound. -/
theorem totient_ratio_lower {d n : ℕ} (hd : 0 < d) (hb : d < 2 ^ n) :
    1 / ((n : ℝ) + 1) ≤ (Nat.totient d : ℝ) / d := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [div_le_div_iff₀ hn hd']
  norm_num only [one_mul]
  exact_mod_cast (le_succ_mul_totient hd hb).trans_eq (Nat.mul_comm _ _)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ArithmeticPredicates
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide
open AIGCompiler BooleanNetwork

lemma ult_correct (w : ℕ) (a b : Basis w) :
    (ult w).eval (Fin.append a b) 0 =
      decide ((bitsValue a).toNat < (bitsValue b).toNat) := by
  rw [ult,compile_correct]
  have h := BVPred.mkUlt_denote_eq (inputs (w+w)).1
    (leftWord (Fin.append a b)) (rightWord (Fin.append a b))
    (binaryInputs w) (Fin.append a b) (binaryInputs_left w _) (binaryInputs_right w _)
  simpa only [leftWord_append,rightWord_append,BitVec.ult] using h

lemma wordLt_eval {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (wordLt a b).eval x 0 = decide ((bitsValue (a.eval x)).toNat < (bitsValue (b.eval x)).toNat) := by
  rw [wordLt,eval_comp,eval_pair,ult_correct]

lemma wordEq_eval (w : ℕ) (a b : Basis w) :
    (wordEq w).eval (Fin.append a b) 0 = decide (bitsValue a = bitsValue b) := by
  have he : (select (Fin.addCases (Fin.natAdd w) (Fin.castAdd w))).eval (Fin.append a b) =
      Fin.append b a := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [eval_select,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right]
  rw [wordEq,eval_bnot,eval_bor,eval_comp,he,ult_correct,ult_correct]
  have hh : bitsValue a = bitsValue b ↔ (bitsValue a).toNat=(bitsValue b).toNat := by
    constructor
    · exact congrArg BitVec.toNat
    · exact BitVec.eq_of_toNat_eq
  simp only [hh]
  cases h₁ : decide ((bitsValue a).toNat < (bitsValue b).toNat) <;>
    cases h₂ : decide ((bitsValue b).toNat < (bitsValue a).toNat) <;>
    simp_all <;> omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AuxiliaryTree
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Occurrence-preserving bounds for the canonical p−1 auxiliary tree in
Section5. Equal labels under different parents remain separate list entries. -/
namespace ExactQuantumFactoring.AuxiliaryTree
open scoped BigOperators

lemma pow_length_le_prod (xs : List ℕ) (hxs : ∀ x ∈ xs, 2≤x) : 2^xs.length≤xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have hi := ih (fun y hy => hxs y (by simp [hy]))
    simp only [List.length_cons,List.prod_cons,pow_succ]
    exact (Nat.mul_le_mul hi hx).trans_eq (Nat.mul_comm _ _)

lemma splitWeight_bound {M n : ℕ} (hM : 0<M) (hbound : M<2^n) : splitWeight M<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  have hh := pow_length_le_prod M.primeFactorsList
    (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
  rw [Nat.prod_primeFactorsList hM.ne'] at hh
  exact hh.trans_lt hbound

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanFold
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_vector _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

lemma all_eval {n : ℕ} (cs : List (BooleanNetwork n 1)) (x : Fin n → Bool) :
    (all cs).eval x 0=true ↔ ∀ c ∈ cs, c.eval x 0=true := by
  induction cs with
  | nil => simp [all]
  | cons c cs ih => simp [all,ih]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordBlocks
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
open scoped BigOperators

lemma wordBlocks_eval {n s w : ℕ} (f : Fin s → BooleanNetwork n w) (x : Basis n) (i : Fin s) :
    block ((wordBlocks f).eval x) i=(f i).eval x := by
  funext j
  simp only [block,wordBlocks,eval_vector,eval_rewire,Function.comp_apply,Equiv.symm_apply_apply]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedStack
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma block_stackEncoding (s w : ℕ) (xs : List (Basis w)) (i : Fin s) :
    block (stackEncoding s w xs) i = xs[i.val]?.getD (fun _ => false) := by
  funext j
  simp [block,stackEncoding]

lemma stackPush_value {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w))
    (x : Basis k) (i : Fin s) :
    block ((stackPush a v).eval x) i =
      if _h : i.val=0 then a.eval x else block (v.eval x) ⟨i.val-1,by omega⟩ := by
  rw [stackPush,wordBlocks_eval]
  split_ifs <;> rfl

lemma block_ext {s w : ℕ} {x y : Basis (s*w)}
    (h : ∀ i : Fin s, block x i=block y i) : x=y := by
  funext j
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective j
  exact congrFun (h i) k

lemma stackPush_encoding {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w))
    (x : Basis k) (xs : List (Basis w)) (hv : v.eval x=stackEncoding s w xs) :
    (stackPush a v).eval x=stackEncoding s w (a.eval x::xs) := by
  apply block_ext
  intro i
  rw [stackPush_value,block_stackEncoding]
  split_ifs with hi
  · simp [hi]
  · rw [hv,block_stackEncoding]
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
    simp [hj]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LevelIndependence
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
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

/-- Counting the equality of two independent levels by fibers, with no
assumption about an approximately uniform distribution. -/
theorem equalLevel_card {A B T : Type*} [Fintype A] [Fintype B]
    (f : A → T) (g : B → T) [DecidableEq T] :
    Fintype.card {x : A × B // f x.1 = g x.2} = ∑ b : B, Fintype.card {a : A // f a = g b} := by
  classical
  rw [Fintype.card_congr (equalLevelEquiv f g), Fintype.card_sigma]

theorem twice_equalLevel_card_le {A B T : Type*} [Fintype A] [Fintype B]
    (f : A → T) (g : B → T) [DecidableEq T]
    (hf : ∀ t, 2 * Fintype.card {a : A // f a = t} ≤ Fintype.card A) :
    2 * Fintype.card {x : A × B // f x.1 = g x.2} ≤ Fintype.card A * Fintype.card B := by
  classical
  rw [equalLevel_card, Finset.mul_sum]
  calc
    _ ≤ ∑ _ : B, Fintype.card A := Finset.sum_le_sum (fun b _ => hf (g b))
    _ = _ := by simp [mul_comm]

/-- Exact product formula used in the source's retrospective F computation. -/
theorem allEqualLevel_card {ι T : Type*} {G : ι → Type*} [Fintype ι] [Fintype T]
    [∀ i, Fintype (G i)] [DecidableEq T] [DecidableEq ι] (i₀ : ι) (f : ∀ i, G i → T) :
    Fintype.card {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} =
      ∑ t : T, ∏ i : ι, Fintype.card {x : G i // f i x = t} := by
  classical
  rw [Fintype.card_congr (allEqualLevelEquiv i₀ f), Fintype.card_sigma]
  congr 1
  funext t
  exact Fintype.card_pi

/-- Two distinct independent components suffice for the exact half bound. -/
theorem twice_allEqualLevel_card_le {ι T : Type*} {G : ι → Type*}
    [Fintype ι] [∀ i, Fintype (G i)] [DecidableEq T] [DecidableEq ι]
    (i₀ i₁ : ι) (hi : i₁ ≠ i₀) (f : ∀ i, G i → T)
    (hf : ∀ t, 2 * Fintype.card {a : G i₀ // f i₀ a = t} ≤ Fintype.card (G i₀)) :
    2 * Fintype.card {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} ≤
      Fintype.card (∀ i, G i) := by
  classical
  let R := ∀ j : {j : ι // j ≠ i₀}, G j.val
  let g : R → T := fun x => f i₁ (x ⟨i₁,hi⟩)
  let emb : {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} →
      {x : G i₀ × R // f i₀ x.1 = g x.2} :=
    fun x => ⟨(Equiv.piSplitAt i₀ G) x.val, (x.property i₁).symm⟩
  have hinj : Function.Injective emb := by
    intro x y h
    apply Subtype.ext
    apply (Equiv.piSplitAt i₀ G).injective
    exact congrArg Subtype.val h
  have hc := Fintype.card_le_of_injective emb hinj
  calc
    _ ≤ 2 * Fintype.card {x : G i₀ × R // f i₀ x.1 = g x.2} :=
      Nat.mul_le_mul_left 2 hc
    _ ≤ Fintype.card (G i₀) * Fintype.card R := twice_equalLevel_card_le _ _ hf
    _ = Fintype.card (∀ i, G i) := by
      rw [← Fintype.card_prod]
      exact (Fintype.card_congr (Equiv.piSplitAt i₀ G)).symm

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Divisibility cannot increase the 2-adic valuation. -/
theorem level_le_of_dvd {d r : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) :
    padicValNat 2 d ≤ padicValNat 2 r := by
  rcases hdr with ⟨k, rfl⟩
  rw [padicValNat.mul (left_ne_zero_of_mul hr) (right_ne_zero_of_mul hr)]
  omega

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LevelCounts
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


open scoped BigOperators
namespace ExactQuantumFactoring

/-- Dividing a positive multiple by a power of two preserves exactly the
order divisors with enough 2-adic slack. -/
theorem dvd_div_pow_two_iff {d r k : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) (hk : 2 ^ k ∣ r) :
    d ∣ r / 2 ^ k ↔ padicValNat 2 d + k ≤ padicValNat 2 r := by
  have hkle : k ≤ padicValNat 2 r := (padicValNat_dvd_iff_le hr).mp hk
  constructor
  · intro h
    have hquot : r / 2 ^ k ≠ 0 := by
      have : 2 ^ k ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hk
      have : 0 < r / 2 ^ k := Nat.div_pos this (by positivity)
      omega
    have hh := level_le_of_dvd hquot h
    rw [padicValNat.div_pow hk] at hh
    omega
  · intro h
    rcases hdr with ⟨a, rfl⟩
    have hd : d ≠ 0 := left_ne_zero_of_mul hr
    have ha : a ≠ 0 := right_ne_zero_of_mul hr
    rw [padicValNat.mul hd ha] at h
    have hp : 2 ^ k ∣ a := (padicValNat_dvd_iff_le ha).mpr (by omega)
    apply (Nat.dvd_div_iff_mul_dvd hk).mpr
    simpa only [Nat.mul_comm (2 ^ k) d] using Nat.mul_dvd_mul_left d hp

/-- For a divisor, an exact valuation cutoff is a single ordinary divisibility
test; hence its size is a cyclic-group root count, not residue enumeration. -/
theorem level_le_iff_dvd_cutoff {d r t : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) :
    padicValNat 2 d ≤ t ↔ d ∣ r / 2 ^ (padicValNat 2 r - t) := by
  have hle := level_le_of_dvd hr hdr
  have hp : 2 ^ (padicValNat 2 r - t) ∣ r :=
    (padicValNat_dvd_iff_le hr).mpr (Nat.sub_le _ _)
  rw [dvd_div_pow_two_iff hr hdr hp]
  omega

/-- The cumulative law of levels in every finite cyclic group. -/
theorem cumulativeLevelCount_eq (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    cumulativeLevelCount G t = Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - t) := by
  classical
  let r := Fintype.card G
  have hr : r ≠ 0 := Fintype.card_ne_zero
  let e := r / 2 ^ (padicValNat 2 r - t)
  have hediv : e ∣ r := Nat.div_dvd_of_dvd
    ((padicValNat_dvd_iff_le hr).mpr (Nat.sub_le _ _))
  have heq : ∀ x : G, padicValNat 2 (orderOf x) ≤ t ↔ x ∈ (powMonoidHom e : G →* G).ker := by
    intro x
    rw [level_le_iff_dvd_cutoff hr (show orderOf x ∣ r from orderOf_dvd_card)]
    exact orderOf_dvd_iff_pow_eq_one
  let E : {x : G // padicValNat 2 (orderOf x) ≤ t} ≃ (powMonoidHom e : G →* G).ker :=
    Equiv.subtypeEquivRight heq
  change Fintype.card _ = e
  rw [Fintype.card_congr E, ← Nat.card_eq_fintype_card, IsCyclic.card_powMonoidHom_ker]
  rw [Nat.card_eq_fintype_card]
  exact Nat.gcd_eq_right hediv

/-- Fibers are obtained by differencing two consecutive cumulative counts. -/
theorem levelCount_eq_cumulative (G : Type*) [Group G] [Fintype G] (t : ℕ) :
    levelCount G t = if t = 0 then cumulativeLevelCount G 0
      else cumulativeLevelCount G t - cumulativeLevelCount G (t - 1) := by
  classical
  by_cases ht : t = 0
  · subst t
    simp [levelCount, cumulativeLevelCount]
  · have hpartition : (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t)) =
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) = t)) ∪
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t - 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdis : Disjoint (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) = t))
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t - 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      omega
    simp only [levelCount, cumulativeLevelCount, ht, ↓reduceIte, Fintype.card_subtype]
    rw [hpartition, Finset.card_union_of_disjoint hdis]
    omega

/-- Exact level counts use only cardinal arithmetic, powers of two and division. -/
theorem levelCount_cyclic (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    levelCount G t = if t = 0 then
      Fintype.card G / 2 ^ padicValNat 2 (Fintype.card G)
    else Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - t) -
      Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - (t - 1)) := by
  rw [levelCount_eq_cumulative]
  simp only [cumulativeLevelCount_eq, Nat.sub_zero]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LevelBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma div_lower_power_two {r v t : ℕ} (hdiv : 2^v ∣ r) (ht : t ≤ v) :
    r / 2^(v-t) = 2^t * (r / 2^v) := by
  have hpow : 2^(v-t) * 2^t = 2^v := by rw [← pow_add, Nat.sub_add_cancel ht]
  calc
    r / 2^(v-t) = (2^(v-t) * (2^t * (r / 2^v))) / 2^(v-t) := by
      rw [← mul_assoc, hpow, Nat.mul_div_cancel' hdiv]
    _ = 2^t * (r / 2^v) := Nat.mul_div_right _ (by positivity)

/-- The traditional cyclic-group level law u, u, 2u, 4u, ... . -/
theorem levelCount_closed (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    levelCount G t = if t = 0 then Fintype.card G / 2^padicValNat 2 (Fintype.card G)
      else if t ≤ padicValNat 2 (Fintype.card G) then
        2^(t-1) * (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) else 0 := by
  have hr : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hd : 2^padicValNat 2 (Fintype.card G) ∣ Fintype.card G :=
    (padicValNat_dvd_iff_le hr).mpr le_rfl
  rw [levelCount_cyclic]
  by_cases ht : t = 0
  · simp [ht]
  · simp only [ht, ↓reduceIte]
    by_cases htv : t ≤ padicValNat 2 (Fintype.card G)
    · rw [ite_eq_left htv, div_lower_power_two hd htv,
        div_lower_power_two hd (by omega : t-1 ≤ padicValNat 2 (Fintype.card G))]
      have he : t = (t-1)+1 := by omega
      nth_rw 1 [he]
      rw [pow_succ]
      have heq : 2 ^ (t-1) * 2 * (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) =
          2 * (2^(t-1) * (Fintype.card G / 2^padicValNat 2 (Fintype.card G))) := by ring
      rw [heq]
      omega
    · have hv : padicValNat 2 (Fintype.card G) ≤ t-1 := by omega
      simp [htv, Nat.sub_eq_zero_of_le hv, Nat.sub_eq_zero_of_le (by omega :
        padicValNat 2 (Fintype.card G) ≤ t)]

/-- No particular level has more than half the elements of a cyclic group of
even order, including the lowest level and the unique top level. -/
theorem two_mul_levelCount_le (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G]
    (heven : 2 ∣ Fintype.card G) (t : ℕ) : 2 * levelCount G t ≤ Fintype.card G := by
  have hr : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hv : 1 ≤ padicValNat 2 (Fintype.card G) := by
    apply (padicValNat_dvd_iff_le hr).mp
    simpa using heven
  have hd : 2^padicValNat 2 (Fintype.card G) ∣ Fintype.card G :=
    (padicValNat_dvd_iff_le hr).mpr le_rfl
  have hrw : 2^padicValNat 2 (Fintype.card G) *
      (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) = Fintype.card G :=
    Nat.mul_div_cancel' hd
  rw [levelCount_closed]
  by_cases ht : t = 0
  · rw [ite_eq_left ht]
    calc
      _ ≤ 2^padicValNat 2 (Fintype.card G) *
          (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) :=
        Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hv)
      _ = _ := hrw
  · rw [ite_eq_right ht]
    by_cases htv : t ≤ padicValNat 2 (Fintype.card G)
    · rw [ite_eq_left htv, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ t)]
      calc
        _ ≤ 2^padicValNat 2 (Fintype.card G) *
            (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 0 < 2) htv)
        _ = _ := hrw
    · simp [htv]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimePowerLevels
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
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Exact prime-power level counts from the already fully proved cyclicity of
odd prime-power unit groups in Mathlib. -/
theorem primePowerLevelCard_eq {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 0 < e) (t : ℕ) :
    primePowerLevelCard p e t = closedLevelCount (primePowerUnitCount p e) t := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsCyclic (ZMod (p^e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have hc : Fintype.card (ZMod (p^e))ˣ = primePowerUnitCount p e := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp he]
    simp [primePowerUnitCount, mul_comm]
  classical
  change Nat.card {x : (ZMod (p^e))ˣ // padicValNat 2 (orderOf x) = t} = _
  rw [Nat.card_eq_fintype_card]
  change levelCount (ZMod (p^e))ˣ t = _
  rw [levelCount_closed, hc]
  rfl

theorem primePowerLevelCard_half {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 0 < e) (t : ℕ) :
    2 * primePowerLevelCard p e t ≤ primePowerUnitCount p e := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsCyclic (ZMod (p^e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have hc : Fintype.card (ZMod (p^e))ˣ = primePowerUnitCount p e := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp he]
    simp [primePowerUnitCount, mul_comm]
  have hpe : 2 < p^e := by
    have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    exact hp3.trans_le (Nat.le_pow he)
  have heven : 2 ∣ Fintype.card (ZMod (p^e))ˣ := by
    rw [ZMod.card_units_eq_totient]
    exact even_iff_two_dvd.mp (Nat.totient_even hpe)
  classical
  have hh := two_mul_levelCount_le (ZMod (p^e))ˣ heven t
  rw [hc] at hh
  simpa only [primePowerLevelCard, Nat.card_eq_fintype_card, levelCount] using hh

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CRTLevels
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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

lemma componentLevel_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (t : Fin (n+1)) :
    Fintype.card {a : ComponentUnits m p // componentLevel hm hmn p a = t} =
      primePowerLevelCard p.val (m.factorization p.val) t.val := by
  classical
  rw [primePowerLevelCard, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun a => Fin.ext_iff)

lemma equal_component_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) :
    Fintype.card {a : ∀ p : Component m, ComponentUnits m p //
      ∀ p, componentLevel hm hmn p (a p) = componentLevel hm hmn p₀ (a p₀)} =
    ∑ t : Fin (n+1), ∏ p : Component m,
      closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val := by
  classical
  rw [allEqualLevel_card p₀]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.prod_congr rfl
  intro p hp
  rw [componentLevel_card]
  have pp := Nat.mem_primeFactors.mp p.property
  exact primePowerLevelCard_eq pp.1 (by
    intro h
    apply (Nat.not_even_iff_odd.mpr hodd)
    exact even_iff_two_dvd.mpr (h ▸ pp.2.1))
    (pp.1.factorization_pos_of_dvd hm pp.2.1) _

/-- The exact source F is the cardinality of the actual CRT favorable event. -/
theorem favorableCount_eq_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) :
    favorableCount m n = Nat.card {a : (ZMod m)ˣ // FavorableUnit hm hmn p₀ a} := by
  classical
  let : NeZero m := ⟨hm⟩
  rw [Nat.card_eq_fintype_card]
  unfold FavorableUnit
  rw [Fintype.card_subtype_compl, ZMod.card_units_eq_totient]
  unfold favorableCount
  congr 1
  rw [← equal_component_card hm hmn hodd p₀]
  exact (Fintype.card_congr ((unitCRT m hm).toEquiv.subtypeEquiv (fun _ => Iff.rfl))).symm

/-- At least half the units are favorable whenever there are two distinct
odd prime-power components, exactly as in Section 5. -/
theorem totient_le_twice_favorableCount {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁ ≠ p₀) :
    m.totient ≤ 2 * favorableCount m n := by
  classical
  let : NeZero m := ⟨hm⟩
  have hhalf := twice_allEqualLevel_card_le p₀ p₁ hne (componentLevel hm hmn) (by
    intro t
    rw [componentLevel_card]
    have pp := Nat.mem_primeFactors.mp p₀.property
    have hpp := primePowerLevelCard_half pp.1 (by
      intro h
      apply (Nat.not_even_iff_odd.mpr hodd)
      exact even_iff_two_dvd.mpr (h ▸ pp.2.1))
      (pp.1.factorization_pos_of_dvd hm pp.2.1) t.val
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow pp.1
      (pp.1.factorization_pos_of_dvd hm pp.2.1)]
    simpa only [primePowerUnitCount, mul_comm] using hpp)
  rw [equal_component_card hm hmn hodd p₀] at hhalf
  have hc : Fintype.card (∀ p : Component m, ComponentUnits m p) = m.totient := by
    rw [← Fintype.card_congr (unitCRT m hm).toEquiv, ZMod.card_units_eq_totient]
  rw [hc] at hhalf
  unfold favorableCount
  omega

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProductStates
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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma productState_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (ψ : ∀ i, α i → ℂ)
    (hψ : ∀ i, ∑ x, Complex.normSq (ψ i x)=1) :
    ∑ x, Complex.normSq (productState ψ x)=1 := by
  simp only [productState,map_prod]
  rw [←Fintype.prod_sum (fun i a => Complex.normSq (ψ i a))]
  simp only [hψ,Finset.prod_const_one]

lemma productState_all_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (ψ : ∀ i, α i → ℂ)
    (P : ∀ i, α i → Prop) :
    outcomeMass (fun x => ∀ i, P i (x i)) (productState ψ)=
      ∏ i, outcomeMass (P i) (ψ i) := by
  classical
  unfold outcomeMass productState
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i, P i (x i)
  · simp [hx,map_prod]
  · rw [ite_eq_right hx]
    obtain ⟨i,hi⟩ := not_forall.mp hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

lemma productState_constant_mass {α : Type*} [Fintype α] {K : ℕ}
    (ψ : Fin K → α → ℂ) (P : Fin K → α → Prop) (z : ℝ)
    (hz : ∀ i, outcomeMass (P i) (ψ i)=z) :
    outcomeMass (fun x => ∀ i, P i (x i)) (productState ψ)=z^K := by
  rw [productState_all_mass]
  simp only [hz,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

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

lemma mass_bounds {α : Type*} [Fintype α] (ψ : α→ℂ) (P : α→Prop)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) : 0≤outcomeMass P ψ ∧ outcomeMass P ψ≤1 := by
  classical
  unfold outcomeMass
  constructor
  · apply Finset.sum_nonneg
    intro x _
    have hh := Complex.normSq_nonneg (ψ x)
    split_ifs <;> linarith
  · rw [← hψ]
    apply Finset.sum_le_sum
    intro x _
    have hh := Complex.normSq_nonneg (ψ x)
    split_ifs <;> linarith

/-- Deliberately uses the original cutoff128 and repetition exponent5. -/
lemma repetition_failure_bound {n : ℕ} (hn : 128≤n) {x : ℝ}
    (hx₀ : 1/(2048*(n+1):ℝ)≤x) (hx₁ : x≤1) :
    (1-x)^(n^5)≤1/(2:ℝ)^(2*n) := by
  have hnR : (128:ℝ)≤n := by exact_mod_cast hn
  have hxpos : 0<x := lt_of_lt_of_le (by positivity) hx₀
  have hmul : ((n:ℝ)^5)*x ≥ 2*n := by
    have hden : (0:ℝ)<2048*(n+1) := by positivity
    have hlow := (div_le_iff₀ hden).mp hx₀
    have hnpos : (0:ℝ)<n := by positivity
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤128) hnR 3
    norm_num at hh
    have hc : (8192:ℝ)≤(n:ℝ)^3 := by linarith
    have hp : 8192*(n:ℝ)^2≤(n:ℝ)^5 := by
      simpa only [← pow_add] using mul_le_mul_of_nonneg_right hc (sq_nonneg (n:ℝ))
    have hfirst : 2*n*(2048*(n+1))≤(n:ℝ)^5 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hlow (by positivity : (0:ℝ)≤(n:ℝ)^5)
    nlinarith
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hx₁) (Real.one_sub_le_exp_neg x) (n^5)
  calc
    (1-x)^(n^5) ≤ Real.exp (-x)^(n^5) := hpow
    _ = Real.exp (-(2*n:ℝ)) * Real.exp (2*n-(n:ℝ)^5*x) := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (-(2*n:ℝ)) := by
      have he : Real.exp (2*n-(n:ℝ)^5*x)≤1 := Real.exp_le_one_iff.mpr (by linarith)
      exact (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le).trans_eq (mul_one _)
    _ = 1/(Real.exp 1)^(2*n) := by
      rw [Real.exp_neg,← Real.exp_nat_mul]
      simp
    _ ≤ 1/(2:ℝ)^(2*n) := by
      apply one_div_le_one_div_of_le (by positivity)
      apply pow_le_pow_left₀ (by norm_num)
      have he := Real.exp_one_gt_d9
      linarith

lemma repeated_success_lower {n : ℕ} (hn : 128≤n) {x : ℝ}
    (hx₀ : 1/(2048*(n+1):ℝ)≤x) (hx₁ : x≤1) :
    1-1/(2:ℝ)^(2*n) ≤ 1-(1-x)^(n^5) := by
  have hh := repetition_failure_bound hn hx₀ hx₁
  linarith

end ExactQuantumFactoring.RepeatedTrials


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_StaticPredicates
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

lemma equalOn_value {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (equalOn a b).eval x 0=true ↔ (bitsValue (a.eval x)).toNat=(bitsValue (b.eval x)).toNat := by
  rw [equalOn,eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  exact ⟨congrArg BitVec.toNat,BitVec.eq_of_toNat_eq⟩

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

lemma correctEncoding_unique {N n : ℕ} {xs ys : List ℕ}
    (hx : CorrectEncoding N n xs) (hy : CorrectEncoding N n ys) : xs=ys := by
  obtain ⟨ps,hp,hs,hprod,_,rfl⟩ := hx
  obtain ⟨qs,hq,ht,hqprod,_,rfl⟩ := hy
  have hperm := (Nat.primeFactorsList_unique hprod hp).trans
    (Nat.primeFactorsList_unique hqprod hq).symm
  have he : ps=qs := hperm.eq_of_pairwise' hs ht
  rw [he]

/-- The valid sorted padded encoding exists and is unique, with every entry in
its n-bit range; the mathematical factor list here is used for analysis only. -/
theorem correctEncoding_exists {N n : ℕ} (hN : 2≤N) (hb : N<2^n) :
    ∃ xs : List ℕ, CorrectEncoding N n xs ∧ xs.length=n ∧ ∀ a ∈ xs, a<2^n := by
  have hn : N.primeFactorsList.length<n := AuxiliaryTree.splitWeight_bound (by omega) hb
  let xs := N.primeFactorsList++List.replicate (n-N.primeFactorsList.length) 0
  refine ⟨xs,⟨N.primeFactorsList,(fun p hp => Nat.prime_of_mem_primeFactorsList hp),
    (Nat.primeFactorsList_sorted N).pairwise,Nat.prod_primeFactorsList (by omega),hn.le,rfl⟩,?_,?_⟩
  · simp only [xs,List.length_append,List.length_replicate]
    omega
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (Nat.le_of_mem_primeFactorsList ha).trans_lt hb
    · have he := (List.mem_replicate.mp ha).2
      rw [he]
      positivity

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

lemma guessWords_injective (n : ℕ) : Function.Injective (guessWords n) := by
  intro x y h
  have he : (fun i : Fin n => (bitsValue (block x i)).toNat)=
      (fun i : Fin n => (bitsValue (block y i)).toNat) := List.ofFn_injective h
  funext a
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective a
  have hi := congrFun he i
  have hb : bitsValue (block x i) = bitsValue (block y i) := BitVec.eq_of_toNat_eq hi
  have hj := congrArg (fun z : BitVec n => z.getLsbD j.val) hb
  simpa only [bitsValue_bit,block] using hj

lemma guessWords_surjective_bounded {n : ℕ} (xs : List ℕ) (hl : xs.length=n)
    (hb : ∀ a∈xs, a<2^n) : ∃ x : Basis (n*n), guessWords n x=xs := by
  let f : Fin n→ℕ := fun i => xs[i.val]'(by omega)
  let x : Basis (n*n) := fun a =>
    (BitVec.ofNat n (f (finProdFinEquiv.symm a).1)).getLsbD (finProdFinEquiv.symm a).2.val
  refine ⟨x,?_⟩
  have he : ∀ i : Fin n, (bitsValue (block x i)).toNat=f i := by
    intro i
    have hf : f i<2^n := hb _ (List.getElem_mem (by omega))
    have hg : block x i=fun j => (BitVec.ofNat n (f i)).getLsbD j.val := by
      funext j
      simp only [block,x,Equiv.symm_apply_apply]
    rw [hg,bitsValue_bits,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hf]
  simp only [guessWords,he]
  have h := List.ofFn_get xs
  subst n
  exact h

/-- Existence/uniqueness is a mathematical fact about the required output,
not a factoring oracle used in the circuit. -/
theorem unique_good_guess {N n : ℕ} (hN : 2≤N) (hb : N<2^n) :
    ∃! x : Basis (n*n), CorrectEncoding N n (guessWords n x) := by
  obtain ⟨xs,hx,hl,hb'⟩ := correctEncoding_exists hN hb
  obtain ⟨x,rfl⟩ := guessWords_surjective_bounded xs hl hb'
  refine ⟨x,hx,?_⟩
  intro y hy
  apply guessWords_injective n
  exact correctEncoding_unique hy hx

lemma fairState_mass (b : ℕ) (x : Basis b) :
    Complex.normSq (fairState b x)=(2:ℝ)⁻¹^b := by
  simp only [fairState,map_pow,Complex.normSq_inv,Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)]

lemma fairState_normalized (b : ℕ) : ∑ x, Complex.normSq (fairState b x)=1 := by
  simp only [fairState_mass,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

/-- The actual fair-bit guess contributes exactly 2^(-n²), not an
input-dependent success probability. -/
theorem fair_guess_mass {N n : ℕ} (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x => CorrectEncoding N n (guessWords n x)) (fairState (n*n))=
      (2:ℝ)⁻¹^(n*n) := by
  classical
  obtain ⟨x,hx,hu⟩ := unique_good_guess hN hb
  have he : ∀ y : Basis (n*n), CorrectEncoding N n (guessWords n y) ↔ y=x := by
    intro y
    exact ⟨fun hy => hu y hy,fun h => h ▸ hx⟩
  simp only [outcomeMass,he,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,fairState_mass]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FairOracle
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Actual fair-bit initialization followed by clean reversible Boolean
computation.  All random bits remain in the returned physical state. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

lemma outcomeMass_encode {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (he : Function.Injective e) (ψ : α → ℂ)
    (P : Basis q → Prop) :
    outcomeMass P (encodeState e ψ)=outcomeMass (P ∘ e) ψ := by
  classical
  unfold outcomeMass
  have hz : ∀ x ∈ (Finset.univ : Finset (Basis q)),
      x ∉ Finset.univ.image e →
      (if P x then Complex.normSq (encodeState e ψ x) else 0)=0 := by
    intro x _ hx
    have ho : x ∉ Set.range e := by
      rintro ⟨a,rfl⟩
      exact hx (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
    rw [encodeState_outside e ψ x ho]
    simp
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  simp only [encodeState_at e he,Function.comp_apply]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSamplerMass
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

lemma natBasis_value (w z : ℕ) : (bitsValue (natBasis w z)).toNat=z%2^w := by
  change (bitsValue (fun i : Fin w => (BitVec.ofNat w z).getLsbD i.val)).toNat=z%2^w
  exact congrArg BitVec.toNat (bitsValue_bits (BitVec.ofNat w z))

end OrderTrial
end ExactQuantumFactoring


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

lemma append_leftRegister {p q : ℕ} (x : Basis p) (y : Basis q) :
    Fin.append x y ∘ leftRegister p q=x := by
  funext i
  exact Fin.append_left _ _ i
lemma append_replace_left {p q : ℕ} (x z : Basis p) (y : Basis q) :
    (leftRegister p q).replace (Fin.append x y) z=Fin.append z y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change (leftRegister p q).replace (Fin.append x y) z (leftRegister p q j)=_
    rw [Register.replace_inside,Fin.append_left]
  · have hj : ∀ k, leftRegister p q k≠Fin.natAdd p j := by
      intro k h
      have hh := congrArg Fin.val h
      change k.val=p+j.val at hh
      have := k.isLt
      omega
    rw [Register.replace_outside _ _ _ ⟨Fin.natAdd p j,hj⟩]
    simp only [Fin.append_right]

lemma leftProgram_basis {p q : ℕ} (ops : List (Instruction p)) (x : Basis p) (y : Basis q) :
    (programMatrix (leftProgram q ops)).mulVec (basisVector (Fin.append x y))=
      encodeState (fun z => Fin.append z y) ((programMatrix ops).mulVec (basisVector x)) := by
  rw [leftProgram,Register.placed_basis_state,append_leftRegister]
  congr 1
  funext z
  exact append_replace_left x z y

lemma encode_independent {α β : Type*} [Fintype α] [Fintype β] {p q : ℕ}
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (χ : β→ℂ) :
    encodeState (fun xy : α×β => Fin.append (e xy.1) (f xy.2)) (independentState ψ χ)=
      ∑ x, ψ x • encodeState (fun y => Fin.append (e x) (f y)) χ := by
  unfold encodeState independentState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [smul_smul]

lemma parallelProgram_basis {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q))
    (x : Basis p) (y : Basis q) :
    (programMatrix (parallelProgram A B)).mulVec (basisVector (Fin.append x y))=
      encodeState (appendEquiv p q) (independentState
        ((programMatrix A).mulVec (basisVector x)) ((programMatrix B).mulVec (basisVector y))) := by
  rw [parallelProgram,programMatrix_append,← Matrix.mulVec_mulVec,leftProgram_basis]
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,rightProgram_basis]
  exact (encode_independent id id _ _).symm

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
lemma integer (k : ℕ) (z : ℤ) : DyadicAt k (z:ℚ) := by
  refine ⟨z*2^k,?_⟩
  push_cast
  field_simp
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

lemma lambda_at {n d : ℕ} (hd : d≤2^n) : DyadicAt (n+10) (prescribedMass d) := by
  have h : DyadicAt (Nat.clog 2 d+10) (prescribedMass d) := ⟨1,by simp [prescribedMass]⟩
  exact h.mono (Nat.add_le_add_right (Nat.clog_le_of_le_pow hd) 10)

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
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma parallelProgram_entry {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q))
    (x z : Basis p) (y u : Basis q) :
    (programMatrix (parallelProgram A B)).mulVec (basisVector (Fin.append x y)) (Fin.append z u)=
      ((programMatrix A).mulVec (basisVector x) z)*((programMatrix B).mulVec (basisVector y) u) := by
  rw [parallelProgram_basis]
  exact encodeState_at (appendEquiv p q) (appendEquiv p q).injective _ (z,u)

lemma productLayout_apply {α β : Type*} {p q : ℕ} (e : α≃Basis p) (f : β≃Basis q) (xy : α×β) :
    productLayout e f xy=Fin.append (e xy.1) (f xy.2) := rfl

namespace OrderTrial

lemma guessProgram_entry (n : ℕ) (x : Guesses n) :
    (programMatrix (guessProgram n)).mulVec (basisVector (guessLayout n (guessZero n)))
      (guessLayout n x)=guessState n x := by
  simp only [guessProgram,guessLayout,productLayout_apply,guessZero,Equiv.refl_apply,
    parallelProgram_entry,hadamards_zero]
  rfl

lemma rawProgram_entry {w : ℕ} (s n : ℕ) (a m : Basis w) (x : Raw w s n) :
    (programMatrix (rawProgram w s n)).mulVec (basisVector (rawLayout w s n (rawZero s n a m)))
      (rawLayout w s n x)=rawState s n a m x := by
  simp only [rawProgram,rawLayout,productLayout_apply,rawZero,Equiv.refl_apply,
    parallelProgram_entry,hadamards_zero,guessProgram_entry]
  rfl

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_DyadicCompletion
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open Exactness OrderTrial

namespace Completion

lemma coeff_at (W t d : ℕ) (s z : ℚ) : DyadicAt (coinBits W t d) (coeff W t s z) := by
  apply (show DyadicAt (W+t+2) (coeff W t s z) from ⟨_,rfl⟩).mono
  unfold coinBits
  omega

lemma guess_at {W t d j : ℕ} {s z : ℚ} (hs : DyadicAt d s) (hz : DyadicAt j z)
    (hj : j ≤ coinBits W t d) : DyadicAt (coinBits W t d) (guessRetention W t s z) := by
  have hδ : DyadicAt t (1/(2:ℚ)^t) := ⟨1,by simp⟩
  have hA : DyadicAt (t+d) ((1-1/(2:ℚ)^t)*s) := by
    simpa using ((DyadicAt.integer t 1).sub hδ).mul hs
  have hC : DyadicAt (W+t+2) (coeff W t s z) := ⟨_,rfl⟩
  have hCA : DyadicAt (coinBits W t d) (coeff W t s z*((1-1/(2:ℚ)^t)*s)) := by
    simpa only [coinBits,Nat.add_assoc] using hC.mul hA
  have hR := (hz.mono hj).sub hCA
  have hG := hR.int_mul (2^(W+t))
  convert hG using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  unfold guessRetention completionRemainder coeff
  rw [pow_add]
  field_simp

lemma fair_eq_mass (W : ℕ) (y₀ : Basis W) :
    outcomeMass (fun y => y=y₀) (fairState W)=1/(2:ℝ)^W := by
  classical
  simp only [outcomeMass,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,fairState_mass,one_div,inv_pow]

lemma fresh_normalized {α : Type*} [Fintype α] (ψ : α→ℂ) (W t d : ℕ)
    (hψ : ∑ x,Complex.normSq (ψ x)=1) : ∑ x,Complex.normSq (fresh ψ W t d x)=1 := by
  have h₁ := RecordedHistory.append_normalized (fairState W)
    (fun _ => fairState (coinBits W t d)) (fair_normalized W) (fun _ => fair_normalized _)
  have h₂ := RecordedHistory.append_normalized ψ
    (fun _ => independentState (fairState W) (fairState (coinBits W t d))) hψ (fun _ => h₁)
  exact RecordedHistory.append_normalized (fairState t)
    (fun _ => independentState ψ (independentState (fairState W) (fairState (coinBits W t d))))
    (fair_normalized t) (fun _ => h₂)

/-- Actual fresh registers do NOT depend on s, goodness or the canonical output.
Those values are used only by the later classical test on the retained record. -/
theorem passed_mass {α : Type*} [Fintype α] {W t d j : ℕ}
    (ψ : α→ℂ) (good : α→Prop) (y₀ : Basis W) (s z : ℚ)
    (hψ : ∑ x,Complex.normSq (ψ x)=1) (hgood : outcomeMass good ψ=(s:ℝ))
    (hsd : DyadicAt d s) (hzd : DyadicAt j z) (hj : j ≤ coinBits W t d)
    (hs₀ : 0 < s) (hs₁ : s≤1) (ht : 0<t) (hz : 0<z)
    (hzA : z≤(1-1/(2:ℚ)^t)*s) :
    outcomeMass (passed good y₀ s z) (fresh ψ W t d)=(z:ℝ) := by
  have hb := completion_retention_bounds W t hs₀ hs₁ ht hz hzA
  have hC := dyadic_fair_threshold (coeff_at W t d s z) hb.1 hb.2.1
  have hG := dyadic_fair_threshold (guess_at hsd hzd hj) hb.2.2.1 (hb.2.2.2.le.trans (by norm_num))
  have hr : outcomeMass (rare (t:=t)) (fairState t)=1/(2:ℝ)^t :=
    fair_value_mass (by positivity : 0<2^t)
  have hnr : outcomeMass (fun b : Basis t => ¬rare b) (fairState t)=1-1/(2:ℝ)^t := by
    rw [RepeatedTrials.mass_compl _ _ (fair_normalized t),hr]
  have ho : outcomeMass (ordinaryPass (W:=W) (t:=t) (d:=d) good s z) (fresh ψ W t d)=
      (1-1/(2:ℝ)^t)*(s:ℝ)*(coeff W t s z:ℝ) := by
    rw [show ordinaryPass (W:=W) (t:=t) (d:=d) good s z =
      (fun r : Raw α W t d => ¬rare r.1 ∧ (good r.2.1 ∧ threshold (coeff W t s z) r.2.2.2)) from rfl]
    rw [fresh,independent_mass (fairState t)
      (independentState ψ (independentState (fairState W) (fairState (coinBits W t d))))
      (fun b => ¬rare b) (fun r => good r.1 ∧ threshold (coeff W t s z) r.2.2),
      independent_mass ψ (independentState (fairState W) (fairState (coinBits W t d)))
      good (fun r => threshold (coeff W t s z) r.2),
      independent_mass_right _ _ _ (fair_normalized W)]
    rw [hnr,hgood]
    rw [show outcomeMass (threshold (D:=coinBits W t d) (coeff W t s z))
      (fairState _)= (coeff W t s z:ℝ) from hC]
    ring
  have hg : outcomeMass (guessPass (t:=t) (d:=d) y₀ s z) (fresh ψ W t d)=
      (1/(2:ℝ)^t)*(1/(2:ℝ)^W)*(guessRetention W t s z:ℝ) := by
    rw [show guessPass (t:=t) (d:=d) y₀ s z =
      (fun r : Raw α W t d => rare r.1 ∧ (r.2.2.1=y₀ ∧ threshold (guessRetention W t s z) r.2.2.2)) from rfl]
    rw [fresh,independent_mass (fairState t)
      (independentState ψ (independentState (fairState W) (fairState (coinBits W t d))))
      rare (fun r => r.2.1=y₀ ∧ threshold (guessRetention W t s z) r.2.2),
      independent_mass_right ψ (independentState (fairState W) (fairState (coinBits W t d)))
        (fun r => r.1=y₀ ∧ threshold (guessRetention W t s z) r.2) hψ,
      independent_mass (fairState W) (fairState (coinBits W t d)) (fun y => y=y₀)
        (threshold (guessRetention W t s z)),fair_eq_mass,hr]
    rw [show outcomeMass (threshold (D:=coinBits W t d) (guessRetention W t s z))
      (fairState _)= (guessRetention W t s z:ℝ) from hG]
    ring
  change outcomeMass (fun r => ordinaryPass good s z r ∨ guessPass y₀ s z r)
    (fresh ψ W t d)=(z:ℝ)
  rw [outcomeMass_disjoint_or _ _ _ (by intro r h; exact h.1.1 h.2.1),ho,hg]
  have he := congrArg (fun q : ℚ => (q:ℝ)) (completion_mass W t s z)
  push_cast at he
  simpa [coeff,guessRetention] using he

lemma program_entry {q : ℕ} (P : List (Instruction q)) (W t d : ℕ) (a : Basis q)
    (r : Raw (Basis q) W t d) :
    (programMatrix (program P W t d)).mulVec
      (basisVector (layout q W t d ((fun _ => false),a,(fun _ => false),(fun _ => false))))
      (layout q W t d r)=fresh ((programMatrix P).mulVec (basisVector a)) W t d r := by
  simp only [program,layout,productLayout_apply,Equiv.refl_apply,parallelProgram_entry,hadamards_zero]
  rfl

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderCandidateLaw
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

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListTransition
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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


/-! The actual uniform-list transition in Section 5: its event, exact closed
probability, and unchanged repetition guarantee. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

lemma favorableBits_mass {m n b : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) (hmb : m ≤ 2^b) :
    outcomeMass (FavorableBits hm hb p₀ b) (fairState b)=
      (favorableCount m n : ℝ)/(2:ℝ)^b := by
  classical
  let : NeZero m := ⟨hm⟩
  let S : Finset (ZMod m)ˣ := Finset.univ.filter (FavorableUnit hm hb p₀)
  have he : (FavorableBits hm hb p₀ b)=
      (fun x => ∃ a∈S, (bitsValue x).toNat=(a : ZMod m).val) := by
    funext x
    apply propext
    simp only [FavorableBits,S,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun ⟨a,ha,hf⟩ => ⟨a,hf,ha.symm⟩,fun ⟨a,hf,ha⟩ => ⟨a,ha.symm,hf⟩⟩
  rw [he,outcomeMass_finite_union _ S _ (by
    intro x a c _ _ ha hc
    apply Units.ext
    exact ZMod.val_injective m (ha.symm.trans hc))]
  have hs : ∀ a∈S, outcomeMass (fun x : Basis b => (bitsValue x).toNat=(a : ZMod m).val)
      (fairState b)=1/(2:ℝ)^b := fun a _ =>
    fair_value_mass ((ZMod.val_lt (a : ZMod m)).trans_le hmb)
  rw [Finset.sum_congr rfl hs,Finset.sum_const,nsmul_eq_mul]
  have hc : S.card=favorableCount m n := by
    rw [favorableCount_eq_card hm hb hodd p₀,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hc,mul_one_div]

lemma coveringPower_le_twice {m : ℕ} (hm : 1 ≤ m) : 2^(Nat.clog 2 m) ≤ 2*m := by
  by_cases he : m=1
  · simp [he]
  · have hm' : 1 < m := by omega
    have hc := Nat.clog_pos (by decide : 1 < 2) hm'
    have hh := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hm'
    simp only [Nat.pred_eq_sub_one] at hh
    calc
      _ = 2^(Nat.clog 2 m-1)*2 := by rw [← pow_succ]; congr 1; omega
      _  ≤  2*m := by omega

lemma favorableBits_lower {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁ ≠ p₀) :
    1/(4*((n:ℝ)+1)) ≤  (favorableCount m n : ℝ)/(2:ℝ)^(Nat.clog 2 m) := by
  have hphi := totient_ratio_lower (by omega : 0 < m) hb
  have hhalf := totient_le_twice_favorableCount (by omega : m ≠ 0) hb hodd p₀ p₁ hne
  have hc := coveringPower_le_twice (by omega : 1 ≤ m)
  have hmR : (0:ℝ) < m := by positivity
  have hpR : (0:ℝ) < (2:ℝ)^(Nat.clog 2 m) := by positivity
  have hnR : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hphiR : (m:ℝ)/(n+1) ≤ m.totient := by
    have hh := (le_div_iff₀ hmR).mp hphi
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hh
  have hhalfR : (m.totient:ℝ) ≤ 2*favorableCount m n := by exact_mod_cast hhalf
  have hcR : (2:ℝ)^(Nat.clog 2 m) ≤ 2*m := by exact_mod_cast hc
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4*(n+1)) hpR).mpr
  have hh := (div_le_iff₀ hnR).mp hphiR
  nlinarith

/-- Source formula (5.4), over the literal independent fair-bit preparation. -/
theorem list_good_mass {m n : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) (K : ℕ) :
    outcomeMass (GoodList hm hb p₀ K) (tensorState (fairState (Nat.clog 2 m)) K)=
      1-(1-(favorableCount m n : ℝ)/(2:ℝ)^(Nat.clog 2 m))^K := by
  unfold GoodList
  rw [tensor_some_mass (fairState (Nat.clog 2 m)) K (FavorableBits hm hb p₀ (Nat.clog 2 m)) (fairState_normalized _),
    favorableBits_mass hm hb hodd p₀ (Nat.le_pow_clog (by decide) _)]

theorem list_good_lower {m n : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m < 2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁ ≠ p₀) :
    1-1/(2:ℝ)^(2*n) ≤ outcomeMass (GoodList (by omega : m ≠ 0) hb p₀ (n^5))
      (tensorState (fairState (Nat.clog 2 m)) (n^5)) := by
  rw [list_good_mass _ hb hodd p₀]
  have hl := favorableBits_lower hm hb hodd p₀ p₁ hne
  have hu := (mass_bounds (fairState (Nat.clog 2 m))
    (FavorableBits (by omega : m ≠ 0) hb p₀ (Nat.clog 2 m)) (fairState_normalized _)).2
  rw [favorableBits_mass _ hb hodd p₀ (Nat.le_pow_clog (by decide) _)] at hu
  apply repeated_success_lower hn _ hu
  calc
    _  ≤  1/(4*((n:ℝ)+1)) := by apply one_div_le_one_div_of_le (by positivity); nlinarith
    _  ≤  _ := hl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionEqualization
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open Exactness RepeatedTrials OrderTrial

lemma OrderTrial.DyadicAt.pow {d : ℕ} {x : ℚ} (h : DyadicAt d x) (k : ℕ) :
    DyadicAt (d*k) (x^k) := by
  induction k with
  | zero => simpa using DyadicAt.integer 0 1
  | succ k ih =>
    simpa only [pow_succ,Nat.mul_succ] using ih.mul h

namespace Completion

lemma target_at (n : ℕ) : DyadicAt n (target n) :=
  (DyadicAt.integer n 1).sub ⟨1,by simp⟩

lemma listSuccess_at {m n : ℕ} (hb : m ≤ 2^n) (K : ℕ) :
    DyadicAt (n*K) (listSuccess m n K) := by
  have hx : DyadicAt n ((favorableCount m n:ℚ)/(2:ℚ)^(Nat.clog 2 m)) :=
    (show DyadicAt (Nat.clog 2 m) _ from ⟨favorableCount m n,by simp⟩).mono
      (Nat.clog_le_of_le_pow hb)
  exact (DyadicAt.integer (n*K) 1).sub (((DyadicAt.integer n 1).sub hx).pow K)

lemma orderSuccess_at {n d : ℕ} (hd : d ≤ 2^n) (K : ℕ) :
    DyadicAt ((n+10)*K) (orderSuccess d K) := by
  have hx : DyadicAt (n+10) ((Nat.totient d:ℚ)*prescribedMass d) := by
    exact_mod_cast (lambda_at hd).int_mul (Nat.totient d)
  exact (DyadicAt.integer ((n+10)*K) 1).sub (((DyadicAt.integer (n+10) 1).sub hx).pow K)

lemma target_pos {n : ℕ} (hn : 1 ≤ n) : 0<target n := by
  have hp : (1:ℚ)<2^n := one_lt_pow₀ (by norm_num) (by omega)
  unfold target
  have hh := (div_lt_one (by positivity : (0:ℚ)<2^n)).mpr hp
  linarith

/-- The source repetition bound suffices for the unchanged equalization target.
No high-probability event is being declared to have probability one. -/
lemma target_le_ordinary {n : ℕ} (hn : 1 ≤ n) {s : ℚ}
    (hs : 1-1/(2:ℚ)^(2*n) ≤ s) :
    target n ≤ (1-1/(2:ℚ)^(2*n))*s := by
  have hp : (2:ℚ) ≤ 2^n := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) hn)
  have hpp : (0:ℚ)<2^n := by positivity
  have he : (2:ℚ)^(2*n)=(2^n)^2 := by rw [Nat.mul_comm 2 n,pow_mul]
  have hu : 0 ≤ 1/(2:ℚ)^n := by positivity
  have hl : 1/(2:ℚ)^n ≤ 1/2 := by exact one_div_le_one_div_of_le (by norm_num) hp
  have hδ : 1/(2:ℚ)^(2*n)=(1/(2:ℚ)^n)^2 := by rw [he,div_pow,one_pow]
  have hfactor : 0 ≤ 1-1/(2:ℚ)^(2*n) := by rw [hδ]; nlinarith
  have hh := mul_le_mul_of_nonneg_left hs hfactor
  unfold target
  rw [hδ] at hh ⊢
  nlinarith [sq_nonneg ((1/(2:ℚ)^n)^2)]

lemma listSuccess_lower {m n : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m<2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁≠p₀) :
    1-1/(2:ℚ)^(2*n) ≤ listSuccess m n (n^5) := by
  have hh := list_good_lower hn hm hb hodd p₀ p₁ hne
  rw [list_good_mass _ hb hodd p₀] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [listSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_natCast] using hh

lemma listSuccess_le_one {m n : ℕ} (hm : m≠0) (hb : m<2^n)
    (hodd : Odd m) (p₀ : Component m) (K : ℕ) : listSuccess m n K ≤ 1 := by
  have hh := (mass_bounds (tensorState (fairState (Nat.clog 2 m)) K)
    (GoodList hm hb p₀ K) (tensor_normalized _ K (fairState_normalized _))).2
  rw [list_good_mass hm hb hodd p₀] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [listSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_natCast] using hh

lemma orderSuccess_le_one {w n s : ℕ} (hn : 1 ≤ n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (K : ℕ) : orderSuccess (orderOf u) K ≤ 1 := by
  have hh := (mass_bounds (tensorState (rawState s n a m) K)
    (fun x => orderResult s n a m K x=orderOf u)
    (tensor_normalized _ K (raw_normalized s n a m))).2
  rw [orderResult_mass hn hs a m hm u ha hdB] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [orderSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_mul,Rat.cast_natCast] using hh

/-- Local same-record equalization for the literal n^5 repeated order trial. -/
theorem order_passed_mass {w n s : ℕ} (hn : 128 ≤ n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (y₀ : Basis (transitionWidth n)) :
    outcomeMass (passed (fun x => orderResult s n a m (n^5) x=orderOf u) y₀
      (orderSuccess (orderOf u) (n^5)) (target n))
      (fresh (tensorState (rawState s n a m) (n^5))
        (transitionWidth n) (2*n) ((n+10)*n^5))=(target n:ℝ) := by
  have hlow := orderSuccess_lower hn hs a m hm u ha hdB
  have hp := target_pos (by omega : 1 ≤ 2*n)
  apply passed_mass _ _ _ _ _ (tensor_normalized _ _ (raw_normalized s n a m))
    (by rw [orderResult_mass (by omega) hs a m hm u ha hdB]; simp [orderSuccess])
    (orderSuccess_at hdB.le _) (target_at n) (by unfold coinBits; omega)
    (by exact hp.trans_le hlow) (orderSuccess_le_one (by omega) hs a m hm u ha hdB _)
    (by omega) (target_pos (by omega)) (target_le_ordinary (by omega) hlow)

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletedOrderSlots
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open Exactness RepeatedTrials OrderTrial

namespace Completion

/-- Dummy slots retain their internal preparation too. Only the constant output
is visible to the controller; no branch-local normalization is performed. -/
lemma dummy_passed_mass {α : Type*} [Fintype α] (ψ : α→ℂ) (n d : ℕ)
    (hn : 128 ≤ n) (hψ : ∑ x,Complex.normSq (ψ x)=1) (y₀ : Basis (transitionWidth n)) :
    outcomeMass (passed (fun _ => True) y₀ 1 (target n))
      (fresh ψ (transitionWidth n) (2*n) d)=(target n:ℝ) := by
  apply passed_mass ψ _ y₀ 1 (target n) hψ
  · simpa only [outcomeMass,ite_true, if_true,Rat.cast_one] using hψ
  · exact DyadicAt.integer d 1
  · exact target_at n
  · unfold coinBits; omega
  · norm_num
  · norm_num
  · omega
  · exact target_pos (by omega)
  · apply target_le_ordinary (by omega : 1 ≤ n)
    have hp : (0:ℚ) ≤ 1/(2:ℚ)^(2*n) := by positivity
    linarith

end Completion

namespace OrderSlots

lemma sampleExponent_spec {n : ℕ} (hn : 128 ≤ n) :
    2^(sampleExponent n+2)=(2^n)^16 := by
  rw [←pow_mul]
  congr 1
  unfold sampleExponent
  omega

lemma fresh_normalized (n : ℕ) (a m : Basis n) :
    ∑ r,Complex.normSq (fresh n a m r)=1 :=
  Completion.fresh_normalized _ _ _ _ (tensor_normalized _ _ (raw_normalized _ _ a m))

lemma unitOrder_lt {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) :
    unitOrder a m < 2^n := by
  classical
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  unfold unitOrder
  split_ifs with h
  · have hh := orderOf_le_card (x:=h.2.unit)
    rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] at hh
    exact (hh.trans (Nat.totient_le _)).trans_lt (bitsValue m).isLt
  · positivity

lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) :
    outcomeMass (passed a m) (fresh n a m)=(Completion.target n:ℝ) := by
  classical
  unfold passed
  split_ifs with h
  · have hlt := unitOrder_lt a m hm
    simp only [unitOrder,dite_eq_left h] at hlt
    exact Completion.order_passed_mass hn (sampleExponent_spec hn) a m hm h.2.unit
      h.2.unit_spec.symm hlt (canonical a m)
  · exact Completion.dummy_passed_mass _ n _ hn
      (tensor_normalized _ _ (raw_normalized _ _ a m)) (canonical a m)

/-- Every supplied base has exactly z retained mass. Out-of-range entries and nonunits are dummy slots,
not an assumption that a random list consists only of units. -/
theorem all_passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (as : Fin (n^5)→Basis n) :
    outcomeMass (fun r : Fin (n^5)→Result n => ∀ i,passed (as i) m (r i))
      (productState (fun i => fresh n (as i) m))=(Completion.target n:ℝ)^(n^5) := by
  exact productState_constant_mass _ _ _ (fun _ => passed_mass hn _ _ hm)

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhaseOracle
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_vector _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork

lemma phase_twice_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (programMatrix [phaseAt t,phaseAt t]).mulVec (basisVector x) =
      (if x t then (-1:ℂ) else 1) • basisVector x := by
  classical
  rw [programMatrix_cons, programMatrix_singleton, ← Matrix.mulVec_mulVec]
  funext y
  rw [phaseAt_apply, phaseAt_apply]
  simp only [Pi.smul_apply, smul_eq_mul, basisVector]
  by_cases h : y=x
  · subst y
    cases x t <;> simp [Complex.I_mul_I]
  · simp [h]

namespace BooleanNetwork

lemma phaseOracle_basis {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r)
    (x : Basis n) :
    (programMatrix (phaseOracle c hr)).mulVec (basisVector (packed r x (fun _ => false))) =
      (if c.eval x 0 then (-1:ℂ) else 1) • basisVector (packed r x (fun _ => false)) := by
  rw [phaseOracle, programMatrix_append, programMatrix_append,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oracleOn_basis]
  simp only [Bool.false_xor]
  rw [phase_twice_basis, Matrix.mulVec_smul, oracleOn_basis]
  have ht : packed r x (c.eval x) phaseTarget = c.eval x 0 := by
    exact packed_target x (c.eval x) 0
  rw [ht]
  congr 1
  funext i
  simp

/-- The same actual program applies its diagonal predicate phase coherently,
not just on classical basis inputs. -/
lemma phaseOracle_state {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r)
    (ψ : Basis n → ℂ) :
    (programMatrix (phaseOracle c hr)).mulVec
      (encodeState (fun x => packed r x (fun _ : Fin 1 => false)) ψ) =
      encodeState (fun x => packed r x (fun _ : Fin 1 => false))
        (fun x => (if c.eval x 0 then (-1:ℂ) else 1)*ψ x) := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, phaseOracle_basis, smul_smul]
  unfold encodeState
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  ring

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalAmplification
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_vector _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork Exactness

lemma RespectsSector.adjoint {ι : Type*} (S : ι → Prop) (U : Matrix ι ι ℂ)
    (h : RespectsSector S U) : RespectsSector S U.conjTranspose := by
  intro x y hxy
  change star (U y x) = 0
  rw [h y x (fun hyx => hxy hyx.symm),star_zero]

lemma RespectsSector.supported {ι : Type*} [Fintype ι] (S : ι → Prop)
    (U : Matrix ι ι ℂ) (h : RespectsSector S U) (v : ι → ℂ)
    (hv : Supported S v) : Supported S (U.mulVec v) := by
  classical
  intro x hx
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : S y
  · exact mul_eq_zero.mpr (Or.inl (h x y (by tauto)))
  · rw [hv y hy,mul_zero]

lemma signState_supported {ι : Type*} (S : ι → Prop) (p : ι → Bool)
    (v : ι → ℂ) (hv : Supported S v) : Supported S (signState p v) := by
  intro x hx
  simp only [signState,hv x hx,mul_zero]

lemma signState_eq {ι : Type*} (p : ι → Bool) (v : ι → ℂ) :
    signState p v = fun x => v x-2*goodPart (fun y => p y=true) v x := by
  classical
  funext x
  simp only [signState,goodPart]
  split_ifs <;> ring

lemma sector_zero_sign {ι : Type*} [DecidableEq ι] (S : ι → Prop)
    (z : ι) (p : ι → Bool) (hp : ∀ x, S x → (p x=true ↔ x=z))
    (v : ι → ℂ) (hv : Supported S v) :
    signState p v = v - ((2*v z) • basisVector z) := by
  classical
  funext x
  simp only [signState,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,basisVector]
  by_cases hx : S x
  · by_cases he : x=z
    · subst x
      simp [hp z hx]
      ring
    · simp [he, show p x ≠ true from fun h => he ((hp x hx).mp h)]
  · have hvx := hv x hx
    by_cases he : x=z
    · subst x
      simp [hvx]
    · simp [he,hvx]

lemma adjoint_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (z : ι) (v : ι → ℂ) :
    U.conjTranspose.mulVec v z = finiteInner (U.mulVec (basisVector z)) v := by
  rw [matrix_basisVector]
  rfl

/-- The physical sign on zero work, conjugated by a reversible preparation,
is minus the reflection about its output, within the invariant input fiber. -/
lemma conjugated_zero_sign {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hu : U ∈ Matrix.unitaryGroup ι ℂ)
    (S : ι → Prop) (hS : RespectsSector S U) (z : ι)
    (p : ι → Bool) (hp : ∀ x, S x → (p x=true ↔ x=z))
    (v : ι → ℂ) (hv : Supported S v) :
    U.mulVec (signState p (U.conjTranspose.mulVec v)) =
      -stateReflection (U.mulVec (basisVector z)) v := by
  rw [sector_zero_sign S z p hp _
    ((hS.adjoint S U).supported S U.conjTranspose _ hv)]
  have huu : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  rw [Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    huu,Matrix.one_mulVec,adjoint_coordinate]
  funext x
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.neg_apply,stateReflection]
  ring

lemma amplificationProgram_state {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r)
    (z : Basis n) :
    (programMatrix (amplificationProgram ops good zero hg hz)).mulVec
      (basisVector (packed r z (fun _ : Fin 1 => false))) =
    encodeState (fun x => packed r x (fun _ : Fin 1 => false))
      ((programMatrix ops).mulVec (signState (fun x => zero.eval x 0)
        ((programMatrix ops).conjTranspose.mulVec
          (signState (fun x => good.eval x 0)
            ((programMatrix ops).mulVec (basisVector z)))))) := by
  rw [amplificationProgram]
  simp only [programMatrix_append,← Matrix.mulVec_mulVec]
  rw [firstProgram_basis,phaseOracle_state,firstProgram_state,programMatrix_reverse]
  rw [phaseOracle_state,firstProgram_state]
  rfl

/-- Exact amplitude amplification implemented over the fixed named gates.
The semantic premises are preparation mass and the unchanged-input invariant,
not a gate oracle or an assumed reflection. -/
theorem physical_quarter_amplification {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r)
    (S : Basis n → Prop) (hS : RespectsSector S (programMatrix ops))
    (z : Basis n) (hstart : S z)
    (hzero : ∀ x, S x → (zero.eval x 0=true ↔ x=z))
    (hquarter : outcomeMass (fun x => good.eval x 0=true)
      ((programMatrix ops).mulVec (basisVector z)) = 1/4) :
    (programMatrix (amplificationProgram ops good zero hg hz)).mulVec
      (basisVector (packed r z (fun _ : Fin 1 => false))) =
      encodeState (fun x => packed r x (fun _ : Fin 1 => false))
        (fun x => -2*goodPart (fun y => good.eval y 0=true)
          ((programMatrix ops).mulVec (basisVector z)) x) := by
  classical
  have hs : Supported S (basisVector z) := by
    intro x hx
    simp [basisVector,show x ≠ z from fun h => hx (h ▸ hstart)]
  have hv := hS.supported S (programMatrix ops) (basisVector z) hs
  have hn : (∑ x, Complex.normSq ((programMatrix ops).mulVec (basisVector z) x)) = 1 := by
    rw [unitary_mass _ (programMatrix_unitary ops)]
    simp [basisVector]
  rw [amplificationProgram_state,
    conjugated_zero_sign _ (programMatrix_unitary ops) S hS z _ hzero _
      (signState_supported S _ _ hv),signState_eq,
    one_reflection _ _ hn hquarter]
  congr 1
  funext x
  simp only [Pi.neg_apply]
  ring

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ReadOnlyCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

lemma Primitive.nonTarget_zero (p : Primitive) (x y : Basis p.arity) (i : Fin p.arity)
    (hi : i.val+1<p.arity) (hne : x i≠y i) : p.localMatrix x y=0 := by
  cases p with
  | not => simp only [Primitive.arity] at hi; omega
  | hadamard => simp only [Primitive.arity] at hi; omega
  | phase => simp only [Primitive.arity] at hi; omega
  | cnot =>
    rw [cnot_localMatrix]
    have hc : cnotPerm y i=y i := by
      fin_cases i <;> simp_all [cnotPerm,Primitive.arity]
    have hxy : x≠cnotPerm y := fun he => hne ((congrFun he i).trans hc)
    change (if x=_ then (1 : ℂ) else 0)=0
    exact ite_eq_right hxy
  | toffoli =>
    rw [toffoli_localMatrix]
    have hc : toffoliPerm y i=y i := by
      fin_cases i <;> simp_all [toffoliPerm,Primitive.arity]
    have hxy : x≠toffoliPerm y := fun he => hne ((congrFun he i).trans hc)
    change (if x=_ then (1 : ℂ) else 0)=0
    exact ite_eq_right hxy

lemma Gate.base_nonTarget_zero (g : Gate) (x y : Basis g.primitive.arity)
    (i : Fin g.primitive.arity) (hi : i.val+1<g.primitive.arity) (hne : x i≠y i) :
    g.baseLocalMatrix x y=0 := by
  rw [g.baseLocalMatrix_eq]
  split_ifs
  · change star (g.primitive.localMatrix y x)=0
    rw [g.primitive.nonTarget_zero y x i hi (Ne.symm hne),star_zero]
  · exact g.primitive.nonTarget_zero x y i hi hne

/-- In the literal fixed alphabet, all but the final wire are controls.
The inverse and added-control variants preserve these same wires. -/
lemma Gate.nonTarget_zero (g : Gate) (x y : Basis g.arity) (i : Fin g.arity)
    (hi : i.val+1<g.arity) (hne : x i≠y i) : g.localMatrix x y=0 := by
  rcases g with ⟨p,inv,ctrl⟩
  cases ctrl
  · exact Gate.base_nonTarget_zero ⟨p,inv,false⟩ x y i hi hne
  · change Basis (p.arity+1) at x y
    change Fin (p.arity+1) at i
    rw [Gate.controlled_localMatrix]
    change controlledMatrix (Gate.mk p inv true).baseLocalMatrix
      (x 0,Fin.tail x) (y 0,Fin.tail y)=0
    by_cases ht : x 0=y 0
    · have hi0 : i.val≠0 := by
        intro hi0
        have hie : i=0 := Fin.ext hi0
        exact hne (hie ▸ ht)
      have hi' : i.val+1<p.arity+1 := hi
      let j : Fin p.arity := ⟨i.val-1,by omega⟩
      have hji : j.succ=i := Fin.ext (by simp only [Fin.val_succ,j]; omega)
      have hjn : Fin.tail x j≠Fin.tail y j := by
        simpa only [Fin.tail_def,hji] using hne
      have htail : Fin.tail x≠Fin.tail y := fun he => hjn (congrFun he j)
      dsimp only [controlledMatrix,Matrix.of_apply]
      rw [ite_eq_left ht]
      split_ifs
      · exact Gate.base_nonTarget_zero ⟨p,inv,true⟩ _ _ j (by simp only [j]; omega) hjn
      · simp
    · simp [controlledMatrix,ht]

lemma Instruction.nonzero_eq {q : ℕ} (o : Instruction q) (x y : Basis q)
    (h : o.matrix x y≠0) (i : Fin q) (hi : i≠o.target) : x i=y i := by
  classical
  have houtside : ∀ i : Fin q,(∀ j,o.wire j≠i)→x i=y i := by
    by_contra hn
    exact h (by simp only [Instruction.matrix,ite_eq_right hn])
  have hlocal : o.gate.localMatrix (x∘o.wire) (y∘o.wire)≠0 := by
    simpa only [Instruction.matrix,ite_eq_left houtside,Gate.localMatrix,Matrix.of_apply] using h
  by_cases hw : ∃ j,o.wire j=i
  · obtain ⟨j,rfl⟩ := hw
    have hj : j.val+1<o.gate.arity := by
      have hjne : j.val≠o.gate.arity-1 := by
        intro he
        apply hi
        unfold Instruction.target
        congr 1
        exact Fin.ext he
      omega
    by_contra hne
    exact hlocal (o.gate.nonTarget_zero _ _ j hj hne)
  · exact houtside i (by simpa only [not_exists] using hw)


end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ControlledHadamard
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

lemma controlledHadamardAt_matrix {q : ℕ} (c t : Fin q) (h : c≠t) (x y : Basis q) :
    (controlledHadamardAt c t h).matrix y x =
      if x c then (hadamardAt t).matrix y x else if y=x then 1 else 0 := by
  classical
  have ho : (∀ i : Fin q,(∀ j : Fin 2, (![c,t] : Fin 2→Fin q) j≠i)→y i=x i) ↔
      (∀ i : Fin q, i≠c→i≠t→y i=x i) := by
    constructor
    · intro hh i hic hit
      apply hh i
      intro j
      fin_cases j
      · exact Ne.symm hic
      · exact Ne.symm hit
    · intro hh i hi
      exact hh i (Ne.symm (hi 0)) (Ne.symm (hi 1))
  change (if ∀ i : Fin q,(∀ j : Fin 2, (![c,t] : Fin 2→Fin q) j≠i)→y i=x i then
    (Gate.mk .hadamard false true).matrix
      (List.ofFn (y∘(![c,t] : Fin 2→Fin q)))
      (List.ofFn (x∘(![c,t] : Fin 2→Fin q))) else 0)=_
  simp only [ho,List.ofFn_succ,List.ofFn_zero,Function.comp_apply,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  rw [hadamardAt_matrix]
  have hyc : (∀ i : Fin q,i≠t→y i=x i) ↔ y c=x c ∧ (∀ i : Fin q,i≠c→i≠t→y i=x i) := by
    constructor
    · exact fun hh => ⟨hh c h,fun i _ hit => hh i hit⟩
    · rintro ⟨hc,hh⟩ i hit
      by_cases hic : i=c
      · simpa [hic] using hc
      · exact hh i hic hit
  have heq : y=x ↔ y c=x c ∧ y t=x t ∧ (∀ i : Fin q,i≠c→i≠t→y i=x i) := by
    constructor
    · rintro rfl; simp
    · rintro ⟨hc,ht,hh⟩
      funext i
      by_cases hic : i=c
      · simpa [hic] using hc
      · by_cases hit : i=t
        · simpa [hit] using ht
        · exact hh i hic hit
  simp only [hyc,heq]
  cases xc : x c <;> cases yc : y c <;>
    simp only [Gate.matrix,Gate.baseMatrix,Bool.true_eq,Bool.false_eq_true,ite_true, if_true,ite_false, if_false,
      Primitive.matrix,List.cons.injEq, and_true]
  all_goals split_ifs <;> simp_all

/-- On a sector with a fixed control, controlled H is H or the identity on an
arbitrary coherent state, including all old retained work. -/
lemma controlledHadamardAt_sector {q : ℕ} (c t : Fin q) (h : c≠t) (b : Bool)
    (ψ : State q) (hs : Supported (fun x => x c=b) ψ) :
    (controlledHadamardAt c t h).matrix.mulVec ψ=
      if b then (hadamardAt t).matrix.mulVec ψ else ψ := by
  classical
  funext y
  change (∑ x,(controlledHadamardAt c t h).matrix y x*ψ x)=_
  simp_rw [controlledHadamardAt_matrix]
  cases b
  · simp only [Bool.false_eq_true,ite_false, if_false]
    calc
      _ = ∑ x : Basis q,(if y=x then (1 : ℂ) else 0)*ψ x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x c=false
        · simp [hx]
        · rw [hs x hx]; simp
      _ = ψ y := by simp
  · simp only [ite_true, if_true]
    change _=∑ x,(hadamardAt t).matrix y x*ψ x
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x c=true
    · simp [hx]
    · rw [hs x hx]; simp

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExactnessFurther2
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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

namespace Exactness

lemma RespectsSector.one {ι : Type*} [DecidableEq ι] (S : ι→Prop) :
    RespectsSector S (1 : Matrix ι ι ℂ) := by
  intro x y h
  have hxy : x≠y := fun he => h (he ▸ Iff.rfl)
  simp [hxy]

lemma RespectsSector.mul {ι : Type*} [Fintype ι] (S : ι→Prop)
    (U V : Matrix ι ι ℂ) (hU : RespectsSector S U) (hV : RespectsSector S V) :
    RespectsSector S (U*V) := by
  classical
  intro x y hxy
  apply Finset.sum_eq_zero
  intro z _
  change U x z*V z y=0
  by_cases hxz : S x↔S z
  · rw [hV z y (fun hzy => hxy (hxz.trans hzy)),mul_zero]
  · rw [hU x z hxz,zero_mul]

end Exactness
open Exactness

lemma Instruction.respects_input {q : ℕ} (o : Instruction q) (inputs : Finset (Fin q))
    (ht : o.target∉inputs) (z : Basis q) : RespectsSector (inputSector inputs z) o.matrix := by
  intro x y hxy
  by_contra hne
  apply hxy
  have he (i : Fin q) (hi : i∈inputs) : x i=y i :=
    o.nonzero_eq x y hne i (fun h => ht (h ▸ hi))
  constructor
  · intro hx i hi
    rw [←he i hi]
    exact hx i hi
  · intro hy i hi
    rw [he i hi]
    exact hy i hi

lemma program_respects_input {q : ℕ} (inputs : Finset (Fin q))
    (P : List (Instruction q)) (hP : ReadOnly inputs P) (z : Basis q) :
    RespectsSector (inputSector inputs z) (programMatrix P) := by
  induction P with
  | nil => exact RespectsSector.one _
  | cons o P ih =>
    rw [programMatrix_cons]
    exact RespectsSector.mul _ _ _
      (ih (fun p hp => hP p (by simp [hp])))
      (o.respects_input inputs (hP o (by simp)) z)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MaskedPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open Exactness BitArithmetic BooleanNetwork

lemma rightProgram_state {p q : ℕ} (ops : List (Instruction q)) (x : Basis p) (ψ : State q) :
    (programMatrix (rightProgram p ops)).mulVec (encodeState (fun y => Fin.append x y) ψ)=
      encodeState (fun y => Fin.append x y) ((programMatrix ops).mulVec ψ) := by
  apply matrix_encodeState
  intro y
  simpa only [matrix_basisVector] using rightProgram_basis ops x y

lemma encode_append_supported {p q : ℕ} (x : Basis p) (ψ : State q) (i : Fin p) :
    Supported (fun y : Basis (p+q) => y (i.castAdd q)=x i)
      (encodeState (fun y => Fin.append x y) ψ) := by
  intro y hy
  apply encodeState_outside
  rintro ⟨z,rfl⟩
  exact hy (Fin.append_left _ _ _)

lemma maskGate_state (n : ℕ) (j : Fin n) (mask : Basis n) (ψ : State n) :
    (maskGate n j).matrix.mulVec (encodeState (fun y => Fin.append mask y) ψ)=
      encodeState (fun y => Fin.append mask y)
        (if mask j then (hadamardAt j).matrix.mulVec ψ else ψ) := by
  rw [maskGate,controlledHadamardAt_sector _ _ _ (mask j) _ (encode_append_supported mask ψ j)]
  cases hj : mask j
  · rfl
  · have he : (hadamardAt j).place (rightRegister n n)=hadamardAt (Fin.natAdd n j) := rfl
    have hh := rightProgram_state [hadamardAt j] mask ψ
    simpa only [rightProgram,List.map_cons,List.map_nil,he,programMatrix_singleton,ite_true, if_true] using hh

/-- The mask is ordinary retained input data. This equation is valid before
any measurement and for arbitrary coherent states in the target register. -/
lemma maskedPrefix_state (n k : ℕ) (h : k ≤ n) (mask : Basis n) (ψ : State n) :
    (programMatrix (maskedPrefix n k h)).mulVec (encodeState (fun y => Fin.append mask y) ψ)=
      encodeState (fun y => Fin.append mask y) ((programMatrix (selectedPrefix mask k h)).mulVec ψ) := by
  induction k with
  | zero => simp only [maskedPrefix,selectedPrefix,programMatrix_nil,Matrix.one_mulVec]
  | succ k ih =>
    rw [maskedPrefix,programMatrix_append,programMatrix_singleton,← Matrix.mulVec_mulVec,ih,
      maskGate_state,selectedPrefix,programMatrix_append,← Matrix.mulVec_mulVec]
    split_ifs <;> simp only [programMatrix_singleton,programMatrix_nil,Matrix.one_mulVec]

lemma selectedPrefix_eq (n b k : ℕ) (h : k ≤ n) :
    selectedPrefix (prefixMask n b) k h=hadamardPrefix n (min k b) (by omega) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [selectedPrefix,ih]
    by_cases hk : k<b
    · have hk0 : min k b=k := Nat.min_eq_left (by omega)
      have hk1 : min (k+1) b=k+1 := Nat.min_eq_left (by omega)
      simp only [prefixMask,hk,decide_true,ite_true, if_true,hk0,hk1,hadamardPrefix]
    · have hk0 : min k b=b := Nat.min_eq_right (by omega)
      have hk1 : min (k+1) b=b := Nat.min_eq_right (by omega)
      simp only [prefixMask,hk,decide_false,Bool.false_eq_true,ite_false, if_false,hk0,hk1,List.append_nil]

/-- Uniformly n gates suffice for EVERY runtime width b<=n. Unlike n fair
bits, the upper n-b bits remain exactly zero, as required for the source list
success bound on small cofactors. -/
lemma maskedPrefix_zero (n b : ℕ) (hb : b ≤ n) :
    (programMatrix (maskedPrefix n n le_rfl)).mulVec
      (basisVector (Fin.append (prefixMask n b) (fun _ => false))) =
      encodeState (fun y => Fin.append (prefixMask n b) y)
        (fun y => if ∀ i : Fin n,b ≤ i.val→y i=false then (Real.sqrt 2:ℂ)⁻¹^b else 0) := by
  rw [← encodeState_basis (fun y => Fin.append (prefixMask n b) y) (fun _ => false),
    maskedPrefix_state,selectedPrefix_eq]
  simp only [Nat.min_eq_right hb,hadamardPrefix_zero]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RuntimeListPreparation
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
open Exactness BitArithmetic BooleanNetwork

lemma listMaskNet_eval (n : ℕ) (m : Basis n) :
    (listMaskNet n).eval m=prefixMask n (Nat.clog 2 (bitsValue m).toNat) := by
  funext i
  have hp : 2^i.val<2^n := Nat.pow_lt_pow_right (by decide) i.isLt
  simp only [listMaskNet,eval_vector,wordLt_eval,wordConstant_eval,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp,eval_select,Function.comp_id,prefixMask]
  congr 1
  exact propext (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).symm

lemma padBits_at {b n : ℕ} (h : b ≤ n) (x : Basis b) (i : Fin b) :
    padBits h x (i.castLE h)=x i := by
  simp [padBits,i.isLt]

lemma padBits_injective {b n : ℕ} (h : b ≤ n) : Function.Injective (padBits h) := by
  intro x y hh
  funext i
  have he := congrFun hh (i.castLE h)
  simpa only [padBits_at] using he

lemma padBits_range {b n : ℕ} (h : b ≤ n) (y : Basis n) :
    y∈Set.range (padBits h) ↔ ∀ i : Fin n,b ≤ i.val→y i=false := by
  constructor
  · rintro ⟨x,rfl⟩ i hi
    simp [padBits,Nat.not_lt.mpr hi]
  · intro hh
    refine ⟨fun i => y (i.castLE h),?_⟩
    funext i
    unfold padBits
    split_ifs with hi
    · rfl
    · exact (hh i (by omega)).symm

lemma prefixFair_encode {b n : ℕ} (hb : b ≤ n) :
    (fun y : Basis n => if ∀ i : Fin n,b ≤ i.val→y i=false then (Real.sqrt 2:ℂ)⁻¹^b else 0)=
      encodeState (padBits hb) (fairState b) := by
  classical
  funext y
  by_cases hy : y∈Set.range (padBits hb)
  · obtain ⟨x,rfl⟩ := hy
    rw [encodeState_at _ (padBits_injective hb),ite_eq_left ((padBits_range hb _).mp ⟨x,rfl⟩)]
    rfl
  · rw [encodeState_outside _ _ y hy,ite_eq_right (fun hh => hy ((padBits_range hb y).mpr hh))]

/-- Runtime active-width preparation, stated as an exact physical program
column over the source's b=ceil(log₂m) fair state. -/
lemma maskedList_state (n : ℕ) (m : Basis n) :
    (programMatrix (maskedPrefix n n le_rfl)).mulVec
      (basisVector (Fin.append ((listMaskNet n).eval m) (fun _ => false)))=
      encodeState (fun y => Fin.append ((listMaskNet n).eval m)
        (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y))
        (fairState (Nat.clog 2 (bitsValue m).toNat)) := by
  rw [listMaskNet_eval,maskedPrefix_zero _ _ (Nat.clog_le_of_le_pow (bitsValue m).isLt.le),
    prefixFair_encode (Nat.clog_le_of_le_pow (bitsValue m).isLt.le),encodeState_comp]
  rfl

lemma padBits_value {b n : ℕ} (hb : b ≤ n) (x : Basis b) :
    (bitsValue (padBits hb x)).toNat=(bitsValue x).toNat := by
  have he : bitsValue (padBits hb x)=(bitsValue x).setWidth n := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (bitsValue (padBits hb x)).getLsbD i=padBits hb x ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
      BitVec.getLsbD_setWidth]
    simp only [hi,decide_true,Bool.true_and,padBits]
    split_ifs with hib
    · exact (bitsValue_bit x ⟨i,hib⟩).symm
    · exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm
  rw [he,setWidth_toNat_of_le hb]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionWords
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open Exactness RepeatedTrials

namespace TransitionWords

lemma read_encode {n K : ℕ} (a : Fin K→Basis n) (i : Fin K) : read (encode a) i=a i := by
  funext j
  simp only [read,encode,Fin.cast_cast,Fin.cast_eq_self,Equiv.symm_apply_apply,Fin.val_castSucc]
  rw [dite_eq_left i.isLt]

end TransitionWords

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListSamplerCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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


namespace ExactQuantumFactoring.ListSampler
open Exactness BitArithmetic BooleanNetwork

lemma word_mask {n : ℕ} (m mask y : Basis n) (i : Fin n) :
    word m mask y ⟨n+i.val,by have := i.isLt; dsimp [width]; omega⟩=mask i := by
  have h₀ : ¬n+i.val<n := by omega
  have h₁ : n+i.val<n+n := by omega
  simp only [word,dite_eq_right h₀,dite_eq_left h₁,Nat.add_sub_cancel_left]

lemma word_sample {n : ℕ} (m mask y : Basis n) (i : Fin n) :
    word m mask y ⟨n+n+i.val,by have := i.isLt; dsimp [width]; omega⟩=y i := by
  have h₀ : ¬n+n+i.val<n := by omega
  have h₁ : ¬n+n+i.val<n+n := by omega
  have h₂ : n+n+i.val<n+n+n := by omega
  simp only [word,dite_eq_right h₀,dite_eq_right h₁,dite_eq_left h₂,Nat.add_sub_cancel_left]

lemma word_work {n : ℕ} (m mask y : Basis n) (i : Fin (width n)) (hi : n+n+n ≤ i.val) :
    word m mask y i=false := by
  simp only [word,dite_eq_right (show ¬i.val<n by omega),dite_eq_right (show ¬i.val<n+n by omega),
    dite_eq_right (Nat.not_lt.mpr hi)]

lemma packed_word {n : ℕ} (m mask : Basis n) :
    packed (n+work n) m mask=word m mask (fun _ => false) := by
  funext i
  unfold packed word
  split_ifs <;> rfl

lemma maskRegister_val (n : ℕ) (i : Fin (n+n)) : (maskRegister n i).val=n+i.val := rfl

lemma word_register {n : ℕ} (m mask y : Basis n) :
    word m mask y ∘ maskRegister n=Fin.append mask y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact (word_mask m mask y j).trans (Fin.append_left _ _ _).symm
  · have he : maskRegister n (Fin.natAdd n j)=⟨n+n+j.val,by have := j.isLt; dsimp [width]; omega⟩ :=
      Fin.ext (by simp only [maskRegister_val,Fin.val_natAdd]; omega)
    rw [Function.comp_apply,he,word_sample,Fin.append_right]

lemma word_replace {n : ℕ} (m mask y mask' y' : Basis n) :
    (maskRegister n).replace (word m mask y) (Fin.append mask' y')=word m mask' y' := by
  funext i
  by_cases hi₀ : i.val<n
  · have ho : ∀ j,maskRegister n j≠i := by
      intro j hh
      have h := congrArg Fin.val hh
      rw [maskRegister_val] at h
      omega
    rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
    simp only [word,hi₀,dite_eq_left]
  · by_cases hi₁ : i.val<n+n+n
    · let j : Fin (n+n) := ⟨i.val-n,by omega⟩
      have he : maskRegister n j=i := Fin.ext (by rw [maskRegister_val]; dsimp [j]; omega)
      rw [←he,Register.replace_inside]
      exact (congrFun (word_register m mask' y') j).symm
    · have ho : ∀ j,maskRegister n j≠i := by
        intro j hh
        have h := congrArg Fin.val hh
        rw [maskRegister_val] at h
        have := j.isLt
        omega
      rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
      change word m mask y i=word m mask' y' i
      rw [word_work _ _ _ _ (by omega),word_work _ _ _ _ (by omega)]

lemma circuit_state (n : ℕ) (m : Basis n) :
    (programMatrix (circuit n)).mulVec
      (basisVector (word m (fun _ => false) (fun _ => false)))=
    encodeState (fun y => word m ((listMaskNet n).eval m)
      (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y))
      (fairState (Nat.clog 2 (bitsValue m).toNat)) := by
  rw [circuit,programMatrix_append,←Matrix.mulVec_mulVec,←packed_word,
    oracleOn_basis]
  simp only [Bool.false_xor]
  rw [packed_word,Register.placed_basis_state,word_register,maskedList_state,
    encodeState_comp]
  congr 1
  funext y
  exact word_replace _ _ _ _ _

lemma word_injective {n : ℕ} (m mask : Basis n) : Function.Injective (word m mask) := by
  intro x y h
  funext i
  have he := congrFun h ⟨n+n+i.val,by have := i.isLt; dsimp [width]; omega⟩
  simpa only [word_sample] using he

/-- Born events in the actual prepared register are exactly the b(n,m)-bit
fair events, retaining the original input, mask and all clean work wires. -/
lemma circuit_mass (n : ℕ) (m : Basis n) (P : Basis (width n)→Prop) :
    outcomeMass P ((programMatrix (circuit n)).mulVec
      (basisVector (word m (fun _ => false) (fun _ => false))))=
    outcomeMass (fun y => P (word m ((listMaskNet n).eval m)
      (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y)))
      (fairState (Nat.clog 2 (bitsValue m).toNat)) := by
  rw [circuit_state]
  exact outcomeMass_encode _ ((word_injective _ _).comp (padBits_injective _)) _ _

end ExactQuantumFactoring.ListSampler


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open Exactness RepeatedTrials

lemma tensorLayout_succ (q K : ℕ) (x : Fin (K+1)→Basis q) :
    tensorLayout q (K+1) x=Fin.append (x 0) (tensorLayout q K (Fin.tail x)) := rfl

lemma tensorProgram_entry {q : ℕ} (ops : List (Instruction q)) (K : ℕ)
    (x y : Fin K→Basis q) :
    (programMatrix (tensorProgram ops K)).mulVec (basisVector (tensorLayout q K x)) (tensorLayout q K y)=
      ∏ i, (programMatrix ops).mulVec (basisVector (x i)) (y i) := by
  induction K with
  | zero =>
    have he : x=y := Subsingleton.elim _ _
    subst y
    simp [tensorProgram,programMatrix,basisVector]
  | succ K ih =>
    rw [tensorProgram,tensorLayout_succ,tensorLayout_succ,parallelProgram_entry,ih,Fin.prod_univ_succ]
    rfl

/-- A literal repeated finite-gate program, not just a tensor-state idealization. -/
lemma tensorProgram_state {q : ℕ} (ops : List (Instruction q)) (K : ℕ) (x : Basis q) :
    (programMatrix (tensorProgram ops K)).mulVec (basisVector (tensorLayout q K (fun _ => x)))=
      encodeState (tensorLayout q K) (tensorState ((programMatrix ops).mulVec (basisVector x)) K) := by
  funext y
  obtain ⟨z,rfl⟩ := (tensorLayout q K).surjective y
  rw [tensorProgram_entry,encodeState_at _ (tensorLayout q K).injective]
  rfl

lemma tensorProgram_event {q : ℕ} (ops : List (Instruction q)) (K : ℕ) (x : Basis q)
    (P : (Fin K→Basis q)→Prop) :
    outcomeMass (P ∘ (tensorLayout q K).symm)
      ((programMatrix (tensorProgram ops K)).mulVec (basisVector (tensorLayout q K (fun _ => x))))=
      outcomeMass P (tensorState ((programMatrix ops).mulVec (basisVector x)) K) := by
  rw [tensorProgram_state,outcomeMass_encode _ (tensorLayout q K).injective]
  congr 1
  funext y
  simp

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListSlots
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open Exactness RepeatedTrials
namespace PhysicalListSlots

lemma sampleRead_word {n : ℕ} (m mask y : Basis n) : sampleRead (ListSampler.word m mask y)=y := by
  funext i
  exact ListSampler.word_sample _ _ _ _

lemma single_normalized {n : ℕ} (m : Basis n) :
    ∑ x,Complex.normSq ((programMatrix (ListSampler.circuit n)).mulVec
      (basisVector (ListSampler.word m (fun _ => false) (fun _ => false))) x)=1 := by
  have hh := ListSampler.circuit_mass n m (fun _ => True)
  simp only [outcomeMass,ite_true, if_true] at hh
  exact hh.trans (fairState_normalized _)

lemma ordinary_normalized {n : ℕ} (m : Basis n) : ∑ x,Complex.normSq (ordinaryState m x)=1 := by
  have hh := tensorProgram_event (ListSampler.circuit n) (n^5)
    (ListSampler.word m (fun _ => false) (fun _ => false)) (fun _ => True)
  change outcomeMass (fun _ => True) (ordinaryState m)=_ at hh
  simp only [outcomeMass,ite_true, if_true] at hh
  exact hh.trans (tensor_normalized _ _ (single_normalized m))

lemma ordinary_good_mass {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (hodd : Odd (bitsValue m).toNat) (p₀ : Component (bitsValue m).toNat) :
    outcomeMass (ListSlots.GoodOutput hm (bitsValue m).isLt p₀ ∘ ordinary) (ordinaryState m)=
      (Completion.listSuccess (bitsValue m).toNat n (n^5):ℝ) := by
  have he : ListSlots.GoodOutput hm (bitsValue m).isLt p₀ ∘ ordinary =
      (fun x : Fin (n^5)→Basis (ListSampler.width n) => ∃ i,
        FavorableBits hm (bitsValue m).isLt p₀ n (sampleRead (x i))) ∘ (tensorLayout _ (n^5)).symm := by
    funext x
    apply propext
    simp only [Function.comp_def,ListSlots.GoodOutput,ordinary,TransitionWords.read_encode,FavorableBits]
    exact ⟨fun ⟨i,u,h,hf⟩ => ⟨i,u,h.symm,hf⟩,fun ⟨i,u,h,hf⟩ => ⟨i,u,h.symm,hf⟩⟩
  rw [he,ordinaryState,ordinaryProgram,ordinaryZero,tensorProgram_event]
  rw [tensor_some_mass _ _ (fun x => FavorableBits hm (bitsValue m).isLt p₀ n (sampleRead x)) (single_normalized m)]
  rw [ListSampler.circuit_mass]
  have hs : (fun y => FavorableBits hm (bitsValue m).isLt p₀ n
      (sampleRead (ListSampler.word m ((listMaskNet n).eval m)
        (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y)))) =
      FavorableBits hm (bitsValue m).isLt p₀ (Nat.clog 2 (bitsValue m).toNat) := by
    funext y
    simp only [sampleRead_word,FavorableBits,padBits_value]
  rw [hs,favorableBits_mass hm (bitsValue m).isLt hodd p₀ (Nat.le_pow_clog (by decide) _)]
  simp only [Completion.listSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,Rat.cast_div,
    Rat.cast_natCast,Rat.cast_ofNat]

lemma fresh_normalized {n : ℕ} (m : Basis n) : ∑ r,Complex.normSq (fresh m r)=1 :=
  Completion.fresh_normalized _ _ _ _ (ordinary_normalized m)

lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀) :
    outcomeMass (passed m (by omega) p₀) (fresh m)=(Completion.target n:ℝ) := by
  have hl := Completion.listSuccess_lower hn hm (bitsValue m).isLt hodd p₀ p₁ hne
  have hu := Completion.listSuccess_le_one (by omega) (bitsValue m).isLt hodd p₀ (n^5)
  have hε : (1:ℚ)/(2:ℚ)^(2*n)<1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  apply Completion.passed_mass _ _ _ _ _ (ordinary_normalized m)
    (ordinary_good_mass m (by omega) hodd p₀)
    (Completion.listSuccess_at (bitsValue m).isLt.le _) (Completion.target_at n)
  · unfold Completion.coinBits Completion.transitionWidth; omega
  · linarith
  · exact hu
  · omega
  · exact Completion.target_pos (by omega)
  · exact Completion.target_le_ordinary (by omega) hl

lemma program_entry {n : ℕ} (m : Basis n) (r : Result n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero m))) (layout n r)=fresh m r :=
  Completion.program_entry _ _ _ _ _ _
lemma program_state {n : ℕ} (m : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero m)))=encodeState (layout n) (fresh m) := by
  funext x
  obtain ⟨r,rfl⟩ := (layout n).surjective x
  rw [program_entry,encodeState_at _ (layout n).injective]

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FixedSplit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open Exactness RepeatedTrials OrderTrial

namespace FixedSplit

lemma fresh_normalized {n : ℕ} (m : Basis n) : ∑ r,Complex.normSq (fresh m r)=1 := by
  apply RecordedHistory.append_normalized
  · exact PhysicalListSlots.fresh_normalized _
  · intro l
    exact productState_normalized _ (fun _ => OrderSlots.fresh_normalized _ _ _)

/-- One list transition followed by the K order/dummy transitions has exactly
z^(K+1) retained mass, unconditioned on the successful factor-data computation. -/
theorem passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀) :
    outcomeMass (passed m (by omega) p₀) (fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  change outcomeMass (fun r => PhysicalListSlots.passed m (by omega) p₀ r.1 ∧
    (fun l (rr : Fin (n^5)→OrderSlots.Result n) => ∀ i,OrderSlots.passed (bases l i) m (rr i)) r.1 r.2)
    (RecordedHistory.appendState _ _) = _
  rw [RecordedHistory.append_constant_mass _ _ _ _ ((Completion.target n:ℝ)^(n^5))
    (fun l _ => OrderSlots.all_passed_mass hn m hm (bases l))]
  rw [PhysicalListSlots.passed_mass hn m hm hodd p₀ p₁ hne]
  exact (mul_comm _ _).trans (pow_succ (Completion.target n:ℝ) (n^5)).symm

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalCompletionOutput
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open BooleanNetwork BitArithmetic
namespace Completion

lemma rareWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (rareWires q W t d).eval (layout q W t d r)=r.1 := by
  funext i
  simp only [rareWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left]
lemma ordinaryWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (ordinaryWires q W t d).eval (layout q W t d r)=r.2.1 := by
  funext i
  simp only [ordinaryWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left,Fin.append_right]
lemma guessWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (guessWires q W t d).eval (layout q W t d r)=r.2.2.1 := by
  funext i
  simp only [guessWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left,Fin.append_right]
lemma rareNet_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (rareNet q W t d).eval (layout q W t d r) 0=true ↔ rare r.1 := by
  rw [rareNet,equalOn_value,rareWires_eval,wordConstant_eval]
  simp only [BitVec.toNat_ofNat,Nat.zero_mod,rare]
lemma outputNet_eval {q W t d : ℕ} (ordinary : BooleanNetwork q W)
    (r : Raw (Basis q) W t d) :
    (outputNet ordinary t d).eval (layout q W t d r)=output ordinary.eval r := by
  rw [outputNet,wordMux_eval,guessWires_eval,eval_comp,ordinaryWires_eval,output]
  simp only [rareNet_eval r]
lemma zeros_eval (k m : ℕ) (x : Basis k) : (zeros k m).eval x=fun _ => false := by
  funext i
  simp only [zeros,eval_vector,eval_constant]
lemma initialNet_eval {k q W t d : ℕ} (ordinary : BooleanNetwork k q) (x : Basis k) :
    (initialNet ordinary W t d).eval x=
      layout q W t d ((fun _ => false),ordinary.eval x,(fun _ => false),(fun _ => false)) := by
  simp only [initialNet,eval_pair,zeros_eval,layout,productLayout_apply,Equiv.refl_apply]

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorWiring
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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
open BooleanNetwork

lemma tensorLayout_wire {q K : ℕ} (x : Fin K → Basis q) (i : Fin K) (j : Fin q) :
    tensorLayout q K x (tensorWire q K i j)=x i j := by
  induction K with
  | zero => exact Fin.elim0 i
  | succ K ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · change Fin.append (x 0) (tensorLayout q K (Fin.tail x)) (j.castAdd _) = _
      exact Fin.append_left _ _ _
    · change Fin.append (x 0) (tensorLayout q K (Fin.tail x))
        (Fin.natAdd q (tensorWire q K i j)) = _
      rw [Fin.append_right]
      exact ih (Fin.tail x) i

lemma tensorSelect_eval {q K : ℕ} (x : Fin K → Basis q) (i : Fin K) :
    (tensorSelect q K i).eval (tensorLayout q K x)=x i := by
  funext j
  exact tensorLayout_wire x i j
lemma tensorSelect_inverse {q K : ℕ} (x : Basis (tensorWidth q K)) (i : Fin K) :
    (tensorSelect q K i).eval x=(tensorLayout q K).symm x i := by
  obtain ⟨y,rfl⟩ := (tensorLayout q K).surjective x
  rw [tensorSelect_eval,Equiv.symm_apply_apply]

lemma tensorNetwork_eval {n q K : ℕ} (f : Fin K → BooleanNetwork n q) (x : Basis n) :
    (tensorNetwork f).eval x=tensorLayout q K (fun i => (f i).eval x) := by
  induction K with
  | zero => exact Subsingleton.elim _ _
  | succ K ih => rw [tensorNetwork,eval_pair,ih,tensorLayout_succ]; rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionNetworks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open BooleanNetwork
namespace TransitionWords

lemma encodeNet_eval {k n K : ℕ} (f : Fin K → BooleanNetwork k n) (x : Basis k) :
    (encodeNet f).eval x=encode (fun i => (f i).eval x) := by
  funext i
  rw [encodeNet,eval_vector]
  dsimp only [encode]
  split_ifs <;> simp only [eval_rewire,Function.comp_apply,eval_constant]

end TransitionWords
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListNetworks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open BooleanNetwork
namespace PhysicalListSlots

lemma sampleNet_eval {n : ℕ} (x : Basis (ListSampler.width n)) : (sampleNet n).eval x=sampleRead x := rfl

lemma ordinaryNet_eval {n : ℕ} (x : Basis (ordinaryWidth n)) : (ordinaryNet n).eval x=ordinary x := by
  change (TransitionWords.encodeNet _).eval x=TransitionWords.encode _
  rw [TransitionWords.encodeNet_eval]
  congr 1
  funext i
  rw [eval_comp,tensorSelect_inverse,sampleNet_eval]
lemma outputNet_eval {n : ℕ} (r : Result n) :
    (outputNet n).eval (layout n r)=output r := by
  change (Completion.outputNet _ _ _).eval (Completion.layout _ _ _ _ r)=_
  rw [Completion.outputNet_eval]
  unfold output Completion.output
  simp only [ordinaryNet_eval]
lemma singleZeroNet_eval {n : ℕ} (m : Basis n) :
    (singleZeroNet n).eval m=ListSampler.word m (fun _=>false) (fun _=>false) := by
  funext i
  rw [singleZeroNet,eval_vector]
  by_cases h : i.val<n
  · rw [dite_eq_left h,eval_bit]
    unfold ListSampler.word
    rw [dite_eq_left h]
  · rw [dite_eq_right h,eval_constant]
    unfold ListSampler.word
    split_ifs <;> rfl
lemma ordinaryZeroNet_eval {n : ℕ} (m : Basis n) : (ordinaryZeroNet n).eval m=ordinaryZero m := by
  rw [ordinaryZeroNet,tensorNetwork_eval,ordinaryZero]
  congr 1
  funext i
  exact singleZeroNet_eval m
lemma initialNet_eval {n : ℕ} (m : Basis n) : (initialNet n).eval m=layout n (zero m) := by
  rw [initialNet,Completion.initialNet_eval,ordinaryZeroNet_eval]
  rfl
lemma launch_state {n : ℕ} (m : Basis n) :
    (programMatrix (launch n)).mulVec (basisVector (packed (work n) m (fun _=>false)))=
      encodeState (fun r : Result n => packed (work n) m (layout n r)) (fresh m) := by
  rw [launch,preparedOracle_basis,initialNet_eval,program_state,encodeState_comp]
  rfl

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderSlots
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open Exactness RepeatedTrials OrderTrial
namespace OrderSlots

lemma ordinary_entry (n : ℕ) (a m : Basis n) (r : Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n) :
    (programMatrix (tensorProgram (rawProgram n (sampleExponent n) n) (n^5))).mulVec
      (basisVector (ordinaryLayout n (fun _ => rawZero (sampleExponent n) n a m)))
      (ordinaryLayout n r)=tensorState (rawState (sampleExponent n) n a m) (n^5) r := by
  change (programMatrix (tensorProgram (rawProgram n (sampleExponent n) n) (n^5))).mulVec
    (basisVector (tensorLayout _ _ (fun _ => rawLayout _ _ _ (rawZero _ _ a m))))
    (tensorLayout _ _ (fun i => rawLayout _ _ _ (r i)))=_
  rw [tensorProgram_entry]
  simp only [rawProgram_entry,tensorState]

/-- The completed order slot is a literal finite gate program on fresh qubits.
Neither the true order nor retrospective factor data occur in its preparation. -/
lemma program_entry (n : ℕ) (a m : Basis n) (r : Result n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero a m))) (layout n r)=fresh n a m r := by
  change (programMatrix (Completion.program _ _ _ _)).mulVec
    (basisVector (Completion.layout _ _ _ _
      ((fun _ => false),ordinaryLayout n (fun _ => rawZero (sampleExponent n) n a m),
        (fun _ => false),(fun _ => false))))
    (Completion.layout _ _ _ _ (r.1,ordinaryLayout n r.2.1,r.2.2))=_
  rw [Completion.program_entry]
  simp only [fresh,Completion.fresh,independentState]
  rw [ordinary_entry]

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderNetworks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open BooleanNetwork

lemma packed_append {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y=Fin.append (Fin.append x y) (fun _=>false) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · exact (packed_input x y j).trans (by simp)
    · exact (packed_target x y j).trans (by simp)
  · rw [packed_work x y _ (by simp),Fin.append_right]

namespace BooleanNetwork

lemma packNet_eval {k n m r : ℕ} (a : BooleanNetwork k n) (b : BooleanNetwork k m)
    (x : Basis k) : (packNet r a b).eval x=packed r (a.eval x) (b.eval x) := by
  rw [packNet,eval_pair,eval_pair,Completion.zeros_eval,packed_append]

end BooleanNetwork
lemma append_false (n m : ℕ) : Fin.append (fun _ : Fin n=>false) (fun _ : Fin m=>false)=fun _=>false := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp only [Fin.append_left,Fin.append_right]

namespace OrderSlots

lemma triangular_zero (b : ℕ) : Triangular.encode b ((fun _=>false),0)=fun _=>false := by
  have h := (basisResidue b).symm_apply_eq.mpr (basisResidue_zero b).symm
  dsimp [Triangular.encode]
  rw [h,packed_append]
  simp only [append_false]

lemma samplerZeroNet_eval {w b : ℕ} (a m : Basis w) :
    (samplerZeroNet w b).eval (Fin.append a m)=OrderSample.word a m (fun _=>false) (fun _=>false) := by
  rw [samplerZeroNet,packNet_eval,eval_pair,eval_select,Completion.zeros_eval,Completion.zeros_eval]
  simp only [Function.comp_id,OrderSample.word,OrderSample.inputWord,triangular_zero]
lemma rawZeroNet_eval {n : ℕ} (a m : Basis n) :
    (rawZeroNet n).eval (Fin.append a m)=
      OrderTrial.rawLayout n (sampleExponent n) n (OrderTrial.rawZero (sampleExponent n) n a m) := by
  rw [rawZeroNet,eval_pair,eval_pair,Completion.zeros_eval,Completion.zeros_eval,samplerZeroNet_eval]
  simp only [OrderTrial.rawLayout,productLayout_apply,Equiv.refl_apply,OrderTrial.rawZero,
    OrderTrial.guessLayout,OrderTrial.guessZero]
  simp only [append_false]
lemma ordinaryZeroNet_eval {n : ℕ} (a m : Basis n) :
    (ordinaryZeroNet n).eval (Fin.append a m)=ordinaryLayout n (fun _=>OrderTrial.rawZero (sampleExponent n) n a m) := by
  rw [ordinaryZeroNet,tensorNetwork_eval]
  simp only [rawZeroNet_eval,ordinaryLayout,Equiv.trans_apply]
  rfl
lemma initialNet_eval {n : ℕ} (a m : Basis n) :
    (initialNet n).eval (Fin.append a m)=layout n (zero a m) := by
  rw [initialNet,Completion.initialNet_eval,ordinaryZeroNet_eval]
  rfl

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open BooleanNetwork Exactness
namespace FixedSplit

lemma ordersProgram_state {n : ℕ} (m : Basis n) (aa : Fin (n^5)→Basis n) :
    (programMatrix (ordersProgram n)).mulVec
      (basisVector (ordersLayout n (fun i=>OrderSlots.zero (aa i) m)))=
    encodeState (ordersLayout n) (productState (fun i=>OrderSlots.fresh n (aa i) m)) := by
  funext x
  obtain ⟨y,rfl⟩ := (ordersLayout n).surjective x
  rw [encodeState_at _ (ordersLayout n).injective]
  change (programMatrix (tensorProgram (OrderSlots.program n) (n^5))).mulVec
    (basisVector (tensorLayout _ _ (fun i=>OrderSlots.layout n (OrderSlots.zero (aa i) m))))
    (tensorLayout _ _ (fun i=>OrderSlots.layout n (y i)))= _
  rw [tensorProgram_entry]
  simp only [OrderSlots.program_entry,productState]

lemma listWires_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (listWires n).eval (listEncoding m l)=PhysicalListSlots.layout n l := by
  exact packed_targetRegister m _
lemma modulusWires_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (modulusWires n).eval (listEncoding m l)=m := packed_first m _

lemma baseNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (l : PhysicalListSlots.Result n) :
    (baseNet i).eval (listEncoding m l)=bases l i := by
  rw [baseNet,eval_rewire,eval_comp,listWires_eval,PhysicalListSlots.outputNet_eval]
  rfl
lemma orderInitialNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (l : PhysicalListSlots.Result n) :
    (orderInitialNet i).eval (listEncoding m l)=OrderSlots.layout n (OrderSlots.zero (bases l i) m) := by
  rw [orderInitialNet,eval_comp,eval_pair,baseNet_eval,modulusWires_eval,OrderSlots.initialNet_eval]
lemma ordersInitialNet_eval {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) :
    (ordersInitialNet n).eval (listEncoding m l)=ordersLayout n (fun i=>OrderSlots.zero (bases l i) m) := by
  rw [ordersInitialNet,tensorNetwork_eval]
  simp only [orderInitialNet_eval]
  rfl

theorem program_state {n : ℕ} (m : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (zero m))=encodeState (encoding m) (fresh m) := by
  apply appendPrepared_state (listEncoding m) (ordersLayout n) (PhysicalListSlots.fresh m)
    (fun l=>productState (fun i=>OrderSlots.fresh n (bases l i) m))
    (PhysicalListSlots.launch n) (packed (PhysicalListSlots.work n) m (fun _=>false))
    (PhysicalListSlots.launch_state m) (ordersInitialNet n) le_rfl (ordersProgram n)
  intro l
  rw [ordersInitialNet_eval,ordersProgram_state]

lemma encoding_injective {n : ℕ} (m : Basis n) : Function.Injective (encoding m) := by
  intro a b hh
  have he : (listEncoding m a.1,ordersLayout n a.2)=(listEncoding m b.1,ordersLayout n b.2) :=
    packed_pair_injective _ _ _ hh
  apply Prod.ext
  · apply (PhysicalListSlots.layout n).injective
    have h : (m,PhysicalListSlots.layout n a.1)=(m,PhysicalListSlots.layout n b.1) :=
      packed_pair_injective _ _ _ (congrArg Prod.fst he)
    exact congrArg Prod.snd h
  · exact (ordersLayout n).injective (congrArg Prod.snd he)

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplitLaunch
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open BooleanNetwork

lemma preparedOracle_encode_dependent {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : α→β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (c : BooleanNetwork p q) (hc : c.net.count ≤ r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=
      encodeState (f a) (F a)) :
    (programMatrix (preparedOracle c hc ops)).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.1 ab.2))
      (RecordedHistory.appendState ψ F) := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,preparedOracle_basis,hlocal,encodeState_comp]
  unfold encodeState RecordedHistory.appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_smul]
  rfl

namespace FixedSplit

lemma initialNet_eval {n : ℕ} (m : Basis n) : (initialNet n).eval m=zero m := by
  simp only [initialNet,packNet_eval,eval_select,Function.comp_id,Completion.zeros_eval,zero]

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalMachine
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork RecordedHistory

lemma oracleOn_encode {α : Type*} [Fintype α] {n m r : ℕ}
    (e : α→Basis n) (ψ : α→ℂ) (c : BooleanNetwork n m) (hc : c.net.count ≤ r) :
    (programMatrix (oracleOn c hc)).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun a=>packed r (e a) (c.eval (e a))) ψ := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rfl

lemma appendPrepared_state_dependent {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : α→β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (A : List (Instruction p)) (v : Basis p)
    (hA : (programMatrix A).mulVec (basisVector v)=encodeState e ψ)
    (c : BooleanNetwork p q) (hc : c.net.count ≤ r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=
      encodeState (f a) (F a)) :
    (programMatrix (appendPrepared A c hc ops)).mulVec
      (basisVector (packed r v (fun _=>false)))=
    encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.1 ab.2)) (appendState ψ F) := by
  rw [appendPrepared,programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hA,encodeState_comp]
  exact preparedOracle_encode_dependent e f ψ F c hc ops hlocal

namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

lemma current_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.currentNet t).eval (M.encoded x t h)=M.config x t h := by
  cases t with
  | zero=>rfl
  | succ t=>exact packed_targetRegister _ _
lemma initNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.initNet t).eval (M.encoded x t h)=FixedSplit.zero (M.query.eval (M.config x t h)) := by
  rw [initNet,eval_comp,FixedSplit.initialNet_eval,eval_comp,M.current_encoded]
lemma updateNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : FixedSplit.Raw n) :
    (M.updateNet t).eval (packed M.initWork (M.encoded x t h)
      (FixedSplit.encoding (M.query.eval (M.config x t h)) r))=M.next (M.config x t h) r := by
  rw [updateNet,eval_comp,eval_pair,eval_comp,eval_select,packed_first,
    M.current_encoded,eval_select,packed_targetRegister]
  rfl

/-- The actual adaptive quantum history, not a table of independent
counterfactual branches. Every update and next modulus comes from this run. -/
theorem program_state (x : Basis c) (t : ℕ) :
    (programMatrix (M.program t)).mulVec (basisVector (M.initial t x))=
      encodeState (M.encoded x t) (M.state x t) := by
  induction t with
  | zero=>
    simp only [program,initial,programMatrix,state,encoded,encodeState]
    simp [Trace]
  | succ t ih=>
    have hp := appendPrepared_state_dependent (M.encoded x t)
      (fun h r=>FixedSplit.encoding (M.query.eval (M.config x t h)) r) (M.state x t)
      (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h)))
      (M.program t) (M.initial t x) ih (M.initNet t) (M.initNet_count t).le
      (FixedSplit.program n) (by
        intro h
        rw [M.initNet_encoded,FixedSplit.program_state])
    dsimp only [program,initial,width]
    rw [programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hp,encodeState_comp]
    simp only [Function.comp_def]
    rw [oracleOn_encode (fun ab : Trace n t×FixedSplit.Raw n=>
      packed M.initWork (M.encoded x t ab.1) (FixedSplit.encoding
        (M.query.eval (M.config x t ab.1)) ab.2))
      (appendState (M.state x t) (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h))))
      (M.updateNet t) (M.updateNet_count t).le]
    congr 1
    funext h
    rw [M.updateNet_encoded]
    rfl

lemma encoded_injective (x : Basis c) (t : ℕ) : Function.Injective (M.encoded x t) := by
  induction t with
  | zero=>intro a b _;exact @Subsingleton.elim Unit inferInstance a b
  | succ t ih=>
    rintro ⟨a,r⟩ ⟨b,s⟩ he
    dsimp only [encoded] at he
    have hinner := congrArg (fun z=>z ∘ firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork) he
    simp only [packed_first] at hinner
    have he' := congrArg (fun z=>z ∘ firstRegister (M.width t) (FixedSplit.width n) M.initWork) hinner
    simp only [packed_first] at he'
    have hab : a=b := ih he' 
    subst b
    have hr := congrArg (fun z=>z ∘ targetRegister (M.width t) (FixedSplit.width n) M.initWork) hinner
    simp only [packed_targetRegister] at hr
    have hrs : r=s := FixedSplit.encoding_injective _ hr
    subst s
    rfl

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_HardCofactor
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

/-- The randomized splitter is invoked only after the prime and perfect-power
cases. Such an input has two genuinely different prime-power components. -/
lemma exists_distinct_components {m : ℕ} (hm : 2 ≤ m) (hc : ¬m.Prime)
    (hp : ¬Primality.PerfectPower m) : ∃ p₀ p₁ : Component m, p₁≠p₀ := by
  obtain ⟨p,hp₀⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < m)
  by_cases hh : ∀ q∈m.primeFactors,q=p
  · have hs : m.factorization.support ⊆ {p} := by
      intro q hq
      rw [Nat.support_factorization] at hq
      exact Finset.mem_singleton.mpr (hh q hq)
    have hpow : p^(m.factorization p)=m := by
      have he := m.factorization.prod_of_support_subset hs (fun p e => p^e)
        (by intro i _; simp)
      simpa only [Finset.prod_singleton] using he.symm.trans (Nat.prod_factorization_pow_eq_self (by omega))
    have hprime := (Nat.mem_primeFactors.mp hp₀).1
    have hexp : m.factorization p≠0 := by
      apply Finsupp.mem_support_iff.mp
      simpa only [Nat.support_factorization] using hp₀
    by_cases he : m.factorization p=1
    · rw [he,pow_one] at hpow
      exact False.elim (hc (hpow ▸ hprime))
    · exact False.elim (hp ⟨p,m.factorization p,hprime.two_le,by omega,hpow⟩)
  · push Not at hh
    obtain ⟨q,hq,hne⟩ := hh
    exact ⟨⟨p,hp₀⟩,⟨q,hq⟩,fun h => hne (congrArg Subtype.val h)⟩

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_UniversalSplit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open Exactness RepeatedTrials OrderTrial
namespace UniversalSplit

lemma secondComponent {m : ℕ} (hm : Hard m) :
    ∃ p₁ : Component m,p₁≠firstComponent hm.1 := by
  classical
  obtain ⟨a,b,hne⟩ := exists_distinct_components hm.1 hm.2.1 hm.2.2.2
  by_cases ha : a=firstComponent hm.1
  · exact ⟨b,by simpa only [←ha] using hne⟩
  · exact ⟨a,ha⟩

lemma dummy_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) :
    outcomeMass dummy (FixedSplit.fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  change outcomeMass (fun r : Raw n => dummyList r.1 ∧ (fun (_ : PhysicalListSlots.Result n)
    (rr : Fin (n^5)→OrderSlots.Result n)=>∀ i,dummyOrder (rr i)) r.1 r.2)
      (RecordedHistory.appendState _ _) = _
  have ho : ∀ l : PhysicalListSlots.Result n, outcomeMass
      (fun rr : Fin (n^5)→OrderSlots.Result n => ∀ i,dummyOrder (rr i))
      (productState (fun i=>OrderSlots.fresh n (FixedSplit.bases l i) m))=
        (Completion.target n:ℝ)^(n^5) := by
    intro l
    rw [productState_all_mass]
    have he : ∀ i : Fin (n^5),outcomeMass dummyOrder
        (OrderSlots.fresh n (FixedSplit.bases l i) m)=(Completion.target n:ℝ) := by
      intro i
      exact Completion.dummy_passed_mass _ n _ hn
        (tensor_normalized _ _ (raw_normalized _ _ _ _)) (natBasis _ 0)
    simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [RecordedHistory.append_constant_mass (PhysicalListSlots.fresh m)
    (fun l=>productState (fun i=>OrderSlots.fresh n (FixedSplit.bases l i) m))
    dummyList (fun _ rr=>∀ i,dummyOrder (rr i)) ((Completion.target n:ℝ)^(n^5)) (fun l _=>ho l)]
  have hl := Completion.dummy_passed_mass (PhysicalListSlots.ordinaryState m) n (n*n^5)
    hn (PhysicalListSlots.ordinary_normalized m) (natBasis _ 0)
  change outcomeMass dummyList (PhysicalListSlots.fresh m)=(Completion.target n:ℝ) at hl
  rw [hl]
  exact (mul_comm _ _).trans (pow_succ (Completion.target n:ℝ) (n^5)).symm

lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) :
    outcomeMass (passed m) (FixedSplit.fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  classical
  unfold passed
  split_ifs with h
  · obtain ⟨p₁,hne⟩ := secondComponent h
    exact FixedSplit.passed_mass hn m h.1 h.2.2.1 (firstComponent h.1) p₁ hne
  · exact dummy_mass hn m

end UniversalSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalMachineMass
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype
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
open Exactness RecordedHistory
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

lemma state_normalized (x : Basis c) (t : ℕ) :
    ∑ h,Complex.normSq (M.state x t h)=1 := by
  induction t with
  | zero=>simp [state,Trace]
  | succ t ih=>
    change ∑ h,Complex.normSq (appendState (M.state x t)
      (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h))) h)=1
    exact append_normalized _ _ ih (fun h=>FixedSplit.fresh_normalized _)

/-- Exact physical-history probability for a clocked network controller. This
is unconditional in its update network and retains all quantum scratch. -/
theorem passed_mass (hn : 128≤n) (x : Basis c) (t : ℕ) :
    outcomeMass (M.passed x t) (M.state x t)=
      ((Completion.target n:ℝ)^(n^5+1))^t := by
  induction t with
  | zero=>simp [outcomeMass,passed,state,Trace]
  | succ t ih=>
    change outcomeMass (fun h : Trace n t×FixedSplit.Raw n=>M.passed x t h.1 ∧
      UniversalSplit.passed (M.query.eval (M.config x t h.1)) h.2)
      (appendState (M.state x t) (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h))))=_
    rw [append_constant_mass (M.state x t)
      (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h))) (M.passed x t)
      (fun h=>UniversalSplit.passed (M.query.eval (M.config x t h)))
      ((Completion.target n:ℝ)^(n^5+1))
      (fun h _=>UniversalSplit.passed_mass hn (M.query.eval (M.config x t h))),ih]
    exact (pow_succ ((Completion.target n:ℝ)^(n^5+1)) t).symm

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MachineInitialization
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

lemma initialNet_eval (t : ℕ) (x : Basis c) :
    (M.initialNet t).eval x=M.initial t x := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    rw [initialNet,packNet_eval,packNet_eval,Completion.zeros_eval,Completion.zeros_eval,ih]
    rfl

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController

namespace NodeCircuit

@[simp] lemma top_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (top s w).eval (pack xs d)=xs.head?.getD (fun _=>false) := by
  rw [top,eval_comp,pending_pack,blockNet_eval,block_stackEncoding]
  cases xs <;> rfl

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.cyclicMod_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork BitArithmetic

namespace BitArithmetic

@[simp] lemma liftInput_eval {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) (x : Basis l) :
    (liftInput a f).eval x=a.eval (x∘f) := by simp [liftInput,eval_comp]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalNodeKernel
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype
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
open BooleanNetwork
namespace NodeKernel
lemma initialNet_eval {n : ℕ} (q : Basis n) : (initialNet n).eval q=zero q := by
  rw [initialNet,PhysicalNode.runInitial,eval_comp,SplitMachine.initialNet_eval]
  rfl
lemma program_state {n : ℕ} (q : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (zero q))=encodeState (encoding q) (fresh q) :=
  (PhysicalNode.machine n (2*n)).program_state (start q) (2*n)
lemma encoding_injective {n : ℕ} (q : Basis n) : Function.Injective (encoding q) :=
  (PhysicalNode.machine n (2*n)).encoded_injective (start q) (2*n)
lemma fresh_normalized {n : ℕ} (q : Basis n) : ∑ r,Complex.normSq (fresh q r)=1 :=
  (PhysicalNode.machine n (2*n)).state_normalized (start q) (2*n)
lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (q : Basis n) :
    Exactness.outcomeMass (passed q) (fresh q)=
      ((Completion.target n:ℝ)^(n^5+1))^(2*n) :=
  (PhysicalNode.machine n (2*n)).passed_mass hn (start q) (2*n)
end NodeKernel
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeMachine
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open BooleanNetwork RecordedHistory

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma current_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.currentNet t).eval (M.encoded x t h)=M.config x t h := by
  cases t with
  | zero=>rfl
  | succ t=>exact packed_targetRegister _ _
lemma initNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.initNet t).eval (M.encoded x t h)=NodeKernel.zero (M.query.eval (M.config x t h)) := by
  rw [initNet,eval_comp,NodeKernel.initialNet_eval,eval_comp,M.current_encoded]
lemma updateNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.updateNet t).eval (packed M.initWork (M.encoded x t h)
      (NodeKernel.encoding (M.query.eval (M.config x t h)) r))=M.next (M.config x t h) r := by
  rw [updateNet,eval_comp,eval_pair,eval_comp,eval_select,packed_first,
    M.current_encoded,eval_select,packed_targetRegister]
  rfl

/-- The actual adaptive quantum history, not a table of independent
counterfactual branches. Every update and next modulus comes from this run. -/
theorem program_state (x : Basis c) (t : ℕ) :
    (programMatrix (M.program t)).mulVec (basisVector (M.initial t x))=
      encodeState (M.encoded x t) (M.state x t) := by
  induction t with
  | zero=>
    simp only [program,initial,programMatrix,state,encoded,encodeState]
    simp [Trace]
  | succ t ih=>
    have hp := appendPrepared_state_dependent (M.encoded x t)
      (fun h r=>NodeKernel.encoding (M.query.eval (M.config x t h)) r) (M.state x t)
      (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h)))
      (M.program t) (M.initial t x) ih (M.initNet t) (M.initNet_count t).le
      (NodeKernel.program n) (by
        intro h
        rw [M.initNet_encoded,NodeKernel.program_state])
    dsimp only [program,initial,width]
    rw [programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hp,encodeState_comp]
    simp only [Function.comp_def]
    rw [oracleOn_encode (fun ab : Trace n t×NodeKernel.Raw n=>
      packed M.initWork (M.encoded x t ab.1) (NodeKernel.encoding
        (M.query.eval (M.config x t ab.1)) ab.2))
      (appendState (M.state x t) (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))))
      (M.updateNet t) (M.updateNet_count t).le]
    congr 1
    funext h
    rw [M.updateNet_encoded]
    rfl

lemma encoded_injective (x : Basis c) (t : ℕ) : Function.Injective (M.encoded x t) := by
  induction t with
  | zero=>intro a b _;exact @Subsingleton.elim Unit inferInstance a b
  | succ t ih=>
    rintro ⟨a,r⟩ ⟨b,s⟩ he
    dsimp only [encoded] at he
    have hinner := congrArg (fun z=>z ∘ firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) he
    simp only [packed_first] at hinner
    have he' := congrArg (fun z=>z ∘ firstRegister (M.width t) (NodeKernel.width n) M.initWork) hinner
    simp only [packed_first] at he'
    have hab : a=b := ih he' 
    subst b
    have hr := congrArg (fun z=>z ∘ targetRegister (M.width t) (NodeKernel.width n) M.initWork) hinner
    simp only [packed_targetRegister] at hr
    have hrs : r=s := NodeKernel.encoding_injective _ hr
    subst s
    rfl

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeMass
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open Exactness RecordedHistory
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma state_normalized (x : Basis c) (t : ℕ) :
    ∑ h,Complex.normSq (M.state x t h)=1 := by
  induction t with
  | zero=>simp [state,Trace]
  | succ t ih=>
    change ∑ h,Complex.normSq (appendState (M.state x t)
      (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))) h)=1
    exact append_normalized _ _ ih (fun h=>NodeKernel.fresh_normalized _)

/-- Exact physical-history probability for a clocked network controller. This
is unconditional in its update network and retains all quantum scratch. -/
theorem passed_mass (hn : 128≤n) (x : Basis c) (t : ℕ) :
    outcomeMass (M.passed x t) (M.state x t)=
      (((Completion.target n:ℝ)^(n^5+1))^(2*n))^t := by
  induction t with
  | zero=>simp [outcomeMass,passed,state,Trace]
  | succ t ih=>
    change outcomeMass (fun h : Trace n t×NodeKernel.Raw n=>M.passed x t h.1 ∧
      NodeKernel.passed (M.query.eval (M.config x t h.1)) h.2)
      (appendState (M.state x t) (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))))=_
    rw [append_constant_mass (M.state x t)
      (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))) (M.passed x t)
      (fun h=>NodeKernel.passed (M.query.eval (M.config x t h)))
      (((Completion.target n:ℝ)^(n^5+1))^(2*n))
      (fun h _=>NodeKernel.passed_mass hn (M.query.eval (M.config x t h))),ih]
    exact (pow_succ (((Completion.target n:ℝ)^(n^5+1))^(2*n)) t).symm

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorList
attribute [-instance] _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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


namespace ExactQuantumFactoring.BitArithmetic.SortedWords

lemma layout_ofFn (w r : ℕ) (f : Fin r→Basis w) :
    layout w r (List.ofFn f)=tensorLayout w r f := by
  induction r with
  | zero=>rfl
  | succ r ih=>
    rw [List.ofFn_succ,layout,tensorLayout_succ]
    simp only [List.head?_cons,Option.getD_some,List.tail_cons]
    rw [ih]
    rfl

end ExactQuantumFactoring.BitArithmetic.SortedWords


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeQueue
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
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

lemma query_encoding (n : ℕ) (a : Basis n) (xs : List (Basis n)) :
    (query n).eval (stackEncoding (capacity n) n (a::xs))=a := by
  rw [query,blockNet_eval,block_stackEncoding]
  rfl

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeHistoryAccess
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open BooleanNetwork
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma previousNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.previousNet t).eval (M.encoded x (t+1) (h,r))=M.encoded x t h := by
  rw [previousNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (NodeKernel.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) ∘
      firstRegister (M.width t) (NodeKernel.width n) M.initWork=_
  rw [packed_first,packed_first]
lemma lastNodeNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.lastNodeNet t).eval (M.encoded x (t+1) (h,r))=
      NodeKernel.encoding (M.query.eval (M.config x t h)) r := by
  rw [lastNodeNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (NodeKernel.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) ∘
      targetRegister (M.width t) (NodeKernel.width n) M.initWork=_
  rw [packed_first,packed_targetRegister]

lemma firstNodeNet_encoded (x : Basis c) (t : ℕ) (h : Trace n (t+1)) :
    (M.firstNodeNet t).eval (M.encoded x (t+1) h)=NodeKernel.encoding (M.query.eval x) (firstRaw t h) := by
  induction t with
  | zero=>exact M.lastNodeNet_encoded x 0 h.1 h.2
  | succ t ih=>
    rw [firstNodeNet,eval_comp,M.previousNet_encoded,ih]
    rfl

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeInitialization
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open BooleanNetwork
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma initialNet_eval (t : ℕ) (x : Basis c) :
    (M.initialNet t).eval x=M.initial t x := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    rw [initialNet,packNet_eval,packNet_eval,Completion.zeros_eval,Completion.zeros_eval,ih]
    rfl

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeLaunch
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
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

lemma startNet_eval (n : ℕ) (a : Basis n) :
    (startNet n).eval a=stackEncoding (capacity n) n [a] := by
  rw [startNet,stackPush_encoding _ _ _ [] (by rw [Completion.zeros_eval];rfl)]
  rfl
lemma startNet_nat {n N : ℕ} : (startNet n).eval (natBasis n N)=initialQueue n N := by
  rw [startNet_eval]
  rfl
lemma initialNet_eval {n N : ℕ} : (initialNet n).eval (natBasis n N)=
    (machine n).initial (steps n) (initialQueue n N) := by
  rw [initialNet,eval_comp,NodeMachine.initialNet_eval,startNet_nat]

lemma query_initial (n N : ℕ) : (query n).eval (initialQueue n N)=natBasis n N :=
  query_encoding n (natBasis n N) []

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeVerifiedCircuit
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
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

lemma nodeWords_length (n : ℕ) (z : Basis (NodeKernel.width n)) : (nodeWords n z).length=n :=
  List.length_ofFn

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveTree
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
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree
namespace PhysicalTree

/-- Exact accepted mass, after the actual complete-data checks. This is still
an event theorem: using it as a physical phase flag requires the missing fully
assembled retrospective Boolean network, rather than an arbitrary predicate. -/
theorem accepted_mass {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n) :
    Exactness.outcomeMass (accepted (n:=n) (N:=N) (by omega))
      ((machine n).state (initialQueue n N) (2*n^2))=
        (((Completion.target n:ℝ)^(n^5+1))^(2*n))^(2*n^2) := by
  have he : accepted (n:=n) (N:=N) (by omega)=
      (machine n).passed (initialQueue n N) (2*n^2) := by
    funext r
    exact propext (accepted_iff_passed hn hN hb r)
  rw [he]
  exact (machine n).passed_mass hn _ _
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QuarterPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending_pack _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_eval _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_cons _root_.OAI.ExactQuantumFactoring.PhysicalNode.values_nil
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
open Exactness OrderTrial

lemma knownProbability_at (n : ℕ) : DyadicAt (n^11) (knownProbability n) := by
  have hd : DyadicAt n (1-1/(2:ℚ)^n) := (DyadicAt.integer n 1).sub ⟨1,by simp⟩
  convert hd.pow (n^10) using 1 <;> first | rfl | ring

namespace Quarter

lemma retention_at (n : ℕ) : DyadicAt (D n) (retention n) := by
  apply (show DyadicAt (n*n+2) (retention n) from ⟨_,rfl⟩).mono
  unfold D Completion.coinBits
  omega
lemma guessRetention_at (n : ℕ) : DyadicAt (D n) (guessRetention n) := by
  have hC : DyadicAt (n*n+2) (retention n) := ⟨_,rfl⟩
  have hP := (knownProbability_at n).mul hC
  have hhalf : DyadicAt 1 (1/2) := ⟨1,by norm_num⟩
  have hprod := hP.mul hhalf
  have hprod' : DyadicAt (D n) (knownProbability n*retention n/2) := by
    simpa only [div_eq_mul_inv,one_div,one_mul] using hprod.mono (l:=D n) (by unfold D Completion.coinBits; omega)
  have hquarter : DyadicAt (D n) (1/4) :=
    (show DyadicAt 2 (1/4) from ⟨1,by norm_num⟩).mono (by unfold D Completion.coinBits; omega)
  have h := (hquarter.sub hprod').int_mul (2^(n*n+1))
  simpa only [guessRetention,quarterRemainder,retention,Int.cast_pow,Int.cast_ofNat] using h

theorem passed_mass {α : Type*} [Fintype α] {N n : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (ψ : α→ℂ) (success : α→Prop) (hψ : ∑ x,Complex.normSq (ψ x)=1)
    (hs : outcomeMass success ψ=(knownProbability n:ℝ)) :
    outcomeMass (passed N success) (fresh ψ n)=1/4 := by
  obtain ⟨hp₀,hp₁⟩ := knownProbability_bounds hn
  obtain ⟨hC₀,hC₁,hG₀,hG₁⟩ := quarter_retention_bounds (n*n) hp₀ hp₁
  have hC := dyadic_fair_threshold (retention_at n) hC₀ hC₁
  have hG := dyadic_fair_threshold (guessRetention_at n) hG₀ (hG₁.le.trans (by norm_num))
  have hr : outcomeMass (fun b : Basis 1 => Completion.rare b) (fairState 1)=1/2 := by
    simpa only [Completion.rare,pow_one] using (fair_value_mass (by norm_num : 0<2^1))
  have hnr : outcomeMass (fun b : Basis 1 => ¬Completion.rare b) (fairState 1)=1/2 := by
    rw [RepeatedTrials.mass_compl _ _ (fair_normalized 1),hr]
    norm_num
  have ho : outcomeMass (ordinaryPass (n:=n) success) (fresh ψ n)=
      (1/2)*(knownProbability n:ℝ)*(retention n:ℝ) := by
    change outcomeMass (fun r : Raw α n => ¬Completion.rare r.1 ∧
      (success r.2.1 ∧ Completion.threshold (retention n) r.2.2.2))
      (Completion.fresh ψ (n*n) 1 (n^11))=_
    rw [Completion.fresh,independent_mass (fairState 1)
      (independentState ψ (independentState (fairState (n*n)) (fairState (D n))))
      (fun b => ¬Completion.rare b) (fun r => success r.1 ∧ Completion.threshold (retention n) r.2.2),
      independent_mass ψ (independentState (fairState (n*n)) (fairState (D n)))
      success (fun r => Completion.threshold (retention n) r.2),
      independent_mass_right _ _ _ (fair_normalized (n*n))]
    rw [hnr,hs]
    rw [show outcomeMass (Completion.threshold (D:=D n) (retention n)) (fairState (D n))=
      (retention n:ℝ) from hC]
    ring
  have hg : outcomeMass (guessPass (n:=n) N) (fresh ψ n)=
      (1/2)*(1/(2:ℝ)^(n*n))*(guessRetention n:ℝ) := by
    change outcomeMass (fun r : Raw α n => Completion.rare r.1 ∧
      (CorrectEncoding N n (guessWords n r.2.2.1) ∧ Completion.threshold (guessRetention n) r.2.2.2))
      (Completion.fresh ψ (n*n) 1 (n^11))=_
    rw [Completion.fresh,independent_mass (fairState 1)
      (independentState ψ (independentState (fairState (n*n)) (fairState (D n))))
      Completion.rare (fun r => CorrectEncoding N n (guessWords n r.2.1) ∧
        Completion.threshold (guessRetention n) r.2.2),
      independent_mass_right ψ (independentState (fairState (n*n)) (fairState (D n)))
      (fun r => CorrectEncoding N n (guessWords n r.1) ∧ Completion.threshold (guessRetention n) r.2) hψ,
      independent_mass (fairState (n*n)) (fairState (D n))
      (fun x => CorrectEncoding N n (guessWords n x)) (Completion.threshold (guessRetention n)),
      hr,fair_guess_mass hN hb]
    rw [show outcomeMass (Completion.threshold (D:=D n) (guessRetention n)) (fairState (D n))=
      (guessRetention n:ℝ) from hG]
    simp only [one_div,inv_pow]
    ring
  change outcomeMass (fun r => ordinaryPass success r ∨ guessPass N r) (fresh ψ n)=1/4
  rw [outcomeMass_disjoint_or _ _ _ (by intro r h; exact h.1.1 h.2.1),ho,hg]
  have h := congrArg (fun q : ℚ => (q:ℝ)) (quarter_mass (n*n) (knownProbability n))
  push_cast at h
  simpa only [retention,guessRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using h

/-- The flagged output always has the same canonical root encoding. -/
theorem passed_correct {α : Type*} {N n : ℕ} (ordinary : α→Basis (n*n)) (success : α→Prop)
    (hsound : ∀ a,success a → CorrectEncoding N n (guessWords n (ordinary a)))
    (r : Raw α n) (h : passed N success r) :
    CorrectEncoding N n (guessWords n (Completion.output ordinary r)) := by
  rcases h with h | h
  · simpa only [Completion.output,ite_eq_right h.1] using hsound r.2.1 h.2.1
  · simpa only [Completion.output,ite_eq_left h.1] using h.2.1

end Quarter
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreePadding
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
open Exactness RepeatedTrials
namespace PhysicalTree

lemma slots_le {n : ℕ} (hn : 128≤n) : slots n≤n^10 := by
  have hp : 1≤n^5 := Nat.one_le_pow _ _ (by omega)
  have h₂ : 8≤n^2 := by nlinarith
  calc
    slots n ≤ ((2*n^5)*(2*n))*(2*n^2) := by
      unfold slots
      gcongr
      omega
    _ = 8*n^8 := by ring
    _ ≤ n^2*n^8 := Nat.mul_le_mul_right _ h₂
    _ = n^10 := by ring

lemma slots_add_padding {n : ℕ} (hn : 128≤n) : slots n+padding n=n^10 :=
  Nat.add_sub_of_le (slots_le hn)

lemma padProgram_state (n : ℕ) :
    (programMatrix (padProgram n)).mulVec
      (basisVector (tensorLayout n (padding n) (fun _ _=>false)))=
    encodeState (tensorLayout n (padding n)) (padState n) := by
  rw [padProgram,tensorProgram_state,hadamards_zero]
  rfl

lemma pad_normalized (n : ℕ) : ∑ x,Complex.normSq (padState n x)=1 :=
  tensor_normalized _ _ (fairState_normalized n)

lemma pad_mass (n : ℕ) : outcomeMass (padPassed (n:=n)) (padState n)=
    (Completion.target n:ℝ)^(padding n) := by
  change outcomeMass (fun x : PadRaw n=>∀ i,¬Completion.rare (x i))
    (tensorState (fairState n) (padding n))=_
  rw [tensor_all_mass (fairState n) (padding n) (fun y=>¬Completion.rare y),mass_compl _ _ (fairState_normalized n)]
  have hr : outcomeMass (fun x : Basis n=>Completion.rare x) (fairState n)=
      1/(2:ℝ)^n := by
    exact fair_value_mass (by positivity)
  rw [hr]
  simp only [Completion.target,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat]

lemma padded_normalized (n N : ℕ) : ∑ x,Complex.normSq (paddedState n N x)=1 :=
by
  change ∑ x : NodeMachine.Trace n (2*n^2)×PadRaw n,
    Complex.normSq (independentState ((machine n).state (initialQueue n N) (2*n^2))
      (padState n) x)=1
  simp only [independentState,Complex.normSq_mul,Fintype.sum_prod_type]
  simp_rw [←Finset.mul_sum,pad_normalized,mul_one]
  exact (machine n).state_normalized _ _

/-- Exact manuscript P_n, now for the actual chronological physical tree,
retrospective checks on its own data log, and literal nonzero-word padding. -/
theorem padded_mass {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (paddedAccepted (n:=n) (N:=N) (by omega)) (paddedState n N)=
      (knownProbability n:ℝ) := by
  change outcomeMass (fun x : PaddedRaw n => accepted (N:=N) (by omega) x.1 ∧
    padPassed x.2) (independentState ((machine n).state (initialQueue n N) (2*n^2))
      (padState n))=_
  rw [independent_mass,accepted_mass hn hN hb,pad_mass,
    ←pow_mul,←pow_mul,←pow_add]
  have he : (n^5+1)*(2*n*(2*n^2))+padding n=n^10 := by
    simpa only [slots,Nat.mul_assoc] using slots_add_padding hn
  rw [he]
  simp only [knownProbability,Completion.target,Rat.cast_pow,Rat.cast_sub,
    Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreePhysicalPreparation
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
open BooleanNetwork BitArithmetic Exactness OrderTrial

lemma parallelProgram_encoded_state {α β : Type*} [Fintype α] [Fintype β] {p q : ℕ}
    (A : List (Instruction p)) (B : List (Instruction q)) (x : Basis p) (y : Basis q)
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (χ : β→ℂ)
    (hA : (programMatrix A).mulVec (basisVector x)=encodeState e ψ)
    (hB : (programMatrix B).mulVec (basisVector y)=encodeState f χ) :
    (programMatrix (parallelProgram A B)).mulVec (basisVector (Fin.append x y))=
      encodeState (fun ab : α×β=>Fin.append (e ab.1) (f ab.2)) (independentState ψ χ) := by
  rw [parallelProgram,programMatrix_append,←Matrix.mulVec_mulVec,leftProgram_basis,hA,
    encodeState_comp,encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,rightProgram_basis,hB,encodeState_comp,Function.comp_def]
  exact (encode_independent e f ψ χ).symm

namespace PhysicalTree

lemma launchProgram_state (n N : ℕ) :
    (programMatrix (launchProgram n)).mulVec (basisVector (launchZero n N))=
      encodeState (launchEncoding n N) ((machine n).state (initialQueue n N) (steps n)) := by
  rw [launchProgram,launchZero,preparedOracle_basis,initialNet_eval,
    NodeMachine.program_state,encodeState_comp]
  rfl
lemma launchEncoding_injective (n N : ℕ) : Function.Injective (launchEncoding n N) := by
  intro a b h
  apply (machine n).encoded_injective (initialQueue n N) (steps n)
  have he:=congrArg (fun x=>x ∘ targetRegister n (width n) (launchWork n)) h
  simpa only [launchEncoding,packed_targetRegister] using he

lemma paddedProgram_state (n N : ℕ) :
    (programMatrix (paddedProgram n)).mulVec (basisVector (paddedZero n N))=
      encodeState (paddedEncoding n N) (paddedState n N) :=
  parallelProgram_encoded_state _ _ _ _ _ _ _ _ (launchProgram_state n N) (padProgram_state n)

lemma paddedEncoding_injective (n N : ℕ) : Function.Injective (paddedEncoding n N) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have he : (launchEncoding n N a,tensorLayout n (padding n) b)=
      (launchEncoding n N c,tensorLayout n (padding n) d) := (appendEquiv _ _).injective h
  have hac:=launchEncoding_injective n N (congrArg Prod.fst he)
  have hbd:=(tensorLayout n (padding n)).injective (congrArg Prod.snd he)
  cases hac
  cases hbd
  rfl

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeQuarterPhysical
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
open BooleanNetwork Exactness

lemma hadamards_zero_encoded (q : ℕ) :
    (programMatrix (hadamardPrefix q q le_rfl)).mulVec (basisVector (fun _=>false))=
      encodeState id (fairState q) := by
  funext x
  rw [hadamards_zero]
  exact (encodeState_at id Function.injective_id (fairState q) x).symm

namespace Completion

lemma extendEncoding_injective {α : Type*} {q : ℕ} (e : α→Basis q)
    (he : Function.Injective e) (W t d : ℕ) : Function.Injective (extendEncoding e W t d) := by
  rintro ⟨a,b,c,h⟩ ⟨a',b',c',h'⟩ hh
  have H : (a,Fin.append (e b) (Fin.append c h))=
      (a',Fin.append (e b') (Fin.append c' h')) :=
    (appendEquiv t (q+(W+coinBits W t d))).injective hh
  have ha:=congrArg Prod.fst H
  have H' : (e b,Fin.append c h)=(e b',Fin.append c' h') :=
    (appendEquiv q (W+coinBits W t d)).injective (congrArg Prod.snd H)
  have hb:=he (congrArg Prod.fst H')
  have H'' : (c,h)=(c',h') :=
    (appendEquiv W (coinBits W t d)).injective (congrArg Prod.snd H')
  have hc:=congrArg Prod.fst H''
  have hd:=congrArg Prod.snd H''
  cases ha; cases hb; cases hc; cases hd; rfl

lemma program_encoded_state {α : Type*} [Fintype α] {q : ℕ}
    (P : List (Instruction q)) (e : α→Basis q) (ψ : α→ℂ) (z : Basis q)
    (hP : (programMatrix P).mulVec (basisVector z)=encodeState e ψ) (W t d : ℕ) :
    (programMatrix (program P W t d)).mulVec
      (basisVector (layout q W t d ((fun _=>false),z,(fun _=>false),(fun _=>false))))=
      encodeState (extendEncoding e W t d) (fresh ψ W t d) := by
  let D:=coinBits W t d
  have hG := parallelProgram_encoded_state
    (hadamardPrefix W W le_rfl) (hadamardPrefix D D le_rfl)
    (fun _=>false) (fun _=>false) id id (fairState W) (fairState D)
    (hadamards_zero_encoded W) (hadamards_zero_encoded D)
  have hO := parallelProgram_encoded_state P
    (parallelProgram (hadamardPrefix W W le_rfl) (hadamardPrefix D D le_rfl))
    z (Fin.append (fun _ : Fin W=>false) (fun _ : Fin D=>false)) e
    (fun r : Basis W×Basis D=>Fin.append r.1 r.2) ψ
    (independentState (fairState W) (fairState D)) hP hG
  have hT := parallelProgram_encoded_state
    (hadamardPrefix t t le_rfl)
    (parallelProgram P (parallelProgram (hadamardPrefix W W le_rfl) (hadamardPrefix D D le_rfl)))
    (fun _=>false) (Fin.append z (Fin.append (fun _ : Fin W=>false) (fun _ : Fin D=>false)))
    id (fun r : α×(Basis W×Basis D)=>Fin.append (e r.1) (Fin.append r.2.1 r.2.2))
    (fairState t) (independentState ψ (independentState (fairState W) (fairState D)))
    (hadamards_zero_encoded t) hO
  exact hT
end Completion

namespace PhysicalTree

lemma quarterProgram_state (n N : ℕ) :
    (programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))=
      encodeState (quarterEncoding n N) (Quarter.fresh (paddedState n N) n) :=
  Completion.program_encoded_state _ _ _ _ (paddedProgram_state n N) _ _ _
lemma quarterEncoding_injective (n N : ℕ) : Function.Injective (quarterEncoding n N) :=
  Completion.extendEncoding_injective _ (paddedEncoding_injective n N) _ _ _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_VerifiedRoot
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
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
lemma first_verified (x : Basis c) (t : ℕ) (h : Trace n (t+1))
    (hp : M.verified x (t+1) h) :
    PhysicalTree.NodeVerified (M.query.eval x) (firstRaw t h) := by
  induction t with
  | zero=>exact hp.2
  | succ t ih=>exact ih h.1 hp.1
end NodeMachine
namespace PhysicalTree
lemma nodeWords_layout (n : ℕ) (z : Basis (NodeKernel.width n)) :
    SortedWords.layout n n (nodeWords n z)=(nodeResult n).eval z := by
  simp only [nodeWords,SortedWords.layout_ofFn,resultFields,eval_comp,tensorSelect_inverse]
  exact (tensorLayout n n).apply_symm_apply _

/-- The literal data-verifier flag implies a correct root readout on arbitrary
raw histories, not just on histories assumed successful in the analysis. -/
theorem verified_root {n N : ℕ} (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hp : (machine n).verified (initialQueue n N) (t+1) h) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (rootResult n t).eval ((machine n).encoded (initialQueue n N) (t+1) h)=
        SortedWords.layout n n zs := by
  have hp0:=(machine n).first_verified (initialQueue n N) t h hp
  change NodeVerified ((query n).eval (initialQueue n N)) (NodeMachine.firstRaw t h) at hp0
  rw [query_initial] at hp0
  have hv : (bitsValue (natBasis n N)).toNat=N := by rw [natBasis_value,Nat.mod_eq_of_lt hb]
  rcases hp0 with hz | hc
  · rw [hv] at hz
    omega
  · refine ⟨nodeWords n (NodeKernel.encoding (natBasis n N) (NodeMachine.firstRaw t h)),
      nodeWords_length _ _,?_,?_⟩
    · simpa only [hv] using hc
    · rw [rootResult,eval_comp,NodeMachine.firstNodeNet_encoded,nodeWords_layout]
      change (nodeResult n).eval (NodeKernel.encoding ((query n).eval (initialQueue n N)) _) = _
      rw [query_initial]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeRootOutput
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
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma flattenWords_numbers {n : ℕ} (zs : List (Basis n)) (hl : zs.length=n) :
    guessWords n ((flattenWords n).eval (SortedWords.layout n n zs))=SortedWords.numbers zs := by
  let f : Fin n→Basis n := fun i=>zs[i.val]'(by omega)
  have hf : List.ofFn f=zs := by
    apply List.ext_getElem
    · simp only [List.length_ofFn,hl]
    · intro i hi hj
      simp only [List.getElem_ofFn,f]
  rw [←hf,SortedWords.layout_ofFn]
  simp only [guessWords,flattenWords,wordBlocks_eval,tensorSelect_eval,
    SortedWords.numbers,List.map_ofFn,Function.comp_def]

lemma rootFlat_correct {n N : ℕ} (hN : 2≤N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hv : (machine n).verified (initialQueue n N) (t+1) h) :
    CorrectEncoding N n (guessWords n ((rootFlat n (t+1)).eval
      ((machine n).encoded (initialQueue n N) (t+1) h))) := by
  obtain ⟨zs,hl,hc,he⟩:=verified_root hN hb t h hv
  rw [rootFlat,eval_comp,he,flattenWords_numbers zs hl]
  exact hc

/-- Soundness uses verifier success on this raw history, not ideal quantum
success or an externally supplied prime-factorization list. -/
theorem padded_output {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : PaddedRaw n) (hp : paddedAccepted (N:=N) (by omega) r) :
    CorrectEncoding N n (guessWords n (ordinaryOutput n N r)) := by
  have hh : ∀ (t : ℕ) (h : NodeMachine.Trace n t), 0<t →
      (machine n).verified (initialQueue n N) t h →
      CorrectEncoding N n (guessWords n ((rootFlat n t).eval
        ((machine n).encoded (initialQueue n N) t h))) := by
    intro t
    cases t with
    | zero=>intro _ ht; omega
    | succ t=>intro h _ hv; exact rootFlat_correct hN hb t h hv
  apply hh _ _ _ hp.1.1
  have : 0<n := by omega
  positivity

/-- Both branches of Section 6's final quarter-probability preparation now
use the actual chronological tree. This is an event/output theorem; it does
not assert the missing efficient Boolean implementation of the full flag. -/
theorem quarter_mass {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (Quarter.passed N (paddedAccepted (n:=n) (N:=N) (by omega)))
      (Quarter.fresh (paddedState n N) n)=1/4 := by
  exact Quarter.passed_mass hn hN hb _ _ (padded_normalized n N) (padded_mass hn hN hb)

theorem quarter_output {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : Quarter.Raw (PaddedRaw n) n)
    (hp : Quarter.passed N (paddedAccepted (n:=n) (N:=N) (by omega)) r) :
    CorrectEncoding N n (guessWords n (Completion.output (ordinaryOutput n N) r)) :=
  Quarter.passed_correct _ _ (fun r hr=>padded_output hn hN hb r hr) r hp

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedQuarterFilter
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
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

lemma paddedHistory_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedHistory n).eval (paddedEncoding n N r)=
      (machine n).encoded (initialQueue n N) (2*n^2) r.1 := by
  simp only [paddedHistory,eval_comp,eval_select,Function.comp_def,paddedEncoding,
    Fin.append_left,launchHistory,launchEncoding]
  exact packed_targetRegister _ _
lemma quarterOutputNet_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterOutputNet n).eval (quarterEncoding n N r)=
      Completion.output (ordinaryOutput n N) r := by
  rw [quarterOutputNet]
  change (Completion.outputNet (paddedOutputNet n) 1 (n^11)).eval
    (Completion.layout _ _ _ _ (r.1,paddedEncoding n N r.2.1,r.2.2))=_
  rw [Completion.outputNet_eval]
  simp only [Completion.output,paddedOutputNet,eval_comp,paddedHistory_eval,ordinaryOutput]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OracleReadOnly
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
open BooleanNetwork

lemma BooleanOp.compile_target {q : ℕ} {t : Fin q} (b : BooleanOp q t) :
    ∀ o∈b.compile,o.target=t := by
  cases b with
  | constant b=>cases b <;> simp [BooleanOp.compile]
  | copy=>simp [BooleanOp.compile]
  | neg=>simp [BooleanOp.compile]
  | conj a b ha hb=>simp only [BooleanOp.compile];split_ifs <;> simp

lemma BooleanProgram.compile_target {q n : ℕ} (P : BooleanProgram q)
    (h : ∀ a∈P,n≤a.1.val) : ∀ o∈P.compile,n≤o.target.val := by
  intro o ho
  obtain ⟨a,ha,ho⟩:=List.mem_flatMap.mp ho
  rw [a.2.compile_target o ho]
  exact h a ha

lemma BoolNet.program_target {n k q : ℕ} (p : BoolNet n k) (h : k≤q) :
    ∀ a∈p.program h,n≤a.1.val := by
  induction p with
  | input=>simp [BoolNet.program]
  | @add k p b ih=>
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact ih (by omega) a ha
    · have he:=List.mem_singleton.mp ha
      subst a
      exact p.input_le

lemma BooleanNetwork.copyPrefix_target {k m : ℕ} (f : Fin m→Fin k) (t : ℕ) (h : t ≤ m) :
    ∀ a∈copyPrefix f t h,k≤a.1.val := by
  induction t with
  | zero=>simp [copyPrefix]
  | succ t ih=>
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact ih (by omega) a ha
    · have he:=List.mem_singleton.mp ha
      subst a
      simp

lemma BooleanNetwork.oracle_target {n m : ℕ} (c : BooleanNetwork n m) :
    ∀ o∈c.oracle,n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · rcases List.mem_append.mp ho with ho|ho
    · exact BooleanProgram.compile_target _ (c.net.program_target _) o ho
    · exact c.net.input_le.trans (BooleanProgram.compile_target _
        (copyPrefix_target _ _ _) o ho)
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
    rw [Instruction.target_reverse]
    exact BooleanProgram.compile_target _ (c.net.program_target _) a (List.mem_reverse.mp ha)

/-- Compute/copy/uncompute never targets a read-only input, including on
malformed scratch states. This global property is what reflection needs. -/
lemma BooleanNetwork.oracleOn_target {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    ∀ o∈oracleOn c hr,n≤o.target.val := by
  intro o ho
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
  rw [Instruction.target_place,oraclePlacement_val]
  have hn:=c.oracle_target a ha
  simp only [oracleIndex,ite_eq_right (Nat.not_lt.mpr hn)]
  split_ifs <;> omega

lemma targetProgram_target {n m r : ℕ} (P : List (Instruction m)) :
    ∀ o∈targetProgram n r P,n≤o.target.val := by
  intro o ho
  obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp ho
  rw [Instruction.target_place,targetRegister_val]
  omega

lemma preparedOracle_target {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (P : List (Instruction m)) : ∀ o∈preparedOracle c hr P,n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · exact c.oracleOn_target hr o ho
  · exact targetProgram_target P o ho

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeReadOnly
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
open BooleanNetwork Exactness

/-- Parallel fresh work does not alter the prefix protected by the left program. -/
lemma parallelProgram_prefix_target {p q n : ℕ} (P : List (Instruction p))
    (Q : List (Instruction q)) (hn : n≤p) (hP : ∀ o∈P,n≤o.target.val) :
    ∀ o∈parallelProgram P Q,n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
    have ha':=hP a ha
    simpa only [Instruction.target_place,leftRegister,Function.Embedding.coeFn_mk,
      Fin.val_castAdd] using ha'
  · obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp ho
    change n≤p+a.target.val
    omega

/-- The branch register preceding an otherwise read-only prefix introduces
only targets before that prefix, never in it. -/
lemma parallelProgram_interval_target {p q n : ℕ} (P : List (Instruction p))
    (Q : List (Instruction q)) (hQ : ∀ o∈Q,n≤o.target.val) :
    ∀ o∈parallelProgram P Q,o.target.val<p ∨ p+n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp ho
    exact Or.inl a.target.isLt
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
    exact Or.inr (Nat.add_le_add_left (hQ a ha) p)

namespace PhysicalTree
lemma paddedProgram_prefix_target (n : ℕ) : ∀ o∈paddedProgram n,n≤o.target.val := by
  apply parallelProgram_prefix_target
  · dsimp only [launchWidth]
    omega
  · exact preparedOracle_target _ _ _

lemma quarterProgram_interval_target (n : ℕ) :
    ∀ o∈quarterProgram n,o.target.val<1 ∨ 1+n≤o.target.val := by
  apply parallelProgram_interval_target
  apply parallelProgram_prefix_target
  · dsimp only [paddedWidth,launchWidth]
    omega
  · exact paddedProgram_prefix_target n

lemma quarterProgram_readOnly (n : ℕ) : ReadOnly (inputWires n) (quarterProgram n) := by
  intro o ho hi
  have ht:=quarterProgram_interval_target n o ho
  have hi':=(Finset.mem_filter.mp hi).2
  omega

/-- This is global input invariance, not merely a clean-input statement. -/
lemma quarterProgram_respects_input (n N : ℕ) :
    RespectsSector (inputSector (inputWires n) (quarterZero n N)) (programMatrix (quarterProgram n)) :=
  program_respects_input _ _ (quarterProgram_readOnly n) _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ZeroOutside
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
open BooleanNetwork Exactness

lemma zeroOutside_value {q : ℕ} (I : Finset (Fin q)) (x : Basis q) :
    (zeroOutside I).eval x 0=true ↔ ∀ i, i∉I → x i=false := by
  simp only [zeroOutside,all_eval,List.mem_ofFn]
  constructor
  · intro h i hi
    have hh:=h _ ⟨i,rfl⟩
    simpa only [ite_eq_right hi,eval_bnot,eval_bit,Bool.not_eq_true'] using hh
  · intro h c hc
    obtain ⟨i,rfl⟩:=hc
    by_cases hi : i∈I
    · simp only [ite_eq_left hi,eval_constant]
    · simp only [ite_eq_right hi,eval_bnot,eval_bit,h i hi,Bool.not_false]

lemma zeroOutside_sector {q : ℕ} (I : Finset (Fin q)) (z : Basis q)
    (hz : ∀ i, i∉I → z i=false) (x : Basis q) (hx : inputSector I z x) :
    (zeroOutside I).eval x 0=true ↔ x=z := by
  rw [zeroOutside_value]
  constructor
  · intro h
    funext i
    by_cases hi : i∈I
    · exact hx i hi
    · rw [h i hi,hz i hi]
  · rintro rfl
    exact hz

lemma tensorLayout_zero (q k : ℕ) :
    tensorLayout q k (fun _ _=>false)=(fun _=>false) := by
  induction k with
  | zero=>funext i;exact Fin.elim0 i
  | succ k ih=>
    rw [tensorLayout_succ]
    change Fin.append (fun _=>false) (tensorLayout q k (fun _ _=>false))=_
    rw [ih]
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Fin.append_left,Fin.append_right]

namespace PhysicalTree
lemma launchZero_suffix (n N : ℕ) (i : Fin (launchWidth n)) (hi : n ≤ i.val) :
    launchZero n N i=false := by
  simp only [launchZero,packed,dite_eq_right (Nat.not_lt.mpr hi)]
  split_ifs <;> rfl

lemma paddedZero_suffix (n N : ℕ) (i : Fin (paddedWidth n)) (hi : n ≤ i.val) :
    paddedZero n N i=false := by
  revert hi
  refine Fin.addCases ?_ ?_ i
  · intro j hj
    simpa only [paddedZero,Fin.append_left] using launchZero_suffix n N j hj
  · intro j _hj
    simp only [paddedZero,Fin.append_right]
    change tensorLayout n (padding n) (fun _ _=>false) j=false
    rw [tensorLayout_zero]

lemma quarterZero_clean (n N : ℕ) (i : Fin (quarterWidth n)) (hi : i∉inputWires n) :
    quarterZero n N i=false := by
  revert hi
  refine Fin.addCases ?_ ?_ i
  · intro j _hj
    simp only [quarterZero,Completion.layout,productLayout_apply,Equiv.refl_apply,Fin.append_left]
  · intro j hj
    simp only [quarterZero,Completion.layout,productLayout_apply,Equiv.refl_apply,Fin.append_right]
    change Fin.append (paddedZero n N) (Fin.append (fun _ : Fin (n*n)=>false)
      (fun _ : Fin (Quarter.D n)=>false)) j=false
    have hn : n ≤ j.val := by
      have hh : ¬(1 ≤ 1+j.val ∧ 1+j.val < 1+n) := by
        simpa only [inputWires,Finset.mem_filter,Finset.mem_univ,true_and,
          Fin.val_natAdd] using hj
      omega
    clear hj
    revert hn
    refine Fin.addCases ?_ ?_ j
    · intro a ha
      simpa only [Fin.append_left] using paddedZero_suffix n N a ha
    · intro a _ha
      simp only [Fin.append_right]
      refine Fin.addCases ?_ ?_ a <;> intro j <;> simp only [Fin.append_left,Fin.append_right]

lemma zeroNet_sector (n N : ℕ) (x : Basis (quarterWidth n))
    (hx : inputSector (inputWires n) (quarterZero n N) x) :
    (zeroNet n).eval x 0=true ↔ x=quarterZero n N :=
  zeroOutside_sector _ _ (quarterZero_clean n N) _ hx

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeAmplified
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma actual_quarter_mass {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x=>(quarterFlag n (by omega)).eval x 0=true)
      ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N)))=1/4 := by
  rw [quarterProgram_state,outcomeMass_encode _ (quarterEncoding_injective n N)]
  have he : ((fun x=>(quarterFlag n (by omega)).eval x 0=true) ∘ quarterEncoding n N)=
      Quarter.passed N (paddedAccepted (N:=N) (by omega)) := by
    funext r
    exact propext (quarterFlag_eval hn hN hb r)
  rw [he]
  exact quarter_mass hn hN hb

/-- An unconditional physical amplification identity for the actual program.
The only hypotheses are the manuscript's padded length and valid input. -/
theorem amplifiedProgram_state {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    (programMatrix (amplifiedProgram n (by omega))).mulVec
      (basisVector (amplifiedZero n N (by omega))) =
      encodeState (fun x=>packed (reflectWork n (by omega)) x (fun _ : Fin 1=>false))
        (fun x=> -2*goodPart (fun y=>(quarterFlag n (by omega)).eval y 0=true)
          ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) x) := by
  apply physical_quarter_amplification _ _ _ _ _
    (inputSector (inputWires n) (quarterZero n N))
    (quarterProgram_respects_input n N) _
  · intro _ _; rfl
  · exact zeroNet_sector n N
  · exact actual_quarter_mass hn hN hb

lemma prepared_nonzero_encoding {n N : ℕ} (x : Basis (quarterWidth n))
    (hx : ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) x≠0) :
    ∃ r : Quarter.Raw (PaddedRaw n) n, quarterEncoding n N r=x := by
  classical
  rw [quarterProgram_state] at hx
  by_contra hh
  exact hx (encodeState_outside _ _ x hh)

lemma quarterFlag_output_on_support {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (x : Basis (quarterWidth n))
    (hx : ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) x≠0)
    (hp : (quarterFlag n (by omega)).eval x 0=true) :
    CorrectEncoding N n (guessWords n ((quarterOutputNet n).eval x)) := by
  obtain ⟨r,rfl⟩:=prepared_nonzero_encoding x hx
  rw [quarterOutputNet_eval]
  exact quarter_output hn hN hb r ((quarterFlag_eval hn hN hb r).mp hp)

/-- Exact support on complete sorted factorizations, for the actual finite
fixed-gate program and a literal Boolean readout. This is a necessary main
proof dependency, not the missing polynomial/uniform circuit-family theorem. -/
theorem amplified_output_on_support {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (x : Basis (amplifiedWidth n (by omega)))
    (hx : ((programMatrix (amplifiedProgram n (by omega))).mulVec
      (basisVector (amplifiedZero n N (by omega)))) x≠0) :
    CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x)) := by
  classical
  rw [amplifiedProgram_state hn hN hb] at hx
  have hr : ∃ y : Basis (quarterWidth n),
      packed (reflectWork n (by omega)) y (fun _ : Fin 1=>false)=x := by
    by_contra hh
    exact hx (encodeState_outside _ _ x hh)
  obtain ⟨y,rfl⟩:=hr
  rw [encodeState_at _ (packed_injective _)] at hx
  have hg : goodPart (fun z=>(quarterFlag n (by omega)).eval z 0=true)
      ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) y≠0 := by
    intro h; exact hx (by rw [h,mul_zero])
  have hp : (quarterFlag n (by omega)).eval y 0=true := by
    by_contra hp
    exact hg (by simp only [goodPart,ite_eq_right hp])
  have hy : ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) y≠0 := by
    simpa only [goodPart,ite_eq_left hp] using hg
  have he : (amplifiedOutput n (by omega)).eval
      (packed (reflectWork n (by omega)) y (fun _ : Fin 1=>false))=(quarterOutputNet n).eval y := by
    rw [amplifiedOutput,eval_comp,eval_select,packed_first]
  rw [he]
  exact quarterFlag_output_on_support hn hN hb y hy hp

lemma amplified_mass_one {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x=>CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x)))
      ((programMatrix (amplifiedProgram n (by omega))).mulVec
        (basisVector (amplifiedZero n N (by omega))))=1 := by
  classical
  have he : ∀ x : Basis (amplifiedWidth n (by omega)),
      (if CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x)) then
        Complex.normSq (((programMatrix (amplifiedProgram n (by omega))).mulVec
          (basisVector (amplifiedZero n N (by omega)))) x) else 0)=
        Complex.normSq (((programMatrix (amplifiedProgram n (by omega))).mulVec
          (basisVector (amplifiedZero n N (by omega)))) x) := by
    intro x
    by_cases hx : ((programMatrix (amplifiedProgram n (by omega))).mulVec
      (basisVector (amplifiedZero n N (by omega)))) x=0
    · simp only [hx,Complex.normSq_zero,ite_self]
    · rw [ite_eq_left (amplified_output_on_support hn hN hb x hx)]
  simp_rw [outcomeMass,he]
  rw [unitary_mass _ (programMatrix_unitary _)]
  simp [basisVector]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeReadout
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
open BooleanNetwork BitArithmetic Exactness

lemma readoutProgram_state {q m r : ℕ} (P : List (Instruction q))
    (c : BooleanNetwork q m) (hr : c.net.count ≤ r) (z : Basis q) :
    (programMatrix (readoutProgram P c hr)).mulVec
      (basisVector (packed r z (fun _=>false)))=
      encodeState (fun x=>packed r x (c.eval x)) ((programMatrix P).mulVec (basisVector z)) := by
  rw [readoutProgram,programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis]
  rw [encodeState,Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rfl

namespace PhysicalTree

/-- Probability ONE of complete factorization for the actual finite physical
fixed-gate program, with its clean reversible readout. Polynomial resource
bounds and finite-alphabet polynomial-time uniformity are separate properties
of the same circuit family. -/
theorem factoringProgram_exact {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x=>CorrectEncoding N n (guessWords n (factoringResult n (by omega) x)))
      ((programMatrix (factoringProgram n (by omega))).mulVec
        (basisVector (factoringZero n N (by omega))))=1 := by
  rw [factoringProgram,factoringZero,readoutProgram_state]
  have hi : Function.Injective (fun x : Basis (amplifiedWidth n (by omega))=>
      packed (readoutWork n (by omega)) x ((amplifiedOutput n (by omega)).eval x)) := by
    intro x y hxy
    have hh:=congrArg (fun z=>z ∘ firstRegister (amplifiedWidth n (by omega)) (n*n)
      (readoutWork n (by omega))) hxy
    simpa only [packed_first] using hh
  rw [outcomeMass_encode _ hi]
  have he : ((fun x : Basis (readoutWidth n (by omega))=>CorrectEncoding N n (guessWords n (factoringResult n (by omega) x))) ∘
      (fun x : Basis (amplifiedWidth n (by omega))=>packed (readoutWork n (by omega)) x ((amplifiedOutput n (by omega)).eval x)))=
      (fun x : Basis (amplifiedWidth n (by omega))=>CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x))) := by
    funext x
    simp only [Function.comp_apply,factoringResult,packed_targetRegister]
  rw [he]
  exact amplified_mass_one hn hN hb

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactoringInputLayout
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
open BooleanNetwork BitArithmetic OrderTrial

lemma natBasis_apply (w N : ℕ) (i : Fin w) : natBasis w N i=N.testBit i.val := by
  simp only [natBasis,BitVec.getLsbD_ofNat,decide_true,i.isLt,Bool.true_and]

lemma packed_shifted {q m r n N : ℕ} (hn : 1+n≤q) :
    packed r (shiftedInput q n N) (fun _ : Fin m=>false)=shiftedInput (q+m+r) n N := by
  funext i
  simp only [packed,shiftedInput]
  by_cases hq : i.val < q
  · rw [dite_eq_left hq]
  · rw [dite_eq_right hq]
    have hi : ¬(1 ≤ i.val ∧ i.val < 1+n) := by omega
    rw [ite_eq_right hi]
    split_ifs <;> rfl

namespace PhysicalTree
lemma quarterZero_input (n N : ℕ) (j : Fin n) :
    quarterZero n N
      (Fin.natAdd 1 ((Fin.castAdd (n*n+Quarter.D n))
        ((Fin.castAdd (tensorWidth n (padding n)))
          (firstRegister n (width n) (launchWork n) j))))=N.testBit j.val := by
  simp only [quarterZero,Completion.layout,productLayout_apply,Equiv.refl_apply,
    Fin.append_right,Fin.append_left,paddedZero,launchZero]
  change packed (launchWork n) (natBasis n N) (fun _ : Fin (width n) => false)
    ⟨j.val, by omega⟩ = _
  rw [packed_input]
  exact natBasis_apply n N j

lemma quarterZero_shifted (n N : ℕ) : quarterZero n N=shiftedInput (quarterWidth n) n N := by
  funext i
  by_cases hi : 1 ≤ i.val ∧ i.val < 1+n
  · let j : Fin n:=⟨i.val-1,by omega⟩
    have he : i=Fin.natAdd 1 ((Fin.castAdd (n*n+Quarter.D n))
        ((Fin.castAdd (tensorWidth n (padding n)))
          (firstRegister n (width n) (launchWork n) j))) := by
      apply Fin.ext
      change i.val=1+(i.val-1)
      omega
    rw [he,quarterZero_input]
    change N.testBit (i.val-1)=_
    rw [←he]
    simp only [shiftedInput,ite_eq_left hi]
  · rw [quarterZero_clean n N i,shiftedInput,ite_eq_right hi]
    simpa only [inputWires,Finset.mem_filter,Finset.mem_univ,true_and] using hi

lemma amplifiedZero_shifted (n N : ℕ) (hn : 0<n) :
    amplifiedZero n N hn=shiftedInput (amplifiedWidth n hn) n N := by
  rw [amplifiedZero,quarterZero_shifted,packed_shifted (quarterWidth_input n)]

lemma factoringZero_shifted (n N : ℕ) (hn : 0<n) :
    factoringZero n N hn=shiftedInput (readoutWidth n hn) n N := by
  rw [factoringZero,amplifiedZero_shifted]
  apply packed_shifted
  have hh:=quarterWidth_input n
  change 1+n≤quarterWidth n+1+reflectWork n hn
  omega
end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactoringRelabel
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma relocate_input (A m ℓ r N : ℕ) (hl : ℓ+1≤A) :
    inputBasis (A+m+r) ℓ N ∘ relocate A m ℓ r hl = shiftedInput (A+m+r) ℓ N := by
  funext i
  change (if relocateVal A m ℓ i.val < ℓ then N.testBit (relocateVal A m ℓ i.val) else false)=_
  unfold shiftedInput relocateVal
  split_ifs <;> simp_all <;> omega

lemma relocate_output (A m ℓ r : ℕ) (hl : ℓ+1≤A) (j : Fin m) :
    (relocate A m ℓ r hl) ⟨A+j.val,by omega⟩=⟨ℓ+j.val,by have:=j.isLt;omega⟩ := by
  apply Fin.ext
  change relocateVal A m ℓ (A+j.val)=ℓ+j.val
  have hj:=j.isLt
  unfold relocateVal
  split_ifs <;> omega

lemma shiftedInput_pad (q n ℓ N : ℕ) (hl : ℓ≤n) (hb : N<2^ℓ) :
    shiftedInput q ℓ N=shiftedInput q n N := by
  funext i
  unfold shiftedInput
  by_cases hi : 1 ≤ i.val ∧ i.val < 1+ℓ
  · rw [ite_eq_left hi,ite_eq_left (by omega)]
  · rw [ite_eq_right hi]
    split_ifs with hj
    · have hb' : N<2^(i.val-1) := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow hb']
    · rfl
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactoringCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma final_input (ℓ N : ℕ) (hb : N<2^ℓ) :
    inputBasis (finalCircuit ℓ).qubits ℓ N ∘ finalRegister ℓ=
      factoringZero (paddedLength ℓ) N (paddedLength_pos ℓ) := by
  dsimp only [finalCircuit]
  rw [finalRegister,relocate_input]
  rw [shiftedInput_pad _ (paddedLength ℓ) ℓ N (le_max_right _ _) hb]
  exact (factoringZero_shifted _ _ _).symm

lemma final_register_output (ℓ : ℕ) (j : Fin (paddedLength ℓ*paddedLength ℓ)) :
    finalRegister ℓ (targetRegister (amplifiedWidth (paddedLength ℓ) (paddedLength_pos ℓ))
      (paddedLength ℓ*paddedLength ℓ) (readoutWork (paddedLength ℓ) (paddedLength_pos ℓ)) j)=
    ⟨ℓ+j.val,by have:=j.isLt;have:=finalRegister_bound ℓ;dsimp only [readoutWidth];omega⟩ := by
  exact relocate_output _ _ _ _ _ j

lemma final_output (ℓ : ℕ) (z : Basis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)))
    (x : Basis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ))) :
    outputList ℓ ((finalRegister ℓ).replace z x)=
      guessWords (paddedLength ℓ) (factoringResult (paddedLength ℓ) (paddedLength_pos ℓ) x) := by
  dsimp only [outputList,guessWords]
  apply congrArg List.ofFn
  funext a
  rw [bitsValue_toNat,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  let k : Fin (paddedLength ℓ*paddedLength ℓ):=finProdFinEquiv (a,j)
  have hk : k.val=a.val*paddedLength ℓ+j.val:=by
    change j.val+paddedLength ℓ*a.val=a.val*paddedLength ℓ+j.val
    ring
  have hh:=final_register_output ℓ k
  have hb : ℓ+a.val*paddedLength ℓ+j.val < readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ) := by
    have hi:=(finalRegister ℓ (targetRegister _ _ _ k)).isLt
    rw [hh] at hi
    dsimp only at hi
    omega
  simp only [readBit,dite_eq_left hb]
  have he : (⟨ℓ+a.val*paddedLength ℓ+j.val,hb⟩ : Fin (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)))=
      finalRegister ℓ (targetRegister _ _ _ k) := by
    rw [hh];apply Fin.ext;dsimp only;omega
  rw [he,Register.replace_inside]
  change (if x (targetRegister _ _ _ k) then 2^j.val else 0)=
    2^j.val*(x (targetRegister _ _ _ k)).toNat
  cases x (targetRegister _ _ _ k) <;> simp

lemma finalCircuit_qubits (ℓ : ℕ) :
    ℓ+(paddedLength ℓ)^2≤(finalCircuit ℓ).qubits := by
  have h:=finalRegister_bound ℓ
  change ℓ+(paddedLength ℓ)^2≤amplifiedWidth _ _+paddedLength ℓ*paddedLength ℓ+readoutWork _ _
  rw [pow_two]
  omega

theorem finalCircuit_exact (ℓ N : ℕ) (hN : 2≤N) (hb : N<2^ℓ) :
    (finalCircuit ℓ).correctProbability ℓ N=1 := by
  have hh : 128≤paddedLength ℓ:=le_max_left _ _
  have hb' : N<2^paddedLength ℓ:=lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  change outcomeMass (fun x=>CorrectEncoding N (paddedLength ℓ) (outputList ℓ x))
    ((finalCircuit ℓ).apply (basisVector (inputBasis (finalCircuit ℓ).qubits ℓ N)))=1
  rw [Circuit.apply_eq_matrix]
  change outcomeMass (fun x : Basis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ))=>
      CorrectEncoding N (paddedLength ℓ) (outputList ℓ x))
    ((programMatrix ((factoringProgram (paddedLength ℓ) (paddedLength_pos ℓ)).map
      (Instruction.place (finalRegister ℓ)))).mulVec
      (basisVector (inputBasis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) ℓ N)))=1
  rw [Register.placed_basis_state]
  have hin := final_input ℓ N hb
  change inputBasis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) ℓ N ∘ finalRegister ℓ = _ at hin
  rw [hin]
  rw [outcomeMass_encode _ (Register.replace_injective _ _)]
  have he : ((fun x=>CorrectEncoding N (paddedLength ℓ) (outputList ℓ x)) ∘
      ((finalRegister ℓ).replace (inputBasis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) ℓ N)))=
      (fun x=>CorrectEncoding N (paddedLength ℓ)
        (guessWords (paddedLength ℓ) (factoringResult (paddedLength ℓ) (paddedLength_pos ℓ) x))) := by
    funext x
    simp only [Function.comp_apply,final_output]
  rw [he]
  exact factoringProgram_exact hh hN hb'

/-- Discharges exactly the input/output clause for one explicit length-only
family. This does NOT assert the outstanding resource or TM2-uniformity clauses. -/
theorem finalCircuit_spec_oai (ℓ N : ℕ) (hN : 2≤N) (hs : N.size=ℓ) :
    ℓ+(paddedLength ℓ)^2≤(finalCircuit ℓ).qubits ∧
      (finalCircuit ℓ).correctProbability ℓ N=1 := by
  refine ⟨finalCircuit_qubits ℓ,finalCircuit_exact ℓ N hN ?_⟩
  rw [←hs]
  exact Nat.lt_size_self N

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_spec_oai := @OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_spec_oai
