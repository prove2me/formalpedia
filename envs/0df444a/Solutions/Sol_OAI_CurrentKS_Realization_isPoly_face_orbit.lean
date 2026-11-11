-- Prove2me | solution 1 for OAI.CurrentKS.Realization.isPoly_face_orbit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:09:34.666142+00:00
-- url     : https://prove2.me/submissions/b6194e3d-a41b-4506-9f40-65de3ed150ab

import Mathlib
import Definitions.Def_OAIQ241TT014
import Theorems.Thm_OAI_CurrentKS_RationalFace_transition_spec

section
-- module Solutions.OAIQ241_TT.Compat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_Realification
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W08.realifyVector_complexify _root_.OAI.KS.W08.realifyVector_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open Matrix
open scoped BigOperators

theorem realify_injective {m n : Type*} :
    Function.Injective (@realify m n) := by
  intro A B h
  apply Matrix.ext
  intro i j
  apply Complex.ext
  · exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  · exact congrFun (congrFun h (Sum.inr i)) (Sum.inl j)

theorem realify_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    realify (A * B) = realify A * realify B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Complex.mul_re,
      Complex.mul_im, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib] <;> ring

theorem realify_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v : n → ℂ) :
    realifyVector (A *ᵥ v) = realify A *ᵥ realifyVector v := by
  funext i
  rcases i with i | i <;>
    simp [realifyVector, realify, Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] <;> ring

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RealifyAdd
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace KS.W08
open Matrix
open scoped BigOperators

variable {m n p : Type*}

lemma realify_add (A B : Matrix m n ℂ) : realify (A+B)=realify A+realify B := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.fromBlocks, neg_add_rev, add_comm]
lemma realify_zero : realify (0 : Matrix m n ℂ)=0 := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.fromBlocks]
lemma realify_smul (r : ℝ) (A : Matrix m n ℂ) : realify (r • A)=r • realify A := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.fromBlocks]
lemma realify_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) :
    realify (∑ i ∈ s,A i)=∑ i ∈ s,realify (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [realify_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,realify_add,ih]
end KS.W08

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_HermitianMat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_one _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

variable {d : ℕ}

section OperatorNorm
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem trace_mul_nonneg {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let : CStarAlgebra (Mat d) := {}
  have hs : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have ht := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [hs.isHermitian.eq, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at ht
  exact (Complex.nonneg_iff.mp ht).1

end OperatorNorm

open scoped Matrix.Norms.Frobenius

lemma inner_smul_leftH (A B : H d) (r : ℝ) :
    inner ℝ (r • A) B = r * inner ℝ A B := by
  exact real_inner_smul_left A B r

theorem matrix_inner (d : ℕ) (A B : Mat d) :
    inner ℂ A B = (B * Aᴴ).trace := by
  change inner ℂ (asL2 A) (asL2 B) = _
  simp only [asL2, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1

theorem inner_eq_trace (A B : H d) :
    inner ℝ A B = ((A : Mat d) * (B : Mat d)).trace.re := by
  change (inner ℂ (A : Mat d) (B : Mat d)).re = _
  rw [matrix_inner, A.property.eq, Matrix.trace_mul_comm]

@[simp] theorem inner_one (A : H d) : inner ℝ one A = realTrace A := by
  rw [inner_eq_trace, one_val, one_mul]
  rfl

@[simp] theorem inner_one' (A : H d) : inner ℝ A one = realTrace A := by
  rw [real_inner_comm]
  exact inner_one A

theorem inner_nonneg_of_psd (A B : H d) (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    0 ≤ inner ℝ A B := by
  rw [inner_eq_trace]
  exact trace_mul_nonneg hA hB

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTrace
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open scoped BigOperators ComplexOrder

variable {d : ℕ}

theorem nonzero_eigenvalues_card_le (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ A.rank := by
  classical
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  have hr : (Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)).rank
      ≤ A.rank := by
    rw [← h]
    simp only [Unitary.conjStarAlgAut_apply]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [Matrix.rank_diagonal] at hr
  simpa only [Function.comp_apply, ne_eq, RCLike.ofReal_eq_zero] using hr

theorem nonzero_eigenvalue_unique (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1)
    (i j : Fin d) (hi : hA.eigenvalues i ≠ 0) (hj : hA.eigenvalues j ≠ 0) :
    i = j := by
  have hcard : Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ 1 :=
    (nonzero_eigenvalues_card_le A hA).trans hrank
  have hs := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact congrArg Subtype.val (hs.elim (⟨i, hi⟩ : {i // hA.eigenvalues i ≠ 0}) ⟨j, hj⟩)

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_BitSupport
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalBits

lemma Parts.mono {b c:ℕ} {q:ℚ} (hq:Parts b q) (hbc:b ≤ c) : Parts c q :=
  ⟨hq.1.trans (Nat.pow_le_pow_right (by decide) hbc),
    hq.2.trans (Nat.pow_le_pow_right (by decide) hbc)⟩
lemma Parts.mul {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c) (q*r) :=
  KS.W30.mul_parts_le_two_pow q r b c hq.1 hq.2 hr.1 hr.2
lemma Parts.add {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c+1) (q+r) := by
  have h := KS.W30.add_parts_le_two_pow q r b c hq.1 hq.2 hr.1 hr.2
  exact ⟨h.1,h.2.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))⟩
lemma Parts.inv {b:ℕ} {q:ℚ} (hq:Parts b q) : Parts b q⁻¹ :=
  KS.W30.inv_parts_le_two_pow q b hq.1 hq.2
lemma Parts.div {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c) (q/r) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv
lemma Parts.neg {b:ℕ} {q:ℚ} (hq:Parts b q) : Parts b (-q) := by
  simpa only [Parts,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hq
lemma Parts.abs {b:ℕ} {q:ℚ} (hq:Parts b q) : Parts b |q| := by
  rcases le_total 0 q with h|h
  · rwa [abs_of_nonneg h]
  · rw [abs_of_nonpos h]; exact hq.neg
lemma parts_size (q:ℚ) : Parts (q.num.natAbs.size+q.den.size) q := by
  constructor
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (by omega))

variable {ι : Type*}

lemma LinearBits.coordinate (i:ι) : LinearBits (fun x : ι→ℚ => x i) := by
  refine ⟨1,by decide,?_⟩
  intro b x hx
  exact (hx i).mono (by omega)
lemma LinearBits.constant (q:ℚ) : LinearBits (fun _ : ι→ℚ => q) := by
  refine ⟨q.num.natAbs.size+q.den.size+1,by omega,?_⟩
  intro b x hx
  exact (parts_size q).mono (by nlinarith)
lemma LinearBits.add {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => f x+g x) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D+1,by omega,?_⟩
  intro b x hx
  exact ((hf b x hx).add (hg b x hx)).mono (by nlinarith)
lemma LinearBits.mul {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => f x*g x) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D,by omega,?_⟩
  intro b x hx
  exact ((hf b x hx).mul (hg b x hx)).mono (by nlinarith)
lemma LinearBits.inv {f:(ι→ℚ)→ℚ} (hf:LinearBits f) : LinearBits (fun x => (f x)⁻¹) := by
  obtain ⟨C,hC,hf⟩ := hf
  exact ⟨C,hC,fun b x hx => (hf b x hx).inv⟩
lemma LinearBits.div {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => f x/g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv
lemma LinearBits.abs {f:(ι→ℚ)→ℚ} (hf:LinearBits f) : LinearBits (fun x => |f x|) := by
  obtain ⟨C,hC,hf⟩ := hf
  exact ⟨C,hC,fun b x hx => (hf b x hx).abs⟩
lemma LinearBits.pow {f:(ι→ℚ)→ℚ} (hf:LinearBits f) (k:ℕ) :
    LinearBits (fun x => (f x)^k) := by
  induction k with
  | zero => simpa only [pow_zero] using LinearBits.constant (ι:=ι) 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf
lemma LinearBits.choose {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g)
    (p:(ι→ℚ)→Prop) [DecidablePred p] : LinearBits (fun x => if p x then f x else g x) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D,by omega,?_⟩
  intro b x hx
  dsimp only
  split_ifs
  · exact (hf b x hx).mono (by nlinarith)
  · exact (hg b x hx).mono (by nlinarith)
lemma LinearBits.min {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => min (f x) (g x)) := by
  simpa only [min_def] using hf.choose hg (fun x => f x≤g x)
lemma LinearBits.max {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => max (f x) (g x)) := by
  simpa only [max_def] using hg.choose hf (fun x => f x≤g x)

end CurrentKS.RationalBits

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_NaturalPolynomial
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23

namespace NaturalPolynomial

theorem eval_mono (p : NaturalPolynomial) : Monotone p.eval := by
  intro x y hxy
  induction p with
  | constant c => exact le_rfl
  | «variable» => exact hxy
  | add p q hp hq => exact Nat.add_le_add hp hq
  | mul p q hp hq => exact Nat.mul_le_mul hp hq
  | power p k hp => exact Nat.pow_le_pow_left hp k

end NaturalPolynomial
end KS.W23

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoutineLength
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.RoutineLength
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

lemma action_length (a : KS.W29.StackAction) (w : List Bool) :
    (a.apply w).length≤w.length+1 := by
  cases a <;> simp [KS.W29.StackAction.apply]; omega

lemma step_length (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (b : Bool)
    (j : Fin M.stackCount) : ((M.step s b).«stacks» j).length ≤ (s.«stacks» j).length+1 := by
  rcases s with ⟨control,tapes⟩
  cases control with
  | none => simp [KS.W01.FixedStack.Machine.step]
  | some c => exact action_length _ _

lemma run_length (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (bits : List Bool)
    (j : Fin M.stackCount) : ((M.run s bits).«stacks» j).length ≤ (s.«stacks» j).length+bits.length := by
  induction bits generalizing s with
  | nil => simp [KS.W01.FixedStack.Machine.run]
  | cons b bs ih =>
    have h := ih (M.step s b)
    have hs := step_length M s b j
    simp only [KS.W01.FixedStack.Machine.run,List.length_cons]
    omega

lemma output_length {k : ℕ} {P : Program k} {before after : Fin k → List Bool} {ticks : ℕ}
    (h : RunSpec P before after ticks) (j : Fin k) :
    (after j).length≤(before j).length+ticks := by
  have hr := run_length P.toMachine ⟨some P.initial,before⟩ (List.replicate ticks false) j
  rw [h _ (List.length_replicate ..)] at hr
  simpa using hr

end CurrentKS.RoutineLength

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word} {ed : δ → Word}
  {f : α → β} {g : β → γ}

lemma Realizes.output_length (r : Realizes ea eb f) (x : α) :
    (eb (f x)).length≤(ea x).length+r.cost x := by
  have h := RoutineLength.output_length (r.routine.spec x) 0
  simpa only [io_zero] using h

lemma prodCode_length (p : α×β) : (prodCode ea eb p).length=2*(ea p.1).length+1+(eb p.2).length := by
  simp only [prodCode,PairRoutine.pair,List.length_append,KS.W01.length_frame]
lemma le_prodCode_left (p : α×β) : (ea p.1).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega
lemma le_prodCode_right (p : α×β) : (eb p.2).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega

instance poly_first (ea : α → Word) (eb : β → Word) : PolyTime (first ea eb) := by
  refine ⟨⟨6*X+5,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  have h2 := le_prodCode_right (ea:=ea) (eb:=eb) p
  change 5*(ea p.1).length+(eb p.2).length+5≤6*(prodCode ea eb p).length+5
  omega
instance poly_second (ea : α → Word) (eb : β → Word) : PolyTime (second ea eb) := by
  refine ⟨⟨4*X+3,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  change 4*(ea p.1).length+3≤4*(prodCode ea eb p).length+3
  omega
instance poly_then (r : Realizes ea eb f) (s : Realizes eb ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.then s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q.comp (X+p),?_⟩⟩
  intro x
  have hl := r.output_length x
  have hs := (hq (f x)).trans (q.eval_mono (hl.trans (Nat.add_le_add_left (hp x) _)))
  have hh := Nat.add_le_add (hp x) hs
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_comp,NaturalPolynomial.eval_variable]
  exact hh
instance poly_both {g : α → γ} (r : Realizes ea eb f) (s : Realizes ea ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.both s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨16*X+13*p+q+15,?_⟩⟩
  intro x
  have hl := r.output_length x
  have h1 := hp x
  have h2 := hq x
  change PairRoutine.pairingTicks ea (fun x => eb (f x)) r.cost s.cost x≤
    16*(ea x).length+13*p.eval (ea x).length+q.eval (ea x).length+15
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ListRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ : Type*}

lemma fold_cons (xs ys : List α) : xs.foldl (fun acc x => x::acc) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLoops
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word}

lemma len_listCode (ea : α → Word) (xs : List α) :
    (listCode ea xs).length=(xs.map (fun x => 2*(ea x).length+1)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length,List.map_cons,List.sum_cons,ih]
lemma sum_map_bound (xs : List α) (f : α → ℕ) (B : ℕ) (h : ∀ x∈xs,f x≤B) :
    (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
lemma listCode_length_bound (xs : List α) (B : ℕ) (h : ∀ x∈xs,(ea x).length≤B) :
    (listCode ea xs).length≤xs.length*(2*B+1) := by
  rw [len_listCode]
  apply sum_map_bound
  intro x hx
  have := h x hx
  omega
lemma list_length_le_code (ea : α → Word) (xs : List α) : xs.length≤(listCode ea xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length,List.length_cons];omega
lemma mem_length_le_code (xs : List α) {x : α} (hx : x∈xs) :
    (ea x).length≤(listCode ea xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rw [listCode_cons,prodCode_length]
      dsimp only
      rcases hx with rfl|hx
      · omega
      · have := ih hx;omega
lemma listCode_reverse_length (ea : α → Word) (xs : List α) :
    (listCode ea xs.reverse).length=(listCode ea xs).length := by
  simp only [len_listCode,List.map_reverse,List.sum_reverse]

instance poly_map {f : α → β} (r : Realizes ea eb f) [PolyTime r] : PolyTime r.map := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let Q := X+p
  refine ⟨⟨2*X+X*(3*X+p+6*Q+8)+X*(2*Q+1)+4,?_⟩⟩
  intro xs
  let L := (listCode ea xs).length
  have hn : xs.length≤L := list_length_le_code ea xs
  have ho : ∀ x∈xs,(eb (f x)).length≤L+p.eval L := by
    intro x hx
    have hl : (ea x).length≤L := mem_length_le_code xs hx
    exact (r.output_length x).trans (Nat.add_le_add hl ((hp x).trans (p.eval_mono hl)))
  have hs := sum_map_bound xs (fun x => FramedMapRoutine.bodyTicks ea (fun x => eb (f x)) r.cost x+1)
    (3*L+p.eval L+6*(L+p.eval L)+8) (by
      intro x hx
      have hl : (ea x).length≤L := mem_length_le_code xs hx
      have hc := (hp x).trans (p.eval_mono hl)
      have hout := ho x hx
      simp only [FramedMapRoutine.bodyTicks,KS.W01.length_frame]
      omega)
  have ht := listCode_length_bound (ea:=fun x => eb (f x)) xs (L+p.eval L) ho
  have hs' := hs.trans (Nat.mul_le_mul_right _ hn)
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change FramedMapRoutine.ticks ea (fun x => eb (f x)) r.cost xs≤_
  simp only [FramedMapRoutine.ticks,FramedMapRoutine.scanTicks]
  change 2*L+2+((xs.map _).sum+1)+(listCode (fun x => eb (f x)) xs).length+1≤_
  change _≤2*L+L*(3*L+p.eval L+6*(L+p.eval L)+8)+L*(2*(L+p.eval L)+1)+4
  omega

lemma fold_scan_bound (F : α → β → α) (cost : α×β → ℕ) (s : α) (xs : List β) (S E C : ℕ)
    (hs : ∀ ys zs,xs=ys++zs → (ea (ys.foldl F s)).length≤S)
    (he : ∀ x∈xs,(eb x).length≤E)
    (hc : ∀ a x,(ea a).length≤S → (eb x).length≤E → cost (a,x)≤C) :
    FoldRoutine.scanTicks ea eb F cost s xs≤xs.length*(3*E+10*S+C+12)+1 := by
  induction xs generalizing s with
  | nil => simp [FoldRoutine.scanTicks]
  | cons x xs ih =>
      have h0 := hs [] (x::xs) rfl
      have h1 := hs [x] xs rfl
      have hx := he x (by simp)
      have hc0 := hc s x h0 hx
      have ht := ih (F s x) (by
        intro ys zs hz
        have h := hs (x::ys) zs (by simp only [List.cons_append];rw [hz])
        simpa only [List.foldl_cons] using h) (fun y hy => he y (by simp [hy]))
      simp only [FoldRoutine.scanTicks,FoldRoutine.bodyTicks,KS.W01.length_frame,List.length_cons,Nat.add_mul,Nat.one_mul]
      simp only [List.foldl_nil,List.foldl_cons] at h0 h1
      omega

instance poly_fold {f : α×β → α} (r : Realizes (prodCode ea eb) ea f) [PolyTime r] [FoldSize r] :
    PolyTime r.fold := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := FoldSize.bound (r:=r)
  refine ⟨⟨5*q+2*X+X*(3*X+10*q+p.comp (2*q+1+X)+12)+7,?_⟩⟩
  intro u
  let L := (prodCode ea (listCode eb) u).length
  let S := q.eval L
  have he : (listCode eb u.2).length≤L := le_prodCode_right u
  have hn := (list_length_le_code eb u.2).trans he
  have hs := hq u.1 u.2
  have h0 : (ea u.1).length≤S := hs [] u.2 rfl
  have hN : (ea (u.2.foldl (fun a b => f (a,b)) u.1)).length≤S := hs u.2 [] (by simp)
  have hc : ∀ a x,(ea a).length≤S → (eb x).length≤L → r.cost (a,x)≤p.eval (2*S+1+L) := by
    intro a x ha hx
    apply (hp (a,x)).trans (p.eval_mono ?_)
    rw [prodCode_length]
    dsimp only
    omega
  have hscan := fold_scan_bound (ea:=ea) (eb:=eb) (fun a b => f (a,b)) r.cost u.1 u.2 S L
    (p.eval (2*S+1+L)) hs (fun x hx => (mem_length_le_code u.2 hx).trans he) hc
  have hscan' := hscan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change FoldRoutine.ticks ea eb (fun a b => f (a,b)) r.cost u.1 u.2≤_
  simp only [FoldRoutine.ticks]
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change _≤5*S+2*L+L*(3*L+10*S+p.eval (2*S+1+L)+12)+7
  change _≤_ at hscan'
  change (FramedMapRoutine.tape eb u.2).length≤L at he
  omega

lemma iterate_ticks_bound {f : α → α} (r : Realizes ea ea f) (x : α) (n C : ℕ)
    (h : ∀ i,i<n → r.cost (f^[i] x)≤C) :
    IterateRoutine.loopTicks r.cost f n x≤n*(C+2)+1 := by
  induction n generalizing x with
  | zero => simp [IterateRoutine.loopTicks]
  | succ n ih =>
      have h0 := h 0 (by omega)
      have ht := ih (f x) (by
        intro i hi
        simpa only [←Function.iterate_succ_apply] using h (i+1) (by omega))
      simp only [Function.iterate_zero, id_eq] at h0
      simp only [IterateRoutine.loopTicks,Nat.add_mul,Nat.one_mul]
      omega
instance poly_iterate {f : α → α} (r : Realizes ea ea f) [PolyTime r] [IterateSize r] :
    PolyTime r.iterate := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := IterateSize.bound (r:=r)
  refine ⟨⟨3*X+X*(p.comp q+2)+3,?_⟩⟩
  intro u
  let L := (prodCode natCode ea u).length
  have hi : (ea u.2).length+u.1≤L := by simp only [L,prodCode_length,natCode,List.length_replicate];omega
  have hn : u.1≤L := by omega
  have ht := iterate_ticks_bound r u.2 u.1 (p.eval (q.eval L)) (by
    intro i hi'
    exact (hp _).trans (p.eval_mono ((hq u.2 i).trans (q.eval_mono (by omega)))))
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change 3*u.1+2+IterateRoutine.loopTicks r.cost f u.1 u.2≤3*L+L*(p.eval (q.eval L)+2)+3
  omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NegativeWitness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem quadratic_single {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single i 1) = M i i := by
  simp [single_dotProduct]

theorem negativeDiagonal_witness {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i : Fin n) (hi : M i i < 0) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single i 1) < 0 := by
  simpa only [quadratic_single] using hi

theorem quadratic_twoSingle {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (a b : ℚ) :
    (Pi.single i a + Pi.single j b) ⬝ᵥ (M *ᵥ (Pi.single i a + Pi.single j b)) =
      a * (M i i * a + M i j * b) + b * (M j i * a + M j j * b) := by
  simp only [add_dotProduct, single_dotProduct, Matrix.mulVec,
    dotProduct_add, dotProduct_single]

theorem zeroPivotWitness_value {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (hii : M i i = 0) (hij : M i j ≠ 0)
    (hsymm : M j i = M i j) :
    zeroPivotWitness M i j ⬝ᵥ (M *ᵥ zeroPivotWitness M i j) = -1 := by
  unfold zeroPivotWitness
  rw [quadratic_twoSingle, hii, hsymm]
  field_simp [hij]
  ring

theorem zeroPivotWitness_negative {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (hii : M i i = 0) (hij : M i j ≠ 0)
    (hsymm : M j i = M i j) :
    zeroPivotWitness M i j ⬝ᵥ (M *ᵥ zeroPivotWitness M i j) < 0 := by
  rw [zeroPivotWitness_value M i j hii hij hsymm]
  decide

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RationalElimination
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

theorem trailingMatrix_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (trailingMatrix M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact hM.apply i.succ j.succ

theorem schurTail_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (schurTail M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [schurTail]
  rw [hM.apply i.succ j.succ, hM.apply 0 j.succ, hM.apply 0 i.succ]
  rw [mul_comm (M 0 j.succ) (M 0 i.succ)]

theorem firstNonzeroOffDiagonal_some {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (j : Fin n)
    (h : firstNonzeroOffDiagonal M = some j) : M 0 j.succ ≠ 0 := by
  have hj := List.find?_some h
  simpa using hj

theorem firstNonzeroOffDiagonal_none_iff {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    firstNonzeroOffDiagonal M = none ↔ ∀ j : Fin n, M 0 j.succ = 0 := by
  simp [firstNonzeroOffDiagonal, List.find?_eq_none]

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArrayRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α γ : Type*}

lemma fold_length (xs : List α) (n : ℕ) : xs.foldl (fun k _ => k+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_comm,Nat.add_left_comm]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLists
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma prefix_code_length (ea : α → Word) (xs ys zs : List α) (h : xs=ys++zs) :
    (listCode ea ys).length≤(listCode ea xs).length := by
  rw [h,listCode_append,List.length_append];omega
lemma prefix_length (xs ys zs : List α) (h : xs=ys++zs) : ys.length≤xs.length := by
  rw [h,List.length_append];omega

instance poly_appendList (ea : α → Word) : PolyTime (appendList ea) := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 5 (le_prodCode_left p)) 4
instance poly_reverseBody (ea : α → Word) : PolyTime (reverseBody ea) := by
  unfold reverseBody;infer_instance
instance size_reverseBody (ea : α → Word) : FoldSize (reverseBody ea) := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_cons,listCode_append,List.length_append,listCode_reverse_length]
  have hp := prefix_code_length ea xs ys zs h
  change _≤(prodCode (listCode ea) (listCode ea) (s,xs)).length
  rw [prodCode_length]
  try dsimp only
  omega
instance poly_reverseList (ea : α → Word) : PolyTime (reverseList ea) := by
  unfold reverseList;infer_instance

instance poly_mapCtxBody {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime (mapCtxBody ec ea eb r) := by
  dsimp only [mapCtxBody]
  apply poly_both
instance size_mapCtxBody {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    FoldSize (mapCtxBody ec ea eb r) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let U := 3*X+1+p.comp (3*X+1)
  refine ⟨⟨3*X+1+X*(2*U+1),?_⟩⟩
  intro s xs ys zs h
  rw [fold_mapCtx]
  let L := (prodCode (prodCode ec (listCode eb)) (listCode ea) (s,xs)).length
  have hc : (ec s.1).length≤L := (le_prodCode_left s).trans (le_prodCode_left (s,xs))
  have ha : (listCode eb s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have he : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have hn : ys.length≤L := (list_length_le_code ea ys).trans he
  have ho : ∀ x∈ys,(eb (f (s.1,x))).length≤3*L+1+p.eval (3*L+1) := by
    intro x hx
    have hl : (prodCode ec ea (s.1,x)).length≤3*L+1 := by
      have he' := (mem_length_le_code ys hx).trans he
      simp only [prodCode_length]
      try dsimp only
      omega
    exact (r.output_length (s.1,x)).trans (Nat.add_le_add hl ((hp _).trans (p.eval_mono hl)))
  have hm := listCode_length_bound (ea:=fun x => eb (f (s.1,x))) ys (3*L+1+p.eval (3*L+1)) ho
  have hm' := hm.trans (Nat.mul_le_mul_right _ hn)
  have heq : listCode eb (ys.map (fun x => f (s.1,x)))=listCode (fun x => eb (f (s.1,x))) ys := by
    simp only [listCode,FramedMapRoutine.tape,List.flatMap_map]
  rw [prodCode_length]
  dsimp only
  rw [listCode_append,List.length_append,listCode_reverse_length,heq]
  change 2*(ec s.1).length+1+((listCode (fun x => eb (f (s.1,x))) ys).length+(listCode eb s.2).length)≤_
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp,U]
  change _≤3*L+1+L*(2*(3*L+1+p.eval (3*L+1))+1)
  omega
instance poly_mapCtx {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime r.mapCtx := by
  unfold Realizes.mapCtx
  infer_instance

instance poly_natAdd : PolyTime natAdd := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  have h := le_prodCode_left (ea:=natCode) (eb:=natCode) p
  simp only [natCode,List.length_replicate] at h
  change 5*p.1+4≤5*(prodCode natCode natCode p).length+4
  omega

instance poly_rangeStep : PolyTime rangeStepRealizes := by dsimp only [rangeStepRealizes];apply poly_both
lemma range_iterate_size (s : ℕ×List ℕ) (k : ℕ) :
    (rangeStep^[k] s).1=s.1+k ∧
    (listCode natCode (rangeStep^[k] s).2).length≤(listCode natCode s.2).length+k*(2*(s.1+k)+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change (rangeStep^[k] s).1+1=s.1+(k+1) ∧ _
      constructor
      · omega
      · change (listCode natCode ((rangeStep^[k] s).1::(rangeStep^[k] s).2)).length≤_
        rw [listCode_cons,prodCode_length]
        simp only [natCode,List.length_replicate]
        try dsimp only
        nlinarith [ih.2]
instance size_rangeStep : IterateSize rangeStepRealizes := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s k
  have h := range_iterate_size s k
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*(rangeStep^[k] s).1+1+(listCode natCode (rangeStep^[k] s).2).length≤10*(2*s.1+1+(listCode natCode s.2).length+k+1)^2
  rw [h.1]
  nlinarith [h.2]
instance poly_range : PolyTime range := by unfold range;infer_instance

instance poly_lengthBody (ea : α → Word) : PolyTime ((first natCode ea).then natSucc) := by infer_instance
instance size_lengthBody (ea : α → Word) : FoldSize ((first natCode ea).then natSucc) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  change (natCode (ys.foldl (fun k _ => k+1) s)).length≤_
  rw [fold_length]
  have hs := le_prodCode_left (ea:=natCode) (eb:=listCode ea) (s,xs)
  have hn := ((prefix_length xs ys zs h).trans (list_length_le_code ea xs)).trans (le_prodCode_right (ea:=natCode) (s,xs))
  simp only [natCode,List.length_replicate] at hs ⊢
  change s+ys.length≤2*(prodCode natCode (listCode ea) (s,xs)).length
  omega
instance poly_lengthList (ea : α → Word) : PolyTime (lengthList ea) := by unfold lengthList;infer_instance
instance poly_tabulate {f : γ×ℕ → α} (r : Realizes (prodCode ec natCode) ea f) [PolyTime r] :
    PolyTime r.tabulate := by unfold Realizes.tabulate;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialScalar
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

instance poly_ratOp (op : KS.W13.ExpressionMachine.BinaryOp) : PolyTime (ratOp op) := by
  refine ⟨⟨5*X+6000000*(X+1)^3+6,?_⟩⟩
  intro p
  have hl := RoutineLength.output_length (KS.W13.ExpressionMachine.binaryArithmetic_spec op p.1 p.2 [] []) 10
  have ht : (ratCode (op.eval p.1 p.2)).length≤KS.W13.ExpressionMachine.binaryBudget p.1 p.2 := by simpa [KS.W13.ExpressionMachine.registers] using hl
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 3
  have ha := le_prodCode_left (ea:=ratCode) (eb:=ratCode) p
  change ArithmeticRoutine.ticks op p.1 p.2≤5*(prodCode ratCode ratCode p).length+6000000*((prodCode ratCode ratCode p).length+1)^3+6
  simp only [ArithmeticRoutine.ticks,ArithmeticRoutine.encode,KS.W13.ExpressionMachine.binaryBudget,KS.W01.ratLength] at ht ⊢
  simp only [ratCode] at *
  omega

instance poly_ratLE : PolyTime ratLE := by
  refine ⟨⟨5*X+2048*(X+1)^2+8,?_⟩⟩
  intro p
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2
  have ha := le_prodCode_left (ea:=ratCode) (eb:=ratCode) p
  change CompareRoutine.ticks p.1 p.2≤5*(prodCode ratCode ratCode p).length+2048*((prodCode ratCode ratCode p).length+1)^2+8
  simp only [CompareRoutine.ticks,CompareRoutine.encode,KS.W29.polynomialFuel,List.length_append]
  simp only [ratCode] at *
  omega

instance poly_ratFloor : PolyTime ratFloor := by
  refine ⟨⟨192*(X+1)^2+2,?_⟩⟩
  intro q
  have hl := RoutineLength.output_length (KS.W20.FloorRationalMachine.polynomial_spec q) 5
  have ht : (ratCode (⌊q⌋ : ℚ)).length≤64*((ratCode q).length+1)^2 := by
    simpa [KS.W20.FloorRationalMachine.state,KS.W19.SignedFloorMachine.«stacks»,KS.W29.polynomialFuel] using hl
  change FloorCleanRoutine.ticks q≤192*((ratCode q).length+1)^2+2
  simp only [FloorCleanRoutine.ticks,KS.W29.polynomialFuel,FloorCleanRoutine.encode]
  simp only [ratCode] at *
  omega

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
instance poly_conditional {f g : α → β} (r : Realizes ea eb f) (s : Realizes ea eb g)
    [PolyTime r] [PolyTime s] : PolyTime (conditional r s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q+6,?_⟩⟩
  intro x
  have hr := (hp x.2).trans (p.eval_mono (le_prodCode_right (ea:=boolCode) (eb:=ea) x))
  have hs := (hq x.2).trans (q.eval_mono (le_prodCode_right (ea:=boolCode) (eb:=ea) x))
  change 5+(if x.1 then r.cost x.2 else s.cost x.2)+1≤p.eval _+q.eval _+6
  split <;> omega
instance poly_ite {p : α → Bool} {f g : α → β} (b : Realizes ea boolCode p)
    (r : Realizes ea eb f) (s : Realizes ea eb g) [PolyTime b] [PolyTime r] [PolyTime s] : PolyTime (b.ite r s) := by unfold Realizes.ite; exact poly_then (b.both (identity ea)) (conditional r s)
instance poly_add {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.add s) := by unfold Realizes.add; exact poly_then (r.both s) (ratOp .add)
instance poly_sub {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.sub s) := by unfold Realizes.sub; exact poly_then (r.both s) (ratOp .sub)
instance poly_mul {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.mul s) := by unfold Realizes.mul; exact poly_then (r.both s) (ratOp .mul)
instance poly_div {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.div s) := by unfold Realizes.div; exact poly_then (r.both s) (ratOp .div)
instance poly_le {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.le s) := by unfold Realizes.le;infer_instance
instance poly_neg {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.neg := by unfold Realizes.neg;infer_instance
instance poly_abs {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.abs := by unfold Realizes.abs;infer_instance
instance poly_roundScalar : PolyTime roundScalar := by unfold roundScalar;infer_instance
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialArrays
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma fold_add_eq (xs : List ℚ) (q : ℚ) : xs.foldl (fun a b => a+b) q=q+xs.sum := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih => simp [ih,add_assoc]
lemma rat_sum_lengths_le (xs : List ℚ) :
    (xs.map KS.W01.ratLength).sum+xs.length≤(listCode ratCode xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,listCode_cons,prodCode_length]
      change KS.W01.ratLength x+_+_≤2*KS.W01.ratLength x+1+_
      omega
instance size_ratAdd : FoldSize (ratOp .add) := by
  refine ⟨⟨40*X+40,?_⟩⟩
  intro s xs ys zs h
  change (ratCode (ys.foldl (fun a b => a+b) s)).length≤_
  rw [fold_add_eq]
  have h1 := KS.W01.ratLength_sum_le ys
  have h2 := KS.W01.ratLength_add_le s ys.sum
  have hs := le_prodCode_left (ea:=ratCode) (eb:=listCode ratCode) (s,xs)
  have hy := (rat_sum_lengths_le ys).trans ((prefix_code_length ratCode xs ys zs h).trans
    (le_prodCode_right (ea:=ratCode) (s,xs)))
  change KS.W01.ratLength s≤_ at hs
  change KS.W01.ratLength (s+ys.sum)≤40*(prodCode ratCode (listCode ratCode) (s,xs)).length+40
  omega
instance poly_sumRationals : PolyTime sumRationals := by
  unfold sumRationals
  apply poly_congr
instance poly_l1Rationals : PolyTime l1Rationals := by unfold l1Rationals;apply poly_then

instance poly_lookupStep (ea : α → Word) : PolyTime (lookupStepRealizes ea) := by
  dsimp only [lookupStepRealizes]
  apply poly_congr
lemma lookup_fold_size (ea : α → Word) (s : ℕ×α) (xs : List α) (K B : ℕ)
    (hk : s.1≤K) (ha : (ea s.2).length≤B) (hx : ∀x∈xs,(ea x).length≤B) :
    (xs.foldl (fun s x => lookupStep (s,x)) s).1≤K ∧
    (ea (xs.foldl (fun s x => lookupStep (s,x)) s).2).length≤B := by
  induction xs generalizing s with
  | nil => exact ⟨hk,ha⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih
      · dsimp only [lookupStep]
        split_ifs <;> (try dsimp only) <;> omega
      · dsimp only [lookupStep]
        split_ifs <;> try dsimp only
        · exact ha
        · exact hx x (by simp)
        · exact ha
      · intro y hy;exact hx y (by simp [hy])
instance size_lookupStep (ea : α → Word) : FoldSize (lookupStepRealizes ea) := by
  refine ⟨⟨3*X+1,?_⟩⟩
  intro s xs ys zs h
  let L := (prodCode (prodCode natCode ea) (listCode ea) (s,xs)).length
  have hk : s.1≤L := by
    have hl := (le_prodCode_left (ea:=natCode) (eb:=ea) s).trans (le_prodCode_left (eb:=listCode ea) (s,xs))
    simpa only [natCode,List.length_replicate] using hl
  have ha : (ea s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have hy : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have ht := lookup_fold_size ea s ys L L hk ha (fun x hx => (mem_length_le_code ys hx).trans hy)
  change (prodCode natCode ea _).length≤3*L+1
  rw [prodCode_length]
  simp only [natCode,List.length_replicate]
  omega
instance poly_getD (ea : α → Word) (a : α) : PolyTime (getD ea a) := by unfold getD;infer_instance

instance poly_zipWith {f : α×β → γ} (r : Realizes (prodCode ea eb) ec f) (a : α) (b : β)
    [PolyTime r] : PolyTime (r.zipWith a b) := by unfold Realizes.zipWith;apply poly_then
instance poly_vectorAdd : PolyTime vectorAdd := by unfold vectorAdd;infer_instance
instance poly_vectorScaleBody : PolyTime vectorScaleBody := by unfold vectorScaleBody;exact poly_ratOp .mul
instance poly_vectorScale : PolyTime vectorScale := by unfold vectorScale;infer_instance
instance poly_matrixAdd : PolyTime matrixAdd := by unfold matrixAdd;infer_instance
instance poly_matrixScale : PolyTime matrixScale := by unfold matrixScale;infer_instance
instance poly_dot : PolyTime dot := by unfold dot;apply poly_then
instance poly_matVec : PolyTime matVec := by unfold matVec;apply poly_then
instance poly_quadratic : PolyTime quadratic := by unfold quadratic;apply poly_then

lemma ratLength_natCast (n : ℕ) : KS.W01.ratLength (n : ℚ)≤4*n+11 := by
  apply (KS.W01.ratLength_le_of_parts (n : ℚ) n n ?_ ?_).trans (by omega)
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n)))
  · simpa only [Rat.den_natCast] using (Nat.one_le_two_pow (n:=n))
instance size_ratSucc : IterateSize ((identity ratCode).add (constant ratCode ratCode 1)) := by
  refine ⟨⟨20*X+60,?_⟩⟩
  intro q n
  change (ratCode ((fun x : ℚ => x+1)^[n] q)).length≤_
  rw [iterate_ratSucc]
  have h := KS.W01.ratLength_add_le q (n : ℚ)
  have hn := ratLength_natCast n
  change KS.W01.ratLength (q+(n : ℚ))≤20*(KS.W01.ratLength q+n)+60
  omega
instance poly_natToRat : PolyTime natToRat := by unfold natToRat;infer_instance
instance size_natMulStep : IterateSize ((first natCode natCode).both natAdd) := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s n
  change (prodCode natCode natCode ((fun a : ℕ×ℕ => (a.1,a.1+a.2))^[n] s)).length≤_
  rcases s with ⟨k,z⟩
  rw [fold_natAdd]
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*k+1+(n*k+z)≤10*(2*k+1+z+n+1)^2
  nlinarith
instance poly_natMul : PolyTime natMul := by unfold natMul;infer_instance
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratFloor _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {ι α β γ : Type*} {L f g : ι → ℕ}

lemma IsPoly.mono (hf : IsPoly L f) (h : ∀i,g i≤f i) : IsPoly L g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => (h i).trans (hp i)⟩
lemma IsPoly.add (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i+g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun i => Nat.add_le_add (hp i) (hq i)⟩
lemma IsPoly.mul (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i*g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun i => Nat.mul_le_mul (hp i) (hq i)⟩
lemma IsPoly.pow (hf : IsPoly L f) (k : ℕ) : IsPoly L (fun i => (f i)^k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k,fun i => Nat.pow_le_pow_left (hp i) k⟩
lemma isPoly_const (L : ι → ℕ) (c : ℕ) : IsPoly L (fun _ => c) := ⟨.constant c,fun _ => le_rfl⟩
lemma isPoly_self (L : ι → ℕ) : IsPoly L L := ⟨X,fun _ => le_rfl⟩
lemma IsPoly.eval (hf : IsPoly L f) (p : NaturalPolynomial) : IsPoly L (fun i => p.eval (f i)) := by
  obtain ⟨q,hq⟩ := hf
  exact ⟨p.comp q,fun i => by simpa only [NaturalPolynomial.eval_comp] using p.eval_mono (hq i)⟩
lemma IsPoly.reindex {κ : Type*} (hf : IsPoly L f) (a : κ → ι) : IsPoly (L ∘ a) (f ∘ a) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => hp (a i)⟩

variable {ea : α → Word} {eb : β → Word} {ec : γ → Word} {F : α → β} {G : β → γ}

lemma RunsPoly.of_poly (r : Realizes ea eb F) [PolyTime r] (a : ι → α)
    (h : IsPoly L (fun i => (ea (a i)).length)) : RunsPoly L r a := by
  refine ⟨h,?_⟩
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  exact (h.eval p).mono (fun i => hp (a i))
lemma RunsPoly.output {r : Realizes ea eb F} {a : ι → α} (h : RunsPoly L r a) :
    IsPoly L (fun i => (eb (F (a i))).length) := (h.input.add h.cost).mono (fun i => r.output_length (a i))
lemma RunsPoly.then {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s (fun i => F (a i))) : RunsPoly L (r.then s) a :=
  ⟨hr.input,hr.cost.add hs.cost⟩
lemma RunsPoly.congr {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {F' : α → β} (h : ∀x,F x=F' x) : RunsPoly L (r.congr h) a := by
  have he : F=F' := funext h
  subst F'
  exact hr
lemma Realizes.congr_cost {r : Realizes ea eb F} {F' : α → β} (h : ∀x,F x=F' x) :
    (r.congr h).cost=r.cost := by
  have he : F=F' := funext h
  subst F'
  rfl
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCeiling
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratFloor _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_ratAdd _root_.OAI.CurrentKS.Realization.size_ratSucc _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

lemma ratNumToNat_cost : ∃ p : NaturalPolynomial,∀q,
    ratNumToNat.cost q≤p.eval (ratCode q).length+6*q.num.toNat := by
  have : PolyTime ratLE := by
    refine ⟨⟨5*X+2048*(X+1)^2+8,?_⟩⟩
    intro input
    have hinput : (ratCode input.1).length+(ratCode input.2).length ≤
        (prodCode ratCode ratCode input).length := by rw [prodCode_length];omega
    have hpower := Nat.pow_le_pow_left (Nat.add_le_add_right hinput 1) 2
    have hleft := le_prodCode_left (ea:=ratCode) (eb:=ratCode) input
    change CompareRoutine.ticks input.1 input.2≤5*(prodCode ratCode ratCode input).length+
      2048*((prodCode ratCode ratCode input).length+1)^2+8
    simp only [CompareRoutine.ticks,CompareRoutine.encode,KS.W29.polynomialFuel,List.length_append]
    simp only [ratCode] at *
    omega
  let cmp := ((constant ratCode ratCode 0).le (identity ratCode)).both (identity ratCode)
  have : PolyTime cmp := by dsimp [cmp,Realizes.le];infer_instance
  have : PolyTime wordTail := ⟨⟨1,fun _ => le_rfl⟩⟩
  have : PolyTime ratNumBinary := by unfold ratNumBinary ratFields;infer_instance
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=cmp)
  obtain ⟨r,hr⟩ := PolyTime.bound (r:=ratNumBinary)
  refine ⟨p+5*r+5*X+20,?_⟩
  intro q
  have hcost := hp q
  have hn := hr q
  have ho := ratNumBinary.output_length q
  have hz : (natCode 0).length=0 := rfl
  have hc : (conditional (ratNumBinary.then binaryToNat) (constant ratCode natCode 0)).cost
      (decide (0≤q),q) ≤ 5*r.eval (ratCode q).length+5*(ratCode q).length+20+6*q.num.toNat := by
    change 5+(if decide (0≤q) then ratNumBinary.cost q+(6*KS.W01.intPayload q.num+4*(binaryNatCode (KS.W01.intPayload q.num)).length+4)
      else (ratCode q).length+1+((natCode 0).length+1))+1≤_
    by_cases hq : 0≤q
    · have he : KS.W01.intPayload q.num=q.num.toNat := by
        have hnum := Rat.num_nonneg.mpr hq
        cases hh : q.num with
        | ofNat n => rfl
        | negSucc n => rw [hh] at hnum;omega
      simp only [hq,decide_true,↓reduceIte,he]
      change (binaryNatCode (KS.W01.intPayload q.num)).length≤_ at ho
      rw [he] at ho
      omega
    · simp only [hq,decide_false,Bool.false_eq_true,↓reduceIte,hz]
      omega
  unfold ratNumToNat
  rw [Realizes.congr_cost]
  change cmp.cost q+(conditional (ratNumBinary.then binaryToNat) (constant ratCode natCode 0)).cost (decide (0≤q),q)≤p.eval (ratCode q).length+5*r.eval (ratCode q).length+5*(ratCode q).length+20+6*q.num.toNat
  omega

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_ratNumToNat (a : ι → ℚ) (ha : IsPoly L (fun i => (ratCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).num.toNat)) : RunsPoly L ratNumToNat a := by
  obtain ⟨p,hp⟩ := ratNumToNat_cost
  exact ⟨ha,((ha.eval p).add ((isPoly_const L 6).mul hn)).mono (fun i => hp (a i))⟩
lemma runsPoly_ratCeil (a : ι → ℚ) (ha : IsPoly L (fun i => (ratCode (a i)).length))
    (hn : IsPoly L (fun i => ⌈a i⌉₊)) : RunsPoly L ratCeil a := by
  unfold ratCeil
  apply RunsPoly.congr
  have : PolyTime (ratOp .sub) := by
    refine ⟨⟨5*X+6000000*(X+1)^3+6,?_⟩⟩
    intro input
    have hlength := RoutineLength.output_length
      (KS.W13.ExpressionMachine.binaryArithmetic_spec .sub input.1 input.2 [] []) 10
    have houtput : (ratCode (KS.W13.ExpressionMachine.BinaryOp.sub.eval input.1 input.2)).length≤
        KS.W13.ExpressionMachine.binaryBudget input.1 input.2 := by
      simpa [KS.W13.ExpressionMachine.registers] using hlength
    have hinput : (ratCode input.1).length+(ratCode input.2).length ≤
        (prodCode ratCode ratCode input).length := by rw [prodCode_length];omega
    have hpower := Nat.pow_le_pow_left (Nat.add_le_add_right hinput 1) 3
    have hleft := le_prodCode_left (ea:=ratCode) (eb:=ratCode) input
    change ArithmeticRoutine.ticks .sub input.1 input.2≤5*(prodCode ratCode ratCode input).length+
      6000000*((prodCode ratCode ratCode input).length+1)^3+6
    simp only [ArithmeticRoutine.ticks,ArithmeticRoutine.encode,
      KS.W13.ExpressionMachine.binaryBudget,KS.W01.ratLength] at houtput ⊢
    simp only [ratCode] at *
    omega
  have : PolyTime ratFloor := by
    refine ⟨⟨192*(X+1)^2+2,?_⟩⟩
    intro input
    have hlength := RoutineLength.output_length (KS.W20.FloorRationalMachine.polynomial_spec input) 5
    have houtput : (ratCode (⌊input⌋ : ℚ)).length≤64*((ratCode input).length+1)^2 := by
      simpa [KS.W20.FloorRationalMachine.state,KS.W19.SignedFloorMachine.«stacks»,
        KS.W29.polynomialFuel] using hlength
    change FloorCleanRoutine.ticks input≤192*((ratCode input).length+1)^2+2
    simp only [FloorCleanRoutine.ticks,KS.W29.polynomialFuel,FloorCleanRoutine.encode]
    simp only [ratCode] at *
    omega
  let pre := ((identity ratCode).neg.then ratFloor).neg
  have : PolyTime pre := by
    dsimp only [pre, Realizes.neg, Realizes.sub]
    refine @poly_congr _ _ _ _ _ _ _ _ ?_
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · infer_instance
      · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
        · refine @poly_congr _ _ _ _ _ _ _ _ ?_
          refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
          · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_ <;> infer_instance
          · assumption
        · assumption
    · assumption
  have hp := RunsPoly.of_poly pre a ha
  apply hp.then
  apply runsPoly_ratNumToNat _ hp.output
  simpa only [id_eq,Int.floor_neg,Int.cast_neg,neg_neg,Rat.num_intCast,Int.ceil_toNat] using hn
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealDecode
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.HermitianCoordinates
open Matrix
open scoped BigOperators

variable {d : ℕ}

lemma realDecode_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (x : Fin d × Fin d → R) : (realDecode x).map f=realDecode (f ∘ x) := by
  ext i j
  cases i <;> cases j <;>
    simp only [realDecode_inl_inl, realDecode_inl_inr, realDecode_inr_inl, realDecode_inr_inr, Matrix.map_apply,
      Function.comp_def,map_neg]
  all_goals split_ifs <;> simp only [map_neg,map_zero]

lemma realDecode_ratCast (x : Fin d × Fin d → ℚ) :
    (realDecode x).map (fun q => (q:ℝ))=realDecode (fun i => (x i:ℝ)) :=
  realDecode_map (algebraMap ℚ ℝ) x
end CurrentKS.HermitianCoordinates

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Pivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

section TrivialStar

variable [StarRing K] [TrivialStar K]

omit [Fintype n] [DecidableEq n] in
theorem pivot_schur_formula {a : K} (ha : a ≠ 0)
    (b : n → K) (D : Matrix n n K) :
    D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
      (pivotRow b) = pivotSchur a b D := by
  ext i j
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, pivotSchur]
  ring

omit [DecidableEq n] [StarRing K] [TrivialStar K] in
theorem pivot_lift_cancel {a : K} (ha : a ≠ 0) (b y : n → K) :
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) +
      ((scalarPivot a)⁻¹ * (pivotRow b)) *ᵥ y = 0 := by
  ext u
  cases u
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] in
theorem pivotWitnessLift_quadratic {a : K} (ha : a ≠ 0)
    (b y : n → K) (D : Matrix n n K) :
    pivotWitnessLift a b y ⬝ᵥ (pivotBlock a b D *ᵥ pivotWitnessLift a b y) =
      y ⬝ᵥ (pivotSchur a b D *ᵥ y) := by
  let := scalarPivotInvertible ha
  have hA : (scalarPivot a).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [scalarPivot]
  have h := Matrix.schur_complement_eq₁₁
    (pivotRow b) D
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) y hA
  rw [pivot_lift_cancel ha, pivot_schur_formula ha] at h
  have hblock : Matrix.fromBlocks (scalarPivot a) (pivotRow b) (pivotRow b)ᴴ D =
      pivotBlock a b D := by
    ext i j
    cases i <;> cases j <;> simp [pivotBlock, pivotRow, Matrix.fromBlocks]
  rw [hblock] at h
  simpa only [← Matrix.dotProduct_mulVec, star_trivial, Matrix.zero_mulVec,
    zero_dotProduct, zero_add, pivotWitnessLift] using h

end TrivialStar

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

theorem quadratic_submatrix_equiv {n m K : Type*} [Fintype n] [Fintype m]
    [CommSemiring K] (M : Matrix n n K) (x : n → K) (e : m ≃ n) :
    (x ∘ e) ⬝ᵥ (M.submatrix e e *ᵥ (x ∘ e)) = x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.submatrix_mulVec_equiv]
  have hc : (x ∘ e) ∘ e.symm = x := by funext i; simp
  rw [hc]
  exact comp_equiv_dotProduct_comp_equiv x (M *ᵥ x) e

theorem fin_pivotBlock {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : M.IsSymm) :
    M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n) =
      pivotBlock (M 0 0) (fun i => M 0 i.succ) (KS.W17.trailingMatrix M) := by
  ext i j
  cases i with
  | inl i => cases i; cases j <;> rfl
  | inr i =>
    cases j with
    | inl j => cases j; exact hM.apply 0 i.succ
    | inr j => rfl

theorem fin_pivotSchur {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : M.IsSymm) :
    pivotSchur (M 0 0) (fun i => M 0 i.succ) (KS.W17.trailingMatrix M) =
      KS.W17.schurTail M := by
  ext i j
  simp only [pivotSchur, KS.W17.schurTail, KS.W17.trailingMatrix, hM.apply 0 i.succ]

theorem fin_pivotWitnessLift {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    KS.W17.schurWitnessLift M y ∘ pivotIndexEquiv n =
      pivotWitnessLift (M 0 0) (fun i => M 0 i.succ) y := by
  funext i
  cases i with
  | inl i =>
    cases i
    simp [pivotIndexEquiv, KS.W17.schurWitnessLift,
      pivotWitnessLift, div_eq_mul_inv, mul_comm]
  | inr i => rfl

theorem fin_schurWitnessLift_quadratic {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : M 0 0 ≠ 0) (y : Fin n → ℚ) :
    KS.W17.schurWitnessLift M y ⬝ᵥ (M *ᵥ KS.W17.schurWitnessLift M y) =
      y ⬝ᵥ (KS.W17.schurTail M *ᵥ y) := by
  rw [← quadratic_submatrix_equiv M (KS.W17.schurWitnessLift M y) (pivotIndexEquiv n),
    fin_pivotBlock M hM, fin_pivotWitnessLift M y,
    pivotWitnessLift_quadratic ha, fin_pivotSchur M hM]

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PSDSeparation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem psdCutEvalReal_cast {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) :
    psdCutEvalReal q (fun i j => (M i j : ℝ)) = (psdCutEval q M : ℝ) := by
  simp [psdCutEvalReal, psdCutEval, dotProduct, Matrix.mulVec,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_neg]

theorem psdCutEvalReal_nonpos {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) :
    psdCutEvalReal q M ≤ 0 := by
  have h := hM.dotProduct_mulVec_nonneg (fun i => (q i : ℝ))
  simpa [psdCutEvalReal] using neg_nonpos.mpr h

theorem psdWitness_separates {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hneg : q ⬝ᵥ (M *ᵥ q) < 0) :
    0 < psdCutEvalReal q (fun i j => (M i j : ℝ)) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef → psdCutEvalReal q B ≤ 0 := by
  constructor
  · rw [psdCutEvalReal_cast]
    have hr : 0 < psdCutEval q M := neg_pos.mpr hneg
    exact_mod_cast hr
  · exact fun B hB => psdCutEvalReal_nonpos q B hB

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_EliminationSoundness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem quadratic_zero_cons {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    Fin.cons 0 y ⬝ᵥ (M *ᵥ Fin.cons 0 y) = y ⬝ᵥ (trailingMatrix M *ᵥ y) := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, trailingMatrix]

theorem rationalNegativeWitness_sound (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) (q : Fin n → ℚ)
    (hout : rationalNegativeWitness n M = some q) : q ⬝ᵥ (M *ᵥ q) < 0 := by
  induction n with
  | zero => simp [rationalNegativeWitness] at hout
  | succ n ih =>
      by_cases hnegative : M 0 0 < 0
      · have hq : Pi.single 0 1 = q := by
          simpa [rationalNegativeWitness, hnegative] using hout
        subst q
        exact negativeDiagonal_witness M 0 hnegative
      · by_cases hzero : M 0 0 = 0
        · cases hfind : firstNonzeroOffDiagonal M with
          | some j =>
              have hq : zeroPivotWitness M 0 j.succ = q := by
                simpa [rationalNegativeWitness, hnegative, hzero, hfind] using hout
              subst q
              exact zeroPivotWitness_negative M 0 j.succ hzero
                (firstNonzeroOffDiagonal_some M j hfind) (hM.apply 0 j.succ)
          | none =>
              cases hrec : rationalNegativeWitness n (trailingMatrix M) with
              | none =>
                  simp [rationalNegativeWitness, hzero, hfind, hrec] at hout
              | some y =>
                  have hq : Fin.cons 0 y = q := by
                    simpa [rationalNegativeWitness, hnegative, hzero, hfind, hrec] using hout
                  subst q
                  rw [quadratic_zero_cons]
                  exact ih (trailingMatrix M) (trailingMatrix_isSymm M hM) y hrec
        · cases hrec : rationalNegativeWitness n (schurTail M) with
          | none =>
              simp [rationalNegativeWitness, hnegative, hzero, hrec] at hout
          | some y =>
              have hq : schurWitnessLift M y = q := by
                simpa [rationalNegativeWitness, hnegative, hzero, hrec] using hout
              subst q
              rw [KS.W07.fin_schurWitnessLift_quadratic M hM hzero y]
              exact ih (schurTail M) (schurTail_isSymm M hM) y hrec

theorem computedPSDSeparator_separates (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) (q : Fin n → ℚ)
    (hout : rationalNegativeWitness n M = some q) :
    0 < psdCutEvalReal q (fun i j => (M i j : ℝ)) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef → psdCutEvalReal q B ≤ 0 :=
  psdWitness_separates q M (rationalNegativeWitness_sound n M hM q hout)

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotPSD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

open Matrix

variable {n : Type*} [Fintype n]

theorem scalarPivot_posDef {a : ℝ} (ha : 0 < a) : (scalarPivot a).PosDef := by
  have heq : scalarPivot a = Matrix.diagonal (fun _ : Unit => a) := by
    ext i j
    cases i; cases j
    simp [scalarPivot]
  rw [heq]
  exact Matrix.PosDef.diagonal (fun _ => ha)

omit [Fintype n] in
theorem real_pivot_schur_formula {a : ℝ} (ha : a ≠ 0)
    (b : n → ℝ) (D : Matrix n n ℝ) :
    D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
      (pivotRow b) = pivotSchur a b D :=
  pivot_schur_formula ha b D

theorem pivotSchur_posSemidef {a : ℝ} (ha : 0 < a)
    (b : n → ℝ) (D : Matrix n n ℝ) (hM : (pivotBlock a b D).PosSemidef) :
    (pivotSchur a b D).PosSemidef := by
  let _ := scalarPivotInvertible (ne_of_gt ha)
  have hM' : (Matrix.fromBlocks (scalarPivot a)
      (pivotRow b)
      (pivotRow b)ᴴ D).PosSemidef := by
    exact hM
  have h := (Matrix.PosDef.fromBlocks₁₁
    (pivotRow b) D (scalarPivot_posDef ha)).mp hM'
  exact real_pivot_schur_formula (ne_of_gt ha) b D ▸ h

omit [Fintype n] in
theorem rat_pivotSchur_cast (a : ℚ) (b : n → ℚ) (D : Matrix n n ℚ) :
    (pivotSchur a b D).map (fun q : ℚ => (q : ℝ)) =
      pivotSchur (a : ℝ) (fun i => (b i : ℝ)) (D.map (fun q : ℚ => (q : ℝ))) := by
  ext i j
  simp [pivotSchur]

omit [Fintype n] in
theorem rat_pivotBlock_cast (a : ℚ) (b : n → ℚ) (D : Matrix n n ℚ) :
    (pivotBlock a b D).map (fun q : ℚ => (q : ℝ)) =
      pivotBlock (a : ℝ) (fun i => (b i : ℝ)) (D.map (fun q : ℚ => (q : ℝ))) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem pivotBlock_posSemidef_iff {a : ℝ} (ha : 0 < a)
    (b : n → ℝ) (D : Matrix n n ℝ) :
    (pivotBlock a b D).PosSemidef ↔ (pivotSchur a b D).PosSemidef := by
  constructor
  · exact pivotSchur_posSemidef ha b D
  · intro hS
    let _ := scalarPivotInvertible (ne_of_gt ha)
    have hS' : (D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
        (pivotRow b)).PosSemidef := by
      rwa [real_pivot_schur_formula (ne_of_gt ha)]
    have h := (Matrix.PosDef.fromBlocks₁₁
      (pivotRow b) D (scalarPivot_posDef ha)).mpr hS'
    exact h

theorem zero_pivotBlock_posSemidef (D : Matrix n n ℝ) (hD : D.PosSemidef) :
    (pivotBlock 0 (fun _ => 0) D).PosSemidef := by
  change (Matrix.fromBlocks (0 : Matrix Unit Unit ℝ) 0 0 D).PosSemidef
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero (by simp) hD.isHermitian
  · intro x
    have hx : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) = x := Sum.elim_comp_inl_inr x
    have h := hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    rw [← hx]
    simpa [Matrix.fromBlocks_mulVec, Function.comp_def] using h

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivotPSD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

theorem fin_psd_of_schurTail {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : 0 < M 0 0)
    (hS : ((KS.W17.schurTail M).map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv (pivotIndexEquiv n)).mp
  change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
    (fun q : ℚ => (q : ℝ))).PosSemidef
  rw [fin_pivotBlock M hM, rat_pivotBlock_cast]
  apply (pivotBlock_posSemidef_iff (by exact_mod_cast ha) _ _).mpr
  rw [← rat_pivotSchur_cast, fin_pivotSchur M hM]
  exact hS

theorem fin_psd_of_zero_pivot_tail {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : M 0 0 = 0) (hrow : ∀ j : Fin n, M 0 j.succ = 0)
    (hD : ((KS.W17.trailingMatrix M).map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv (pivotIndexEquiv n)).mp
  change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
    (fun q : ℚ => (q : ℝ))).PosSemidef
  rw [fin_pivotBlock M hM, rat_pivotBlock_cast]
  simp only [ha, hrow, Rat.cast_zero]
  exact zero_pivotBlock_posSemidef _ hD

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_EliminationCompleteness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem rationalNegativeWitness_none_psd (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm)
    (hout : rationalNegativeWitness n M = none) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  induction n with
  | zero =>
      have hz : M.map (fun q : ℚ => (q : ℝ)) = 0 := by
        ext i j
        exact Fin.elim0 i
      rw [hz]
      exact Matrix.PosSemidef.zero
  | succ n ih =>
      by_cases hnegative : M 0 0 < 0
      · simp [rationalNegativeWitness, hnegative] at hout
      · by_cases hzero : M 0 0 = 0
        · cases hfind : firstNonzeroOffDiagonal M with
          | some j =>
              simp [rationalNegativeWitness, hzero, hfind] at hout
          | none =>
              have hrec : rationalNegativeWitness n (trailingMatrix M) = none := by
                simpa [rationalNegativeWitness, hnegative, hzero, hfind] using hout
              exact KS.W07.fin_psd_of_zero_pivot_tail M hM hzero
                ((firstNonzeroOffDiagonal_none_iff M).mp hfind)
                (ih (trailingMatrix M) (trailingMatrix_isSymm M hM) hrec)
        · have hrec : rationalNegativeWitness n (schurTail M) = none := by
            simpa [rationalNegativeWitness, hnegative, hzero] using hout
          have ha : 0 < M 0 0 :=
            lt_of_le_of_ne (le_of_not_gt hnegative) (Ne.symm hzero)
          exact KS.W07.fin_psd_of_schurTail M hM ha
            (ih (schurTail M) (schurTail_isSymm M hM) hrec)

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RationalPSDDecision
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17
open Matrix

theorem rationalNegativeWitness_none_iff_psd (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) :
    rationalNegativeWitness n M = none ↔
      (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  constructor
  · exact rationalNegativeWitness_none_psd n M hM
  · intro hPSD
    cases ho : rationalNegativeWitness n M with
    | none => rfl
    | some q =>
      have hs := computedPSDSeparator_separates n M hM q ho
      have hn := hs.2 (M.map (fun r : ℚ => (r : ℝ))) hPSD
      exact (not_lt_of_ge hn hs.1).elim

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCoordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*} {ea : α → Word}
local instance coordinates_natLE : PolyTime natLE := by unfold natLE;infer_instance
local instance coordinates_natEq : PolyTime natEq := by unfold natEq;infer_instance
local instance coordinates_matrixEntry_r8c08d3_1 : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
local instance coordinates_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
local instance coordinates_identityEntry : PolyTime identityEntry := by unfold identityEntry;infer_instance
local instance coordinates_identityMatrix : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then

local instance coordinates_fromBlocks_r8c08d3_1 : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then
instance poly_natLT : PolyTime natLT := by unfold natLT;infer_instance
instance poly_scaleMatrix {f : α → ℚ} {g : α → MatrixData}
    (r : Realizes ea ratCode f) (s : Realizes ea matrixCode g) [PolyTime r] [PolyTime s] :
    PolyTime (r.scaleMatrix s) := by unfold Realizes.scaleMatrix;apply poly_then
instance poly_negateMatrix : PolyTime negateMatrix := by unfold negateMatrix;infer_instance
instance poly_zeroMatrix : PolyTime zeroMatrix := by unfold zeroMatrix;infer_instance
instance poly_squareTabulate {f : (MatrixData×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime (squareTabulate r) := by unfold squareTabulate;apply poly_then
instance poly_singletonList (ea : α → Word) : PolyTime (singletonList ea) := by unfold singletonList;apply poly_then
instance poly_replicateList (ea : α → Word) : PolyTime (replicateList ea) := by unfold replicateList;infer_instance
instance poly_blockScalar : PolyTime blockScalar := by unfold blockScalar;apply poly_then
instance poly_withLevel : PolyTime withLevel := by unfold withLevel;apply poly_both
instance poly_matrixSub : PolyTime matrixSub := by
  unfold matrixSub
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd
instance poly_zeroRect : PolyTime zeroRect := by unfold zeroRect;apply poly_then
instance poly_basisVector : PolyTime basisVector := by unfold basisVector;apply poly_then
instance poly_pencilFromEval {f : α×List ℚ → MatrixData}
    (r : Realizes (prodCode ea vectorCode) matrixCode f) [PolyTime r] :
    PolyTime r.pencilFromEval := by
  unfold Realizes.pencilFromEval
  refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · refine @poly_tabulate _ _ _ _ _ _ ?_
      refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply poly_both
      · exact poly_matrixSub
instance poly_vdD : PolyTime vdD := by unfold vdD;infer_instance
instance poly_vdRest : PolyTime vdRest := by unfold vdRest;infer_instance
instance poly_vdAtoms : PolyTime vdAtoms := by unfold vdAtoms;infer_instance
instance poly_vdParams : PolyTime vdParams := by unfold vdParams;infer_instance
instance poly_vdX : PolyTime vdX := by unfold vdX;infer_instance
instance poly_vdTheta : PolyTime vdTheta := by unfold vdTheta;infer_instance
instance poly_vdEps : PolyTime vdEps := by unfold vdEps;infer_instance
instance poly_realDimension : PolyTime realDimension := by unfold realDimension;infer_instance
instance poly_valueDimension : PolyTime valueDimension := by unfold valueDimension;infer_instance
instance poly_coordinateIndexRealizes (b : Bool) : PolyTime (coordinateIndexRealizes b) := by unfold coordinateIndexRealizes;first | infer_instance | apply poly_then
instance poly_coordinateEntry (b : Bool) : PolyTime (coordinateEntry b) := by unfold coordinateEntry;infer_instance
instance poly_coordinates (b : Bool) : PolyTime (coordinates b) := by unfold coordinates;first | infer_instance | apply poly_then

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Lookup
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N n : ℕ}

lemma activeIndices_length_le (x : Fin N → ℚ) : (activeIndices x).length≤N := by
  have hh := List.length_filter_le (fun i : Fin N => decide (|x i|<1)) (List.finRange N)
  simp only [List.length_finRange] at hh
  exact hh

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PSDCleanRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.PSDCleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W07 KS.W17 KS.W17.FixedPSD
open CleanRoutine

lemma output_length (a : Datum) : (output a).length ≤ controllerTicks a := by
  have h := RoutineLength.output_length
    (KS.W23.PSDControllerPolynomial.controller_polynomial_spec a.2) (23 : Fin 35)
  simp only [output,witnessState,matrixState,state,show (23 : Fin 35)≠32 by decide,
    show (23 : Fin 35)≠26 by decide,show (23 : Fin 35)≠31 by decide,
    show (23 : Fin 35)≠30 by decide,ite_false, if_false,ite_true, if_true,List.length_nil,zero_add] at h ⊢
  exact h

lemma ticks_le (a : Datum) : ticks a≤
    3*(Computability.encodeNat a.1).length+2*(KS.W08.denseMatrixTape a.2).length+
      3*controllerTicks a+6 := by
  have h := output_length a
  unfold ticks
  omega

end CurrentKS.PSDCleanRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InvH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}

open scoped Matrix.Norms.L2Operator

theorem le_trace_smul_one {A : Mat d} (hA : A.PosSemidef) :
    A ≤ (A.trace.re : ℂ) • (1 : Mat d) := by
  let : CStarAlgebra (Mat d) := {}
  have heig (i : Fin d) : hA.isHermitian.eigenvalues i ≤ A.trace.re := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hc : 0 ≤ cfc (fun x : ℝ => A.trace.re - x) A := by
    apply (cfc_nonneg_iff _ A).mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hA.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    exact sub_nonneg.mpr (heig i)
  rw [cfc_sub (fun _ : ℝ => A.trace.re) (fun x : ℝ => x),
    cfc_const _ A hA.isHermitian.isSelfAdjoint] at hc
  change 0 ≤ (algebraMap ℝ (Mat d)) A.trace.re - cfc (id : ℝ → ℝ) A at hc
  rw [cfc_id ℝ A hA.isHermitian.isSelfAdjoint] at hc
  have hmap : (algebraMap ℝ (Mat d)) A.trace.re = (A.trace.re : ℂ) • (1 : Mat d) := by
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply]
  rw [hmap] at hc
  exact sub_nonneg.mp hc

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section L2Operator

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma sandwich_psd (A U : H d) (hU : U ∈ psdCone d) : sandwich A U ∈ psdCone d := by
  have hh := hU.mul_mul_conjTranspose_same (A : Mat d)
  rw [A.property.eq] at hh
  exact hh

end L2Operator

section Frobenius

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma inner_sandwich (A U P : H d) :
    inner ℝ P (sandwich A U) = inner ℝ (sandwich A P) U := by
  rw [inner_eq_trace, inner_eq_trace]
  change ((P : Mat d) * ((A : Mat d) * (U : Mat d) * (A : Mat d))).trace.re =
    ((A : Mat d) * (P : Mat d) * (A : Mat d) * (U : Mat d)).trace.re
  rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm ((P : Mat d) * (A : Mat d) * (U : Mat d))]
  simp only [mul_assoc]

end Frobenius

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_TraceCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ realTrace A :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

lemma realTrace_mono {A B : H d} (hab : A ≤ B) : realTrace A ≤ realTrace B := by
  have hh := realTrace_nonneg (show B-A ∈ psdCone d from hab)
  simpa using hh

@[simp] lemma traceCLM_apply (A : H d) : traceCLM A = realTrace A := inner_one A

lemma psd_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ A := hA.nonneg

lemma mem_psd_iff_nonneg (A : H d) : A ∈ psdCone d ↔ 0 ≤ A := by
  constructor
  · exact psd_nonneg
  · intro hA
    have hh : (0 : Mat d) ≤ (A : Mat d) := hA
    exact hh.posSemidef

lemma scalar_one_mono {r s : ℝ} (hrs : r ≤ s) :
    r • (one : H d) ≤ s • one := by
  apply sub_nonneg.mp
  erw [← sub_smul]
  exact psd_nonneg (psd_smul one_mem_psdCone (sub_nonneg.mpr hrs))

lemma trace_bound_above {A : H d} (hA : A ∈ psdCone d) : A ≤ realTrace A • one :=
  le_trace_smul_one hA

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InnerRight
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma trace_zero_psd {A : H d} (hA : A ∈ psdCone d) (htr : realTrace A = 0) : A = 0 := by
  apply le_antisymm
  · simpa only [htr, zero_smul] using trace_bound_above hA
  · exact psd_nonneg hA

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTraceSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_sum {ι : Type*} (s : Finset ι) (A : ι → H d) :
    realTrace (∑ i ∈ s, A i) = ∑ i ∈ s, realTrace (A i) := by
  simp only [← inner_one, inner_sum]

lemma psd_sum {ι : Type*} (s : Finset ι) (A : ι → H d) (hA : ∀ i ∈ s, A i ∈ psdCone d) :
    (∑ i ∈ s, A i) ∈ psdCone d := by
  exact (mem_psd_iff_nonneg _).mpr (Finset.sum_nonneg fun i hi => (mem_psd_iff_nonneg _).mp (hA i hi))

lemma scalar_mono_psd {A : H d} (hA : A ∈ psdCone d) {r s : ℝ} (hrs : r ≤ s) : r • A ≤ s • A := by
  apply sub_nonneg.mp
  rw [← sub_smul s r A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul hA (sub_nonneg.mpr hrs))

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r8c08d3_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma sum_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) : (∑ i, A i) ≤ (Hermitian.one : H d) := by
  have hp := trace_bound_above (psd_sum Finset.univ A fun i _ => hA i)
  simpa only [realTrace_sum,htr,one_smul] using hp

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PosLower
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma exists_pos_lower [NeZero d] {P : H d} (hP : P ∈ pd d) :
    ∃ a : ℝ, 0 < a ∧ a • (one : H d) ≤ P := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨a, ha, hap⟩ := (CFC.exists_pos_algebraMap_le_iff (a := (P : Mat d)) P.property).mpr
    ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (P : Mat d)).mp hP.isStrictlyPositive)
  refine ⟨a, ha, ?_⟩
  change (a : ℂ) • (1 : Mat d) ≤ (P : Mat d)
  convert hap using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply]

end

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma eq_zero_of_inner_pd [NeZero d] {P Z : H d} (hP : P ∈ pd d)
    (hZ : Z ∈ psdCone d) (hz : inner ℝ P Z = 0) : Z = 0 := by
  obtain ⟨a, ha, hap⟩ := exists_pos_lower hP
  have hh := inner_nonneg_of_psd (P-a•one) Z (show P-a•one ∈ psdCone d from hap) hZ
  rw [inner_sub_left, inner_smul_leftH, inner_one, hz] at hh
  have htr := realTrace_nonneg hZ
  apply trace_zero_psd hZ
  nlinarith

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich2
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma sandwich_eq_zero_iff [NeZero d] (U B : H d) (hB : B ∈ pd d) :
    sandwich U B = 0 ↔ U = 0 := by
  constructor
  · intro he
    have hz : inner ℝ B (sandwich U Hermitian.one) = 0 := by
      rw [real_inner_comm, ← inner_sandwich, he, inner_zero_right]
    have hs := eq_zero_of_inner_pd hB (sandwich_psd U _ one_mem_psdCone) hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [inner_eq_trace]
    have hv : (U : Mat d) * (U : Mat d) = 0 := by
      have hh := congrArg Subtype.val hs
      simpa only [sandwich_val, one_val, mul_one, ZeroMemClass.coe_zero] using hh
    rw [hv]
    simp
  · rintro rfl
    apply Subtype.ext
    simp [sandwich]

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Select
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Descent
variable {α : Type*}

lemma select_mem (score : α → ℚ) (a : α) (l : List α) : select score a l ∈ a :: l := by
  induction l generalizing a with
  | nil => simp [select]
  | cons b bs ih =>
    rw [select]
    split
    · have hh := ih b
      simp only [List.mem_cons] at hh ⊢
      tauto
    · have hh := ih a
      simp only [List.mem_cons] at hh ⊢
      tauto

lemma run_invariant (step : α → Option α) (P : α → Prop)
    (hp : ∀ x y,P x → step x=some y → P y) (k : ℕ) (x : α) (hx : P x) :
    P (run step k x) := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    simp only [run]
    split
    · exact hx
    · rename_i y hy
      exact ih y (hp x y hx hy)

end CurrentKS.Descent

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStored
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma flatten_code_le (ea : α → Word) (xs : List (List α)) :
    (listCode ea xs.flatten).length≤(listCode (listCode ea) xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatten_cons,listCode_append,List.length_append,listCode_cons,prodCode_length]
      omega
instance size_appendList (ea : α → Word) : FoldSize (appendList ea) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_append_flatten,listCode_append,List.length_append]
  have hs := le_prodCode_left (ea:=listCode ea) (eb:=listCode (listCode ea)) (s,xs)
  have hy := (flatten_code_le ea ys).trans ((prefix_code_length (listCode ea) xs ys zs h).trans (le_prodCode_right (ea:=listCode ea) (s,xs)))
  change _≤2*(prodCode (listCode ea) (listCode (listCode ea)) (s,xs)).length
  dsimp only at hs hy
  omega
instance poly_flattenList (ea : α → Word) : PolyTime (flattenList ea) := by unfold flattenList;infer_instance
instance poly_joinList (ea : α → Word) : PolyTime (joinList ea) := by unfold joinList;infer_instance
instance poly_singleton (ea : α → Word) : PolyTime (singleton ea) := by unfold singleton;apply poly_then
instance poly_filterCtx {p : γ×α → Bool} (r : Realizes (prodCode ec ea) boolCode p) [PolyTime r] :
    PolyTime r.filterCtx := by unfold Realizes.filterCtx;infer_instance

instance poly_natToBinary : PolyTime natToBinary := by unfold natToBinary;infer_instance

lemma psd_raw_poly : ∃ p : NaturalPolynomial,∀a,PSDCleanRoutine.ticks a≤p.eval (PSDCleanRoutine.input a).length := by
  refine ⟨5*X+3*NaturalPolynomial.constant PSDControllerPolynomial.coefficient*(X+1)^58+6,?_⟩
  intro a
  have h := PSDCleanRoutine.ticks_le a
  have hd : (Computability.encodeNat a.1).length≤(PSDCleanRoutine.input a).length := by
    simp only [PSDCleanRoutine.input,List.length_append,KS.W01.length_frame];omega
  have hm : (KS.W08.denseMatrixTape a.2).length≤(PSDCleanRoutine.input a).length := by
    simp only [PSDCleanRoutine.input,List.length_append];omega
  unfold PSDCleanRoutine.controllerTicks KS.W29.polynomialFuel at h
  have hp := Nat.mul_le_mul_left PSDControllerPolynomial.coefficient (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 58)
  change _≤5*(PSDCleanRoutine.input a).length+3*PSDControllerPolynomial.coefficient*((PSDCleanRoutine.input a).length+1)^58+6
  rw [Nat.mul_assoc]
  omega
instance poly_psdStored : PolyTime psdStored := by
  unfold psdStored
  refine @poly_congr _ _ _ _ _ _ _ _ ?_
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_changeOutput _ _ _ _ _ _ _ _ _ _ ?_
    refine @poly_reindex _ _ _ _ _ _ _ _ _ _ ?_
    refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · apply poly_then
    · apply poly_then
  · exact ⟨psd_raw_poly⟩

instance poly_natLE : PolyTime natLE := by unfold natLE;infer_instance
instance poly_natEq : PolyTime natEq := by unfold natEq;infer_instance
instance poly_matrixEntry : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
instance poly_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
instance poly_identityEntry : PolyTime identityEntry := by unfold identityEntry;infer_instance
instance poly_identityMatrix : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then
instance poly_transposeMatrix : PolyTime transposeMatrix := by unfold transposeMatrix;apply poly_then
instance poly_matrixMul : PolyTime matrixMul := by unfold matrixMul;apply poly_then
instance poly_fromBlocks : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then
instance poly_tabulateFin {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] :
    PolyTime (r.tabulateFin rn) := by unfold Realizes.tabulateFin;infer_instance
instance poly_familyFirst {n : α → ℕ} : PolyTime (familyFirst (ea:=ea) (n:=n)) := by unfold familyFirst;apply poly_reindex
instance poly_familyIndex {n : α → ℕ} : PolyTime (familyIndex (ea:=ea) (n:=n)) := by unfold familyIndex;apply poly_reindex

instance poly_pow {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] (k : ℕ) : PolyTime (r.pow k) := by
  induction k with
  | zero => unfold Realizes.pow;infer_instance
  | succ k ih => unfold Realizes.pow;infer_instance
instance poly_min {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.min s) := by unfold Realizes.min;infer_instance
instance poly_max {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.max s) := by unfold Realizes.max;infer_instance
instance poly_inv {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.inv := by unfold Realizes.inv;infer_instance
instance poly_lt {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.lt s) := by unfold Realizes.lt;infer_instance
instance poly_eq {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.eq s) := by unfold Realizes.eq;infer_instance

instance poly_better (ea : α → Word) : PolyTime (better ea) := by unfold better;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialExplicit
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
  {f : α → β} {g : β → γ}
lemma PolyTime.both {g : α → γ} {r : Realizes ea eb f} {s : Realizes ea ec g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.both s) := @poly_both _ _ _ _ _ _ _ _ _ _ hr hs
lemma PolyTime.ite {p : α → Bool} {g : α → β} {b : Realizes ea boolCode p}
    {r : Realizes ea eb f} {s : Realizes ea eb g} (hb : PolyTime b) (hr : PolyTime r) (hs : PolyTime s) :
    PolyTime (b.ite r s) := @poly_ite _ _ _ _ _ _ _ _ _ _ hb hr hs
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSchedule
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_saD : PolyTime saD := by unfold saD;infer_instance
instance poly_saRest : PolyTime saRest := by unfold saRest;infer_instance
instance poly_saN : PolyTime saN := by unfold saN;apply poly_then
instance poly_saScalars : PolyTime saScalars := by unfold saScalars;apply poly_then
instance poly_saNu : PolyTime saNu := by unfold saNu;apply poly_then
instance poly_saLam : PolyTime saLam := by unfold saLam;apply poly_then
instance poly_saEpsilon : PolyTime saEpsilon := by unfold saEpsilon;apply poly_div
instance poly_saSigma : PolyTime saSigma := by unfold saSigma;apply poly_div
instance poly_movementBudget : PolyTime movementBudget := by unfold movementBudget;apply poly_max
instance poly_saThreshold : PolyTime saThreshold := by unfold saThreshold;apply poly_div
instance poly_saCoarse : PolyTime saCoarse := by unfold saCoarse;apply poly_add
instance poly_saCurve2 : PolyTime saCurve2 := by unfold saCurve2;apply poly_mul
instance poly_saCurve3 : PolyTime saCurve3 := by unfold saCurve3;apply poly_mul
instance poly_saBudget : PolyTime saBudget := by unfold saBudget;apply poly_add
instance poly_saStep : PolyTime saStep := by unfold saStep;apply poly_min
instance poly_saStencil : PolyTime saStencil := by unfold saStencil;apply poly_min
instance poly_saMesh : PolyTime saMesh := by unfold saMesh;apply poly_div
instance poly_parameters_singleton : PolyTime parameters.singletonRat := by unfold parameters.singletonRat;apply poly_then
instance poly_parameters : PolyTime parameters := by unfold parameters;apply poly_changeOutput
instance poly_parameterField (i : ℕ) : PolyTime (parameterField i) := by
  unfold parameterField
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_reindex
  · infer_instance
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RankFactor
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder

variable {d : ℕ}

lemma rank_one_factor (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef)
    (hrank : A.rank ≤ 1) : ∃ u : Fin d → ℂ, A = vecMulVec u (star u) := by
  classical
  by_cases hzero : A = 0
  · refine ⟨0, ?_⟩
    rw [hzero]
    ext j k
    simp [vecMulVec]
  have he : ∃ i, hA.isHermitian.eigenvalues i ≠ 0 := by
    by_contra! hh
    apply hzero
    exact hA.isHermitian.eigenvalues_eq_zero_iff.mp (funext hh)
  obtain ⟨i,hi⟩ := he
  let U : Matrix (Fin d) (Fin d) ℂ := hA.isHermitian.eigenvectorUnitary
  let e : ℝ := hA.isHermitian.eigenvalues i
  have he0 : 0 ≤ e := hA.eigenvalues_nonneg i
  have hsqrt : (Real.sqrt e : ℂ) * (Real.sqrt e : ℂ) = (e : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt he0
  refine ⟨fun j => (Real.sqrt e : ℂ) * U j i, ?_⟩
  have hspec := hA.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] at hspec
  rw [hspec]
  ext j k
  change ∑ l, ((U * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.isHermitian.eigenvalues)) j l) *
      U.conjTranspose l k = ((Real.sqrt e : ℂ)*U j i) * star ((Real.sqrt e : ℂ)*U k i)
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.mul_diagonal,Function.comp_apply,Matrix.conjTranspose_apply,
      StarMul.star_mul,Complex.star_def,Complex.conj_ofReal]
    change U j i * (e : ℂ) * star (U k i) =
      ((Real.sqrt e : ℂ) * U j i) * (star (U k i) * (Real.sqrt e : ℂ))
    rw [← hsqrt]
    ring
  · intro l _ hli
    have hl : hA.isHermitian.eigenvalues l = 0 := by
      by_contra hl
      exact hli (nonzero_eigenvalue_unique A hA.isHermitian hrank l i hl hi)
    simp only [Matrix.mul_diagonal,Function.comp_apply,hl,RCLike.ofReal_zero,mul_zero,zero_mul]
  · simp

lemma outer_sandwich (u : Fin d → ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    vecMulVec u (star u) * B * vecMulVec u (star u) =
      (star u ⬝ᵥ (B *ᵥ u)) • vecMulVec u (star u) := by
  ext i j
  simp only [Matrix.mul_apply,vecMulVec_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.mulVec,dotProduct]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma trace_outer_mul (u : Fin d → ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    (vecMulVec u (star u) * B).trace = star u ⬝ᵥ (B *ᵥ u) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,vecMulVec_apply,Matrix.mulVec,dotProduct,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma rank_one_sandwich (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef)
    (hrank : A.rank ≤ 1) (B : Matrix (Fin d) (Fin d) ℂ) :
    A*B*A = (A*B).trace • A := by
  obtain ⟨u,rfl⟩ := rank_one_factor A hA hrank
  rw [outer_sandwich,trace_outer_mul]

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SandwichShiftInverse
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma trace_mul_real (A B : H d) : (((A : Mat d)*(B : Mat d)).trace.re : ℂ) = ((A : Mat d)*(B : Mat d)).trace := by
  have hs : star (((A : Mat d)*(B : Mat d)).trace) = ((A : Mat d)*(B : Mat d)).trace := by
    rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,A.property.eq,B.property.eq,Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.mp hs

lemma sandwich_rank_one (A B : H d) (hA : A ∈ psdCone d) (hrank : (A : Mat d).rank ≤ 1) :
    sandwich A B = (inner ℝ A B) • A := by
  apply Subtype.ext
  change (A : Mat d)*(B : Mat d)*(A : Mat d) = (inner ℝ A B) • (A : Mat d)
  rw [CurrentKS.rank_one_sandwich _ hA hrank,inner_eq_trace]
  have hs (r : ℝ) : r • (A : Mat d) = (r : ℂ) • (A : Mat d) := by
    ext i j
    exact Complex.real_smul
  rw [hs,trace_mul_real]

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SquareInterval
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot

lemma squareInterval_spec (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^2) (k : ℕ) :
    0 ≤ (squareInterval q k).1 ∧ (squareInterval q k).2 ≤ 1 ∧
    ((squareInterval q k).1:ℝ) ≤ r ∧ r ≤ ((squareInterval q k).2:ℝ) ∧
    (squareInterval q k).2-(squareInterval q k).1=(1/2:ℚ)^k := by
  induction k with
  | zero => simpa [squareInterval] using And.intro hr hr1
  | succ k ih =>
    have horder : (squareInterval q k).1 ≤ (squareInterval q k).2 := by
      exact_mod_cast ih.2.2.1.trans ih.2.2.2.1
    let m : ℚ := ((squareInterval q k).1+(squareInterval q k).2)/2
    have hml : (squareInterval q k).1 ≤ m := by dsimp [m] <;> linarith
    have hmu : m ≤ (squareInterval q k).2 := by dsimp [m] <;> linarith
    have hm : 0 ≤ m := ih.1.trans hml
    have hmr : (0:ℝ) ≤ m := by exact_mod_cast hm
    have he : squareInterval q (k+1) = if m^2 ≤ q then (m,(squareInterval q k).2) else ((squareInterval q k).1,m) := rfl
    rw [he]
    split
    · rename_i h
      have hc : (m:ℝ)^2 ≤ r^2 := by rw [← hq]; exact_mod_cast h
      have hle := (pow_le_pow_iff_left₀ hmr hr (by decide : 2≠0)).mp hc
      refine ⟨hm,ih.2.1,hle,ih.2.2.2.1,?_⟩
      change (squareInterval q k).2-m=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring
    · rename_i h
      have hc : r^2 ≤ (m:ℝ)^2 := by rw [← hq]; exact_mod_cast (le_of_lt (lt_of_not_ge h))
      have hle := (pow_le_pow_iff_left₀ hr hmr (by decide : 2≠0)).mp hc
      refine ⟨ih.1,hmu.trans ih.2.1,ih.2.2.1,hle,?_⟩
      change m-(squareInterval q k).1=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring

lemma squareInterval_upper_error (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^2) (k : ℕ) :
    |((squareInterval q k).2:ℝ)-r| ≤ (1/2:ℝ)^k := by
  obtain ⟨_,_,hl,hu,hw⟩ := squareInterval_spec q r hr hr1 hq k
  have hwr : ((squareInterval q k).2:ℝ)-(squareInterval q k).1=(1/2:ℝ)^k := by
    have hc := congrArg (fun z : ℚ => (z : ℝ)) hw
    norm_num only [Rat.cast_sub,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hc
    exact hc
  rw [abs_of_nonneg (sub_nonneg.mpr hu)]
  linarith

lemma inverse_pow_size_le {δ : ℚ} (hδ : 0 < δ) : (1/2:ℚ)^δ.den.size ≤ δ := by
  have hd : (0:ℚ) < δ.den := by exact_mod_cast δ.den_pos
  have hp : (0:ℚ) < 2^δ.den.size := by positivity
  have hnum : (1:ℚ) ≤ δ.num := by exact_mod_cast (Int.add_one_le_iff.mpr (Rat.num_pos.mpr hδ))
  have hden : (δ.den:ℚ) ≤ 2^δ.den.size := by exact_mod_cast (Nat.lt_size_self δ.den).le
  rw [_root_.one_div_pow,one_div]
  calc
    (2^δ.den.size:ℚ)⁻¹ ≤ (δ.den:ℚ)⁻¹ := inv_anti₀ hd hden
    _ ≤ (δ.num:ℚ)/(δ.den:ℚ) := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hnum hd.le
    _ = δ := Rat.num_div_den δ

theorem upperSqrt_spec (q δ : ℚ) (hδ : 0 < δ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.sqrt (q:ℝ) ≤ (upperSqrt q δ:ℝ) ∧
    (upperSqrt q δ:ℝ) ≤ Real.sqrt (q:ℝ)+(δ:ℝ) := by
  have hr := Real.sqrt_nonneg (q:ℝ)
  have hr1 : Real.sqrt (q:ℝ) ≤ 1 := by
    exact (Real.sqrt_le_one).mpr (by exact_mod_cast hq1)
  have he : (q:ℝ) = Real.sqrt (q:ℝ)^2 := (Real.sq_sqrt (by exact_mod_cast hq)).symm
  have hs := squareInterval_spec q (Real.sqrt q) hr hr1 he δ.den.size
  have herror := squareInterval_upper_error q (Real.sqrt q) hr hr1 he δ.den.size
  have hh : (1/2:ℝ)^δ.den.size ≤ (δ:ℝ) := by
    have h := Rat.cast_le (K := ℝ).mpr (inverse_pow_size_le hδ)
    norm_num only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  refine ⟨hs.2.2.2.1,?_⟩
  have hm := (abs_le.mp herror).2
  dsimp [upperSqrt]
  linarith

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_RealificationSPD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open Matrix
open scoped ComplexOrder BigOperators

theorem realify_conjTranspose {m n : Type*} (A : Matrix m n ℂ) :
    realify Aᴴ = (realify A)ᵀ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem realify_isHermitian {n : Type*} (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (realify A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrFun (congrFun (realify_conjTranspose A) j) i
  rw [hA] at h
  simpa using h

theorem realifyVector_dotProduct {n : Type*} [Fintype n] (x y : n → ℂ) :
    realifyVector x ⬝ᵥ realifyVector y = (star x ⬝ᵥ y).re := by
  simp [realifyVector, dotProduct, Fintype.sum_sum_type, Complex.mul_re,
    Finset.sum_add_distrib]

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealifyHermitian
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace KS.W08
open Matrix
open scoped ComplexOrder BigOperators

lemma realify_isHermitian_iff {n : Type*} (A : Matrix n n ℂ) :
    (realify A).IsHermitian ↔ A.IsHermitian := by
  refine ⟨?_,realify_isHermitian A⟩
  intro h
  apply realify_injective
  rw [realify_conjTranspose]
  simpa using h.eq

theorem realify_posSemidef_iff {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    (realify A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((realify_isHermitian_iff A).mp h.isHermitian) ?_
    intro v
    have hv := h.dotProduct_mulVec_nonneg (realifyVector v)
    rw [star_trivial,← realify_mulVec,realifyVector_dotProduct] at hv
    exact Complex.nonneg_iff.mpr ⟨hv,((realify_isHermitian_iff A).mp h.isHermitian |>.im_star_dotProduct_mulVec_self v).symm⟩
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (realify_isHermitian A h.isHermitian) ?_
    intro v
    have hv := h.dotProduct_mulVec_nonneg (complexifyVector v)
    have hr : 0 ≤ (star (complexifyVector v) ⬝ᵥ (A *ᵥ complexifyVector v)).re :=
      Complex.nonneg_iff.mp hv |>.1
    rw [← realifyVector_dotProduct,realify_mulVec,realifyVector_complexify] at hr
    simpa only [star_trivial] using hr

end KS.W08

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_AffineRealEval
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {n m p d N : ℕ}

lemma realFinDecode_cast (x : Fin d × Fin d → ℚ) :
    (realFinDecode d x).map (fun q => (q:ℝ))=realFinDecode d (fun i => (x i:ℝ)) := by
  change ((realDecode x).submatrix _ _).map _=(realDecode _).submatrix _ _
  rw [← Matrix.submatrix_map,realDecode_ratCast]

lemma cast_matrix_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin m) (Fin m) ℚ) :
    (∑ i ∈ s,A i).map (fun q => (q:ℝ))=∑ i ∈ s,(A i).map (fun q => (q:ℝ)) := by
  ext i j
  simp [Matrix.sum_apply,Rat.cast_sum]
lemma cast_matrix_smul (r : ℚ) (A : Matrix (Fin m) (Fin m) ℚ) :
    (r • A).map (fun q => (q:ℝ))=(r:ℝ) • A.map (fun q => (q:ℝ)) := by
  ext i j
  simp [Matrix.smul_apply]
lemma cast_matrix_one : (1 : Matrix (Fin m) (Fin m) ℚ).map (fun q => (q:ℝ))=1 := by
  exact Matrix.map_one _ (by simp) (by simp)
lemma cast_matrix_sub (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A-B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))-B.map (fun q => (q:ℝ)) := by
  ext i j
  simp
lemma cast_matrix_mul (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A*B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))*B.map (fun q => (q:ℝ)) := by
  exact Matrix.map_mul (f := algebraMap ℚ ℝ)

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FinRealify
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates KS.W08
open scoped BigOperators ComplexOrder

variable {n m p d N : ℕ}

lemma posSemidef_reindex_iff {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℝ) (e : β ≃ α) : (A.submatrix e e).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    have hh := h.submatrix e.symm
    simp only [Matrix.submatrix_submatrix,Function.comp_def,Equiv.apply_symm_apply] at hh
    exact hh
  · exact fun h => h.submatrix _

lemma finRealify_psd (A : Matrix (Fin d) (Fin d) ℂ) :
    (finRealify A).PosSemidef ↔ A.PosSemidef := by
  rw [finRealify,posSemidef_reindex_iff,realify_posSemidef_iff]
lemma finRealify_one : finRealify (1 : Matrix (Fin d) (Fin d) ℂ)=1 := by
  unfold finRealify
  rw [realify_one]
  ext i j
  simp [Matrix.one_apply]
lemma finRealify_add (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A+B)=finRealify A+finRealify B := by
  simp only [finRealify,realify_add,Matrix.submatrix_add,Pi.add_apply]
lemma finRealify_smul (r : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (r • A)=r • finRealify A := by
  simp only [finRealify,realify_smul,Matrix.submatrix_smul,Pi.smul_apply]
lemma finRealify_neg (A : Matrix (Fin d) (Fin d) ℂ) : finRealify (-A)= -finRealify A := by
  have h : realify (-A) = -realify A := by
    ext (i|i) (j|j) <;> simp [realify,Matrix.fromBlocks]
  simp only [finRealify,h,Matrix.submatrix_neg]
  rfl
lemma finRealify_sub (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A-B)=finRealify A-finRealify B := by
  simp only [sub_eq_add_neg,finRealify_add,finRealify_neg]
lemma finRealify_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A*B)=finRealify A*finRealify B := by
  rw [finRealify,realify_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _).symm
lemma finRealify_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d) (Fin d) ℂ) :
    finRealify (∑ i ∈ s,A i)=∑ i ∈ s,finRealify (A i) := by
  ext i j
  simp only [finRealify,realify_sum,Matrix.submatrix_apply,Matrix.sum_apply]

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_OperatorNorm
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma operatorNorm_nonneg (A : H d) : 0 ≤ operatorNorm A := norm_nonneg _

lemma operatorNorm_eq_matrix (A : H d) : operatorNorm A = ‖(A : Mat d)‖ := rfl

lemma scalarOne_eq_algebraMap (r : ℝ) : ((r • (one : H d) : H d) : Mat d) = algebraMap ℝ (Mat d) r := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

lemma le_operatorNorm_smul_one (A : H d) : A ≤ operatorNorm A • one := by
  let : CStarAlgebra (Mat d) := {}
  change (A : Mat d) ≤ ((operatorNorm A • one : H d) : Mat d)
  rw [scalarOne_eq_algebraMap,operatorNorm_eq_matrix]
  exact A.property.isSelfAdjoint.le_algebraMap_norm_self

lemma operatorNorm_le_of_psd_le {A : H d} (hA : A ∈ psdCone d) {r : ℝ} (hr : 0 ≤ r)
    (hhi : A ≤ r • (one : H d)) : operatorNorm A ≤ r := by
  let : CStarAlgebra (Mat d) := {}
  apply (CStarAlgebra.norm_le_iff_le_algebraMap (A : Mat d) hr hA.nonneg).mpr
  change (A : Mat d) ≤ ((r • one : H d) : Mat d) at hhi
  rwa [scalarOne_eq_algebraMap] at hhi

lemma operatorNorm_eq_zero_iff (A : H d) : operatorNorm A = 0 ↔ A = 0 := by
  rw [operatorNorm_eq_matrix,norm_eq_zero]
  exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩

end

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceBasics
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_activeIndices : PolyTime activeIndices := by unfold activeIndices;apply poly_then
instance poly_fD : PolyTime fD := by unfold fD;apply poly_then
instance poly_fRest : PolyTime fRest := by unfold fRest;apply poly_then
instance poly_fAtoms : PolyTime fAtoms := by unfold fAtoms;apply poly_then
instance poly_fArgs : PolyTime fArgs := by unfold fArgs;apply poly_then
instance poly_fBase : PolyTime fBase := by unfold fBase;apply poly_then
instance poly_fScalars : PolyTime fScalars := by unfold fScalars;apply poly_then
instance poly_fNu : PolyTime fNu := by unfold fNu;apply poly_then
instance poly_fLam : PolyTime fLam := by unfold fLam;apply poly_then
instance poly_fIndices : PolyTime fIndices := by unfold fIndices;apply poly_congr
instance poly_fN : PolyTime fN := by unfold fN;apply poly_congr
instance poly_fSchedule : PolyTime fSchedule := by unfold fSchedule;apply poly_then
instance poly_gather : PolyTime gather := by unfold gather;apply poly_mapCtx
instance poly_fState : PolyTime fState := by unfold fState;apply poly_congr
instance poly_fpP : PolyTime fpP := by unfold fpP;apply poly_then
instance poly_fpY : PolyTime fpY := by unfold fpY;apply poly_then
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NearestEndpoint
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N : ℕ}

lemma nearestEndpoint_abs (r : ℚ) : |nearestEndpoint r|=1 := by
  unfold nearestEndpoint
  split <;> norm_num

lemma freezeOne_cube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N) :
    ∀ j,|freezeOne σ x i j|≤1 := by
  unfold freezeOne
  split
  · intro j
    by_cases hj : j=i
    · subst j;simpa using (nearestEndpoint_abs (x i)).le
    · simpa only [Function.update_of_ne hj] using hx j
  · exact hx

lemma freezeOne_other (σ : ℚ) (x : Fin N → ℚ) (i j : Fin N) (hji : j≠i) :
    freezeOne σ x i j=x j := by
  unfold freezeOne
  split <;> simp [Function.update_of_ne hji]

lemma freezeOne_assigned (σ : ℚ) (x : Fin N → ℚ) (i : Fin N) :
    |freezeOne σ x i i|=1 ∨ σ<1-|freezeOne σ x i i| := by
  unfold freezeOne
  split
  · exact Or.inl (by simpa using nearestEndpoint_abs (x i))
  · exact Or.inr (lt_of_not_ge ‹¬1-|x i|≤σ›)

lemma freezeOne_preserves_assigned (σ : ℚ) (x : Fin N → ℚ) (i j : Fin N)
    (h : |x j|=1 ∨ σ<1-|x j|) :
    |freezeOne σ x i j|=1 ∨ σ<1-|freezeOne σ x i j| := by
  by_cases hji : j=i
  · subst j;exact freezeOne_assigned σ x i
  · simpa only [freezeOne_other σ x i j hji] using h

lemma freezeList_cube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (l : List (Fin N)) :
    ∀ j,|freezeList σ x l j|≤1 := by
  induction l generalizing x with
  | nil => exact hx
  | cons i is ih => exact ih _ (freezeOne_cube σ x hx i)

lemma freezeList_preserves_assigned (σ : ℚ) (x : Fin N → ℚ) (l : List (Fin N)) (j : Fin N)
    (h : |x j|=1 ∨ σ<1-|x j|) :
    |freezeList σ x l j|=1 ∨ σ<1-|freezeList σ x l j| := by
  induction l generalizing x with
  | nil => exact h
  | cons i is ih => exact ih _ (freezeOne_preserves_assigned σ x i j h)

lemma freezeList_assigned (σ : ℚ) (x : Fin N → ℚ) (l : List (Fin N)) (j : Fin N) (hj : j∈l) :
    |freezeList σ x l j|=1 ∨ σ<1-|freezeList σ x l j| := by
  induction l generalizing x with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with hij|hj
    · subst j
      exact freezeList_preserves_assigned σ _ is i (freezeOne_assigned σ x i)
    · exact ih _ hj

lemma freezeAll_strip (σ : ℚ) (x : Fin N → ℚ) (j : Fin N)
    (hj : |freezeAll σ x j|<1) : |freezeAll σ x j|<1-σ := by
  have hh := freezeList_assigned σ x (List.finRange N) j (List.mem_finRange j)
  change |freezeAll σ x j|=1 ∨ σ<1-|freezeAll σ x j| at hh
  rcases hh with h|h <;> linarith

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Transition
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

lemma freezeAll_stripCube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) :
    StripCube σ (freezeAll σ x) :=
  ⟨freezeList_cube σ x hx _,fun i hi => (freezeAll_strip σ x i hi).le⟩

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_VarianceH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma varianceH_psd (A : Fin N → H d) : varianceH A ∈ psdCone d :=
  psd_sum Finset.univ _ fun index _ => sandwich_psd (A index) _ one_mem_psdCone

lemma trace_each_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i) = 1) (i : Fin N) : Hermitian.realTrace (A i) ≤ 1 := by
  rw [← htr]
  exact Finset.single_le_sum (fun j _ => realTrace_nonneg (hA j)) (Finset.mem_univ i)

lemma varianceH_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (htr : ∑ i,Hermitian.realTrace (A i) = 1) :
    varianceH A ≤ (Hermitian.one : H d) := by
  apply le_trans _ (sum_le_one A hA htr)
  apply Finset.sum_le_sum
  intro i _
  rw [sandwich_rank_one (A i) _ (hA i) (hrank i),inner_one']
  simpa only [one_smul] using scalar_mono_psd (hA i) (trace_each_le_one A hA htr i)

lemma varianceH_pos [NeZero d] (A : Fin N → H d) (_hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i) = 1) : 0 < operatorNorm (varianceH A) := by
  apply lt_of_le_of_ne (operatorNorm_nonneg _)
  intro heq
  have hzero : varianceH A = 0 := (operatorNorm_eq_zero_iff _).mp heq.symm
  have hz (i : Fin N) : A i = 0 := by
    have hle : sandwich (A i) (Hermitian.one : H d) ≤ varianceH A :=
      Finset.single_le_sum (fun j _ => psd_nonneg (sandwich_psd (A j) _ one_mem_psdCone)) (Finset.mem_univ i)
    rw [hzero] at hle
    have hh : sandwich (A i) (Hermitian.one : H d) = 0 :=
      le_antisymm hle (psd_nonneg (sandwich_psd _ _ one_mem_psdCone))
    exact (sandwich_eq_zero_iff (A i) (Hermitian.one : H d) Matrix.PosDef.one).mp hh
  have ht : (∑ i,Hermitian.realTrace (A i)) = 0 := by simp only [hz,realTrace_zero,Finset.sum_const_zero]
  linarith

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_RealTraceVarianceRank
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma realTrace_variance_rank_one (A : Fin N → H d) (hA : ∀ i,A i ∈ psdCone d)
    (hrank : ∀ i,(A i : Mat d).rank ≤ 1) :
    Hermitian.realTrace (varianceH A)=∑ i,(Hermitian.realTrace (A i))^2 := by
  rw [varianceH,Hermitian.realTrace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) _ (hA i) (hrank i),inner_one',Hermitian.realTrace_smul]
  ring

lemma variance_lower [NeZero d] [NeZero N] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (hrank : ∀ i,(A i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) :
    1/((N:ℝ)*d) ≤ operatorNorm (varianceH A) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast NeZero.pos d
  have hNpos : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun _ : Fin N => (1:ℝ)) (fun i => Hermitian.realTrace (A i))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,htr] at hcs
  have ht := realTrace_mono (le_operatorNorm_smul_one (varianceH A))
  rw [Hermitian.realTrace_smul,Hermitian.realTrace_one,realTrace_variance_rank_one A hA hrank] at ht
  have hm := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N : (0:ℝ)≤N)
  apply (div_le_iff₀ (by positivity : (0:ℝ)<N*d)).mpr
  nlinarith

lemma variance_lower_paper [NeZero d] [NeZero N] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (hrank : ∀ i,(A i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) :
    1/((N:ℝ)*d^2) ≤ operatorNorm (varianceH A) := by
  apply le_trans _ (variance_lower A hA hrank htr)
  have hdpos : (0:ℝ) < d := by exact_mod_cast NeZero.pos d
  have hNpos : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  apply one_div_le_one_div_of_le (mul_pos hNpos hdpos)
  have hd : (1:ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  exact mul_le_mul_of_nonneg_left (by nlinarith : (d:ℝ) ≤ (d:ℝ)^2) hNpos.le

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_UpperIndex
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalGrid

lemma upperIndex_le (den : ℕ) (test : ℚ → Bool) (k : ℕ) : upperIndex den test k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [upperIndex]
    split
    · exact ih.trans (Nat.le_succ k)
    · rfl

lemma upperIndex_spec (den : ℕ) (test : ℚ → Bool) (r : ℝ)
    (htest : ∀ k : ℕ,test ((k:ℚ)/den)=true ↔ r ≤ (k:ℝ)/den) (k : ℕ)
    (hk : r ≤ (k:ℝ)/den) :
    r ≤ (upperIndex den test k:ℝ)/den ∧
      (upperIndex den test k:ℝ)/den ≤ r+1/(den:ℝ) ∨ r ≤ 0 ∧ upperIndex den test k=0 := by
  induction k with
  | zero => exact Or.inr ⟨by simpa using hk,rfl⟩
  | succ k ih =>
    by_cases h : test ((k:ℚ)/den)=true
    · simp only [upperIndex,h,↓reduceIte]
      exact ih ((htest k).mp h)
    · have hlt : (k:ℝ)/den < r := lt_of_not_ge (fun he => h ((htest k).mpr he))
      simp only [upperIndex,h,Bool.false_eq_true,↓reduceIte]
      apply Or.inl
      refine ⟨hk,?_⟩
      rw [Nat.cast_add,Nat.cast_one,add_div]
      linarith

theorem upper_spec (den : ℕ) (hden : 0 < den) (test : ℚ → Bool) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (htest : ∀ k : ℕ,test ((k:ℚ)/den)=true ↔ r ≤ (k:ℝ)/den) :
    r ≤ (upper den test:ℝ) ∧ (upper den test:ℝ) ≤ r+1/(den:ℝ) ∧ upper den test ≤ 1 := by
  have hd : (0:ℝ)<den := by exact_mod_cast hden
  have hdq : (0:ℚ)<den := by exact_mod_cast hden
  have hspec := upperIndex_spec den test r htest den (by simpa only [div_self hd.ne'] using hr1)
  have hle : upper den test ≤ 1 := by
    unfold upper
    apply (div_le_one hdq).mpr
    exact_mod_cast upperIndex_le den test den
  have he : (upper den test:ℝ)=(upperIndex den test den:ℝ)/den := by simp [upper]
  refine ⟨?_,?_,hle⟩
  · rcases hspec with hs|hs
    · simpa only [he] using hs.1
    · rw [he,hs.2,Nat.cast_zero,zero_div]
      exact hs.1
  · rcases hspec with hs|hs
    · simpa only [he] using hs.2
    · rw [he,hs.2,Nat.cast_zero,zero_div]
      positivity

end CurrentKS.RationalGrid

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {d N : ℕ}

noncomputable section
open CurrentKS.Hermitian CurrentKS.Variational CurrentKS.State
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

lemma rationalVariance_symm (coords : Fin N → Fin d × Fin d → ℚ) :
    (rationalVariance coords).IsSymm := by
  change (∑ i,realFinDecode d (coords i)*realFinDecode d (coords i)).transpose=_
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.transpose_mul,(realFinDecode_symm _).eq]

lemma rationalVariance_cast (coords : Fin N → Fin d × Fin d → ℚ) :
    (rationalVariance coords).map (fun q => (q:ℝ)) =
      finRealify ((varianceH (rationalAtoms coords) : H d) : Mat d) := by
  simp only [rationalVariance,cast_matrix_sum,cast_matrix_mul,realFinDecode_cast,
    varianceH,Submodule.coe_sum,finRealify_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sandwich_val]
  change _=finRealify ((_ : Mat d)*1*(_ : Mat d))
  rw [mul_one,finRealify_mul]
  congr 1

lemma varianceTest_spec (coords : Fin N → Fin d × Fin d → ℚ) (q : ℚ) (hq : 0 ≤ q) :
    varianceTest coords q=true ↔ operatorNorm (varianceH (rationalAtoms coords)) ≤ (q:ℝ) := by
  have hsym : (q • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)-rationalVariance coords).IsSymm :=
    (Matrix.isSymm_one.smul q).sub (rationalVariance_symm coords)
  rw [varianceTest,Option.isNone_iff_eq_none,KS.W17.rationalNegativeWitness_none_iff_psd _ _ hsym,
    cast_matrix_sub,cast_matrix_smul,cast_matrix_one,rationalVariance_cast]
  rw [← finRealify_one,← finRealify_smul,← finRealify_sub,finRealify_psd]
  change (q:ℝ) • (Hermitian.one : H d)-varianceH (rationalAtoms coords) ∈ psdCone d ↔ _
  rw [mem_psd_iff_nonneg,sub_nonneg]
  constructor
  · exact operatorNorm_le_of_psd_le (varianceH_psd _) (by exact_mod_cast hq)
  · intro h
    exact (le_operatorNorm_smul_one _).trans (scalar_one_mono h)

theorem varianceQuery_spec [NeZero d] [NeZero N] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
    let ν := varianceQuery coords
    let ν₀ := operatorNorm (varianceH (rationalAtoms coords))
    0 < ν ∧ ν ≤ 1 ∧ ν₀ ≤ (ν:ℝ) ∧ (ν:ℝ) ≤ (1001/1000:ℝ)*ν₀ := by
  have hd : 0 < d := NeZero.pos d
  have hN : 0 < N := NeZero.pos N
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  let A := rationalAtoms coords
  have hpos := varianceH_pos A hA htr
  have hle := operatorNorm_le_of_psd_le (varianceH_psd A) zero_le_one (by simpa using varianceH_le_one A hA hrank htr)
  have h := CurrentKS.RationalGrid.upper_spec (1000*N*d^2) (by positivity) (varianceTest coords)
    (operatorNorm (varianceH A)) hpos.le hle (fun k => by
      rw [varianceTest_spec coords _ (by positivity)]
      simp only [Rat.cast_div,Rat.cast_natCast]
      rfl)
  have hlow := variance_lower_paper A hA hrank htr
  refine ⟨by exact_mod_cast hpos.trans_le h.1,h.2.2,h.1,?_⟩
  apply h.2.1.trans
  have he : (1:ℝ)/(1000*N*d^2)=(1/1000)*(1/((N:ℝ)*d^2)) := by ring
  push_cast
  rw [he]
  linarith

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PenaltyParameter
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule
open CurrentKS.RationalRoot

lemma penaltyParameter_interval {N : ℕ} (hN : 0 < N) {ν : ℚ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) :
    Real.sqrt (ν:ℝ)/(200*N) ≤ (penaltyParameter N ν:ℝ) ∧
      (penaltyParameter N ν:ℝ) ≤ Real.sqrt (ν:ℝ)/(100*N) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hνr : (0:ℝ) < ν := by exact_mod_cast hν
  have hνr1 : (ν:ℝ) ≤ 1 := by exact_mod_cast hν1
  have hs := upperSqrt_spec ν ν hν hν.le hν1
  have hself : (ν:ℝ) ≤ Real.sqrt (ν:ℝ) := by
    nlinarith [Real.sq_sqrt hνr.le,Real.sqrt_nonneg (ν:ℝ)]
  have hup : (upperSqrt ν ν:ℝ) ≤ 2*Real.sqrt (ν:ℝ) := by linarith
  simp only [penaltyParameter,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]
  refine ⟨div_le_div_of_nonneg_right hs.1 (by positivity),?_⟩
  have hh := div_le_div_of_nonneg_right hup (show (0:ℝ) ≤ 200*N by positivity)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma penaltyParameter_pos_le {N : ℕ} (hN : 0 < N) {ν : ℚ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) :
    0 < penaltyParameter N ν ∧ penaltyParameter N ν ≤ 1 := by
  have hh := penaltyParameter_interval hN hν hν1
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hνr : (0:ℝ) < ν := by exact_mod_cast hν
  have hp : (0:ℝ) < penaltyParameter N ν :=
    (div_pos (Real.sqrt_pos.mpr hνr) (by positivity)).trans_le hh.1
  have hu : (penaltyParameter N ν:ℝ) ≤ 1 := by
    apply hh.2.trans
    apply (div_le_one (by positivity)).mpr
    have hs := Real.sqrt_le_one.mpr (show (ν:ℝ) ≤ 1 by exact_mod_cast hν1)
    linarith
  exact ⟨by exact_mod_cast hp,by exact_mod_cast hu⟩

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMatrixFold
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_fromBlocks _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_identityEntry _root_.OAI.CurrentKS.Realization.poly_identityMatrix _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_matrixEntry _root_.OAI.CurrentKS.Realization.poly_matrixMul _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natEq _root_.OAI.CurrentKS.Realization.poly_natLE _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_natToBinary _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_psdStored _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_transposeMatrix _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

lemma QParts.mono {H K : ℕ} {q : ℚ} (h : QParts H q) (hk : H≤K) : QParts K q :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by decide) hk),h.2.trans (Nat.pow_le_pow_right (by decide) hk)⟩
lemma qparts_zero (H : ℕ) : QParts H 0 := by constructor <;> simp [Nat.one_le_two_pow]
lemma qparts_length (q : ℚ) : QParts (ratCode q).length q := KS.W01.rational_parts_le_two_pow_length q
lemma QParts.add {H K : ℕ} {q r : ℚ} (hq : QParts H q) (hr : QParts K r) : QParts (H+K+1) (q+r) := by
  have ht := KS.W30.add_parts_le_two_pow _ _ _ _ hq.1 hq.2 hr.1 hr.2
  exact ⟨ht.1,ht.2.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩
lemma QParts.length {H : ℕ} {q : ℚ} (hq : QParts H q) : (ratCode q).length≤4*H+7 := by
  have h := KS.W01.ratLength_le_of_parts q H H hq.1 hq.2
  change KS.W01.ratLength q≤4*H+7
  omega

lemma getD_property {α : Type*} (P : α → Prop) (xs : List α) (a : α) (i : ℕ)
    (ha : P a) (hx : ∀x∈xs,P x) : P (xs.getD i a) := by
  by_cases h : i<xs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hx _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ha
lemma zipDefault_property {α β γ : Type*} (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    (f : α×β → γ) (a : α) (b : β) (xs : List α) (ys : List β)
    (ha : P a) (hb : Q b) (hx : ∀x∈xs,P x) (hy : ∀y∈ys,Q y)
    (hf : ∀ x y,P x → Q y → R (f (x,y))) :
    ∀z∈zipDefault f a b (xs,ys),R z := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
  exact hf _ _ (getD_property P xs a i ha hx) (getD_property Q ys b i hb hy)

lemma matrixParts_length (M : MatrixData) : MatrixParts (matrixCode M).length M := by
  intro row hr q hq
  exact (qparts_length q).mono ((mem_length_le_code row hq).trans (mem_length_le_code M hr))
lemma MatrixParts.mono {H K : ℕ} {M : MatrixData} (h : MatrixParts H M) (hk : H≤K) : MatrixParts K M :=
  fun row hr q hq => (h row hr q hq).mono hk

lemma matrixShape_length (M : MatrixData) : MatrixShape (matrixCode M).length M := by
  refine ⟨list_length_le_code _ _,?_⟩
  intro row hr
  exact (list_length_le_code _ _).trans (mem_length_le_code M hr)
lemma MatrixShape.mono {L K : ℕ} {M : MatrixData} (h : MatrixShape L M) (hk : L≤K) : MatrixShape K M :=
  ⟨h.1.trans hk,fun row hr => (h.2 row hr).trans hk⟩
lemma matrix_length_bound {H L : ℕ} {M : MatrixData} (hh : MatrixParts H M) (hs : MatrixShape L M) :
    (matrixCode M).length≤L*(2*(L*(2*(4*H+7)+1))+1) := by
  apply (listCode_length_bound M _ (fun row hr => ?_)).trans (Nat.mul_le_mul_right _ hs.1)
  exact (listCode_length_bound row _ (fun q hq => (hh row hr q hq).length)).trans (Nat.mul_le_mul_right _ (hs.2 row hr))

instance poly_accumMatrix : PolyTime accumMatrixRealizes := by
  unfold accumMatrixRealizes
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd
instance poly_normalPencil : PolyTime normalPencil := by unfold normalPencil;apply poly_then

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_QueryBits
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalBits

lemma Parts.abs_le {b : ℕ} {q : ℚ} (hq : Parts b q) : |q| ≤ (2:ℚ)^b := by
  have hnum : |(q.num:ℚ)| ≤ (2:ℚ)^b := by
    have hh : (q.num.natAbs:ℚ) ≤ (2:ℚ)^b := by exact_mod_cast hq.1
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  have hd : (1:ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  rw [←Rat.num_div_den q,abs_div,abs_of_pos (by positivity : (0:ℚ)<q.den)]
  apply (div_le_iff₀ (by positivity : (0:ℚ)<q.den)).mpr
  exact hnum.trans (le_mul_of_one_le_right (by positivity) hd)

end CurrentKS.RationalBits

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_RationalGridBits
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalGridSize

lemma Grid.zero (D : ℕ) : Grid D 0 := by simp [Grid]
lemma Grid.one (D : ℕ) : Grid D 1 := by simp [Grid]
lemma Grid.neg {D : ℕ} {q : ℚ} (hq : Grid D q) : Grid D (-q) := by
  simpa only [Grid,Rat.neg_den] using hq
lemma Grid.add {D : ℕ} {q r : ℚ} (hq : Grid D q) (hr : Grid D r) : Grid D (q+r) :=
  (Rat.add_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)
lemma Grid.sub {D : ℕ} {q r : ℚ} (hq : Grid D q) (hr : Grid D r) : Grid D (q-r) :=
  (Rat.sub_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)
lemma Grid.mul_integer {D : ℕ} {q : ℚ} (hq : Grid D q) (k : ℤ) : Grid D (q*(k:ℚ)) := by
  apply (Rat.mul_den_dvd q (k:ℚ)).trans
  simpa only [Grid,Rat.den_intCast,mul_one] using hq

lemma Grid.den_le {D : ℕ} (hD : 0 < D) {q : ℚ} (hq : Grid D q) : q.den ≤ D :=
  Nat.le_of_dvd hD hq

lemma numerator_le_den {q : ℚ} (hq : |q| ≤ 1) : q.num.natAbs ≤ q.den := by
  have hd : (0:ℚ) < q.den := by exact_mod_cast q.den_pos
  have hn : |(q.num:ℚ)|/(q.den:ℚ) ≤ 1 := by
    calc
      |(q.num:ℚ)|/(q.den:ℚ) = |(q.num:ℚ)/(q.den:ℚ)| := by rw [abs_div,abs_of_pos hd]
      _ = |q| := congrArg abs (Rat.num_div_den q)
      _ ≤ 1 := hq
  have hn' : |(q.num:ℚ)| ≤ (q.den:ℚ) := (div_le_one hd).mp hn
  have he : ((q.num.natAbs:ℕ):ℚ)=|(q.num:ℚ)| := by simp
  rw [← he] at hn'
  exact_mod_cast hn'

lemma coordinate_size_bound {D : ℕ} (hD : 0 < D) {q : ℚ}
    (hgrid : Grid D q) (hq : |q| ≤ 1) :
    q.num.natAbs ≤ D ∧ q.den ≤ D :=
  ⟨(numerator_le_den hq).trans (hgrid.den_le hD),hgrid.den_le hD⟩

open scoped BigOperators

lemma coordinate_bit_bound {D : ℕ} (hD : 0 < D) {q : ℚ}
    (hgrid : Grid D q) (hq : |q| ≤ 1) : bitSize q ≤ 2*D.size := by
  obtain ⟨hn,hd⟩ := coordinate_size_bound hD hgrid hq
  have hn' := Nat.size_le_size hn
  have hd' := Nat.size_le_size hd
  unfold bitSize
  omega

lemma size_mul_le (m n : ℕ) : (m*n).size ≤ m.size+n.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self m) (Nat.lt_size_self n)

lemma size_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∏ i∈s,f i).size ≤ 1+∑ i∈s,(f i).size := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    have hm := size_mul_le (f a) (∏ i∈s,f i)
    omega

end CurrentKS.RationalGridSize

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoots
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_fromBlocks _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_identityEntry _root_.OAI.CurrentKS.Realization.poly_identityMatrix _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_matrixEntry _root_.OAI.CurrentKS.Realization.poly_matrixMul _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natEq _root_.OAI.CurrentKS.Realization.poly_natLE _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_natToBinary _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_psdStored _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_transposeMatrix _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize

local notation "X" => NaturalPolynomial.variable

instance poly_ratNumBinary : PolyTime ratNumBinary := by unfold ratNumBinary;infer_instance
instance poly_unframeNat : PolyTime unframeNat := by unfold unframeNat;apply poly_reindex
instance poly_ratDenBinary : PolyTime ratDenBinary := by unfold ratDenBinary;apply poly_then
instance poly_ratDenSize : PolyTime ratDenSize := by unfold ratDenSize;infer_instance

lemma QParts.abs_le {H : ℕ} {q : ℚ} (h : QParts H q) : |q|≤(2:ℚ)^H :=
  RationalBits.Parts.abs_le h
lemma qparts_of_grid {D H K : ℕ} {q : ℚ} (hD : 0<D) (hg : Grid D q)
    (hd : D≤2^K) (hq : |q|≤(2:ℚ)^H) : QParts (H+K) q := by
  have hden := (hg.den_le hD).trans hd
  have he : |(q.num:ℚ)|=|q| * (q.den:ℚ) := by
    have h := congrArg abs (Rat.num_div_den q)
    rw [abs_div,abs_of_pos (by positivity : (0:ℚ)<q.den)] at h
    exact (div_eq_iff (by positivity : (q.den:ℚ)≠0)).mp h
  have hn : (q.num.natAbs:ℚ)≤(2:ℚ)^(H+K) := by
    rw [Nat.cast_natAbs,Int.cast_abs,he,pow_add]
    exact mul_le_mul hq (by exact_mod_cast hden) (by positivity) (by positivity)
  exact ⟨by exact_mod_cast hn,hden.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩
lemma grid_mono {D E : ℕ} {q : ℚ} (hg : Grid D q) (hd : D∣E) : Grid E q := hg.trans hd
lemma grid_mid {D : ℕ} {a b : ℚ} (ha : Grid D a) (hb : Grid D b) :
    Grid (D*2) ((a+b)/2) := by
  change ((a+b)/2).den∣D*2
  have h := Rat.mul_den_dvd (a+b) (1/2:ℚ)
  norm_num only [show (1/2:ℚ).den=2 from by norm_num] at h
  simpa only [div_eq_mul_inv,one_div,one_mul] using h.trans (Nat.mul_dvd_mul (ha.add hb) (dvd_refl 2))
lemma abs_mid {a b M : ℚ} (ha : |a|≤M) (hb : |b|≤M) : |(a+b)/2|≤M := by
  rw [abs_div,abs_of_pos (by norm_num : (0:ℚ)<2)]
  have ht := (abs_add_le a b).trans (add_le_add ha hb)
  linarith

lemma root_iterate_invariant (pow : ℕ) (q a b : ℚ) (k : ℕ) (M : ℚ)
    (ha : |a|≤M) (hb : |b|≤M) :
    let z := (rootStep pow)^[k] (q,(a,b))
    z.1=q ∧ Grid (a.den*b.den*2^k) z.2.1 ∧ Grid (a.den*b.den*2^k) z.2.2 ∧
      |z.2.1|≤M ∧ |z.2.2|≤M := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero,id_eq,pow_zero,mul_one]
    exact ⟨True.intro,Nat.dvd_mul_right _ _,Nat.dvd_mul_left _ _,ha,hb⟩
  | succ k ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    let z := (rootStep pow)^[k] (q,(a,b))
    have hd : a.den*b.den*2^(k+1)=(a.den*b.den*2^k)*2 := by rw [pow_succ];ring
    have hg : a.den*b.den*2^k∣a.den*b.den*2^(k+1) := by rw [hd];exact Nat.dvd_mul_right _ _
    have hm := grid_mid ih.2.1 ih.2.2.1
    rw [←hd] at hm
    have ham := abs_mid ih.2.2.2.1 ih.2.2.2.2
    change (rootStep pow z).1=q ∧ _
    dsimp only [rootStep]
    split
    · exact ⟨ih.1,hm,grid_mono ih.2.2.1 hg,ham,ih.2.2.2.2⟩
    · exact ⟨ih.1,grid_mono ih.2.1 hg,hm,ih.2.2.2.1,ham⟩

local instance poly_roots_pow {α : Type*} {encoding : α → Word} {value : α → ℚ}
    (routine : Realizes encoding ratCode value) [PolyTime routine] (exponent : ℕ) :
    PolyTime (routine.pow exponent) := by
  induction exponent with
  | zero => unfold Realizes.pow; infer_instance
  | succ exponent hypothesis =>
      let := hypothesis
      unfold Realizes.pow
      infer_instance

instance poly_rootStep (pow : ℕ) : PolyTime (rootStepRealizes pow) := by
  unfold rootStepRealizes;apply poly_congr
instance size_rootStep (pow : ℕ) : IterateSize (rootStepRealizes pow) := by
  refine ⟨⟨100*X+100,?_⟩⟩
  intro p k
  let L := (rootStateCode p).length
  have hq : (ratCode p.1).length≤L := le_prodCode_left p
  have ha : (ratCode p.2.1).length≤L := (le_prodCode_left p.2).trans (le_prodCode_right p)
  have hb : (ratCode p.2.2).length≤L := (le_prodCode_right p.2).trans (le_prodCode_right p)
  have hpa := (qparts_length p.2.1).mono ha
  have hpb := (qparts_length p.2.2).mono hb
  have hi := root_iterate_invariant pow p.1 p.2.1 p.2.2 k ((2:ℚ)^L) hpa.abs_le hpb.abs_le
  dsimp only at hi
  have hd : p.2.1.den*p.2.2.den*2^k≤2^(2*L+k) := by
    rw [pow_add,show 2*L=L+L by omega,pow_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hpa.2 hpb.2)
  have hD : 0<p.2.1.den*p.2.2.den*2^k := by positivity
  have hla := (qparts_of_grid hD hi.2.1 hd hi.2.2.2.1).length
  have hlb := (qparts_of_grid hD hi.2.2.1 hd hi.2.2.2.2).length
  change (ratCode ((rootStep pow)^[k] p).2.1).length≤_ at hla
  change (ratCode ((rootStep pow)^[k] p).2.2).length≤_ at hlb
  change (rootStateCode ((rootStep pow)^[k] p)).length≤100*(L+k)+100
  simp only [rootStateCode,prodCode_length]
  rw [hi.1]
  omega
instance poly_rootRun (pow : ℕ) : PolyTime (rootRun pow) := by unfold rootRun;infer_instance
instance poly_upperSqrt : PolyTime upperSqrt := by unfold upperSqrt;apply poly_congr
instance poly_approxPsi : PolyTime approxPsi := by unfold approxPsi;apply poly_congr
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoundedStep
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize
open scoped BigOperators

instance poly_roundedUpdate : PolyTime roundedUpdate := by unfold roundedUpdate;apply poly_then
instance poly_statePencil : PolyTime statePencil := by unfold statePencil;apply poly_then
instance poly_stateParameters : PolyTime stateParameters := by unfold stateParameters;apply poly_then
instance poly_stateY : PolyTime stateY := by unfold stateY;apply poly_then
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSearch
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_searchPencil : PolyTime searchPencil := by unfold searchPencil;apply poly_then
instance poly_searchParameters : PolyTime searchParameters := by unfold searchParameters;apply poly_then
instance poly_searchY : PolyTime searchY := by unfold searchY;apply poly_then
instance poly_searchDim : PolyTime searchDim := by unfold searchDim;infer_instance
instance poly_searchStep : PolyTime searchStepRealizes := by unfold searchStepRealizes;apply poly_div
instance poly_searchMesh : PolyTime searchMeshRealizes := by unfold searchMeshRealizes;apply poly_div
instance poly_searchInit : PolyTime searchInit := by unfold searchInit;apply poly_changeOutput

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOptimize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_optB : PolyTime optB := by unfold optB;apply poly_then
instance poly_optF : PolyTime optF := by unfold optF;apply poly_then
instance poly_optScalars : PolyTime optScalars := by unfold optScalars;apply poly_then
instance poly_optDelta : PolyTime optDelta := by unfold optDelta;apply poly_then
instance poly_optRest : PolyTime optRest := by unfold optRest;apply poly_then
instance poly_optRadius : PolyTime optRadius := by unfold optRadius;apply poly_both
instance poly_optUpper : PolyTime optUpper := by unfold optUpper;apply poly_then
instance poly_optLevel : PolyTime optLevel := by unfold optLevel;apply poly_add
instance poly_optLevelPencil : PolyTime optLevelPencil := by unfold optLevelPencil;apply poly_congr
instance poly_osP : PolyTime osP := by unfold osP;apply poly_then
instance poly_osK : PolyTime osK := by unfold osK;apply poly_then
instance poly_osY : PolyTime osY := by unfold osY;apply poly_then
instance poly_isPSD : PolyTime isPSD := by unfold isPSD;apply poly_congr

lemma RunsPoly.then_with {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
    {F : α → β} {G : β → γ} {ι : Type*} {L : ι → ℕ}
    {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a)
    (hs : IsPoly L (fun i => (eb (F (a i))).length) → RunsPoly L s (fun i => F (a i))) :
    RunsPoly L (r.then s) a := hr.then (hs hr.output)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialValueQuery
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_veP : PolyTime veP := by unfold veP;infer_instance
instance poly_veY : PolyTime veY := by unfold veY;infer_instance
instance poly_veD : PolyTime veD := by unfold veD;apply poly_then
instance poly_veN : PolyTime veN := by unfold veN;apply poly_then
instance poly_veEye : PolyTime veEye := by unfold veEye;apply poly_then
instance poly_veEps : PolyTime veEps := by unfold veEps;apply poly_then
instance poly_veTime : PolyTime veTime := by unfold veTime;apply poly_then
instance poly_sandwich : PolyTime sandwich := by unfold sandwich;apply poly_then
instance poly_tinyMatrix : PolyTime tinyMatrix := by unfold tinyMatrix;apply poly_then
instance poly_traceMatrix : PolyTime traceMatrix := by unfold traceMatrix;apply poly_then
instance poly_valueObjective : PolyTime valueObjective := by unfold valueObjective;apply poly_add
instance poly_valueCoeffs : PolyTime valueCoeffs := by unfold valueCoeffs;apply poly_then
instance poly_vqData : PolyTime vqData := by unfold vqData;apply poly_then
instance poly_vqDelta : PolyTime vqDelta := by unfold vqDelta;apply poly_then
instance poly_valueLipschitz : PolyTime valueLipschitz := by unfold valueLipschitz;apply poly_mul
instance poly_valueOuterRadius : PolyTime valueOuterRadius := by unfold valueOuterRadius;apply poly_mul
instance poly_valueInnerRadius : PolyTime valueInnerRadius := by unfold valueInnerRadius;apply poly_div
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialPotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_ppD : PolyTime ppD := by unfold ppD;apply poly_then
instance poly_ppRest : PolyTime ppRest := by unfold ppRest;apply poly_then
instance poly_ppAtoms : PolyTime ppAtoms := by unfold ppAtoms;apply poly_then
instance poly_ppArgs : PolyTime ppArgs := by unfold ppArgs;apply poly_then
instance poly_ppX : PolyTime ppX := by unfold ppX;apply poly_then
instance poly_ppScalars : PolyTime ppScalars := by unfold ppScalars;apply poly_then
instance poly_ppNu : PolyTime ppNu := by unfold ppNu;apply poly_then
instance poly_ppLam : PolyTime ppLam := by unfold ppLam;apply poly_then
instance poly_ppError : PolyTime ppError := by unfold ppError;apply poly_then
instance poly_ppN : PolyTime ppN := by unfold ppN;apply poly_congr
instance poly_ppRootTolerance : PolyTime ppRootTolerance := by unfold ppRootTolerance;apply poly_div
instance poly_ppTheta : PolyTime ppTheta := by unfold ppTheta;apply poly_congr
instance poly_ppQuery : PolyTime ppQuery := by unfold ppQuery;apply poly_changeOutput

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMatrixSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_approxPsi _root_.OAI.CurrentKS.Realization.poly_basisVector _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_fromBlocks _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_identityEntry _root_.OAI.CurrentKS.Realization.poly_identityMatrix _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_matrixEntry _root_.OAI.CurrentKS.Realization.poly_matrixMul _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natEq _root_.OAI.CurrentKS.Realization.poly_natLE _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_pencilFromEval _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_rootRun _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_transposeMatrix _root_.OAI.CurrentKS.Realization.poly_upperSqrt _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_zeroMatrix _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
lemma matrixAdd_shape {L : ℕ} (A B : MatrixData) (h : MatrixShape L A) :
    MatrixShape L (addMatrices A B) := by
  constructor
  · simpa only [addMatrices,zipDefault,List.length_map,List.length_range] using h.1
  · intro row hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simp only [zipDefault,List.length_map,List.length_range]
    exact getD_property (fun row : List ℚ => row.length≤L) A [] i (by simp) h.2
lemma matrixAdd_parts {H K : ℕ} (A B : MatrixData) (ha : MatrixParts H A) (hb : MatrixParts K B) :
    MatrixParts (H+K+1) (addMatrices A B) := by
  apply zipDefault_property (fun row => ∀q∈row,QParts H q) (fun row => ∀q∈row,QParts K q)
    (fun row => ∀q∈row,QParts (H+K+1) q) _ [] [] A B (by simp) (by simp) ha hb
  intro x y hx hy
  exact zipDefault_property _ _ _ _ 0 0 x y (qparts_zero _) (qparts_zero _) hx hy (fun a b ha hb => ha.add hb)
lemma matrixAdd_fold {L H : ℕ} (A : MatrixData) (xs : List MatrixData)
    (shape : MatrixShape L A) (parts : MatrixParts H A) (hp : ∀p∈xs,MatrixParts L p) :
    MatrixShape L (xs.foldl addMatrices A) ∧ MatrixParts (H+xs.length*(L+1)) (xs.foldl addMatrices A) := by
  induction xs generalizing A H with
  | nil => simpa using And.intro shape parts
  | cons x xs ih =>
    have h := ih (addMatrices A x) (matrixAdd_shape A x shape)
      (matrixAdd_parts A x parts (hp x (by simp))) (fun p hp' => hp p (by simp [hp']))
    simpa only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
instance size_matrixAdd : FoldSize matrixAdd := by
  refine ⟨⟨1000*(X+1)^4,?_⟩⟩
  intro A xs ys zs h
  let L := (prodCode matrixCode (listCode matrixCode) (A,xs)).length
  have ha : (matrixCode A).length≤L := le_prodCode_left (A,xs)
  have hy : (listCode matrixCode ys).length≤L :=
    (prefix_code_length _ xs ys zs h).trans (le_prodCode_right (A,xs))
  have hn := (list_length_le_code _ _).trans hy
  have ht := matrixAdd_fold A ys ((matrixShape_length A).mono ha) ((matrixParts_length A).mono ha)
    (fun p hp => (matrixParts_length p).mono ((mem_length_le_code ys hp).trans hy))
  have he := matrix_length_bound ht.2 ht.1
  apply he.trans
  change L*(2*(L*(2*(4*(L+ys.length*(L+1))+7)+1))+1)≤1000*(L+1)^4
  calc
    _≤L*(2*(L*(2*(4*(L+L*(L+1))+7)+1))+1) := by gcongr
    _≤_ := by nlinarith [Nat.zero_le L, sq_nonneg (L:ℤ)]
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialVariance
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppQuery _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppTheta _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_valueCoeffs _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
instance poly_mgN : PolyTime mgN := by unfold mgN;apply poly_then
instance poly_mgRest : PolyTime mgRest := by unfold mgRest;apply poly_then
instance poly_mgM : PolyTime mgM := by unfold mgM;apply poly_then
instance poly_mgDen : PolyTime mgDen := by unfold mgDen;apply poly_then
instance poly_mgShift : PolyTime mgShift := by unfold mgShift;apply poly_changeOutput
instance poly_mgTest : PolyTime mgTest := by unfold mgTest;apply poly_congr
instance poly_gridStep : PolyTime gridStep := by
  unfold gridStep
  apply PolyTime.both
  · infer_instance
  · apply PolyTime.both
    · infer_instance
    · apply PolyTime.ite <;> infer_instance
lemma gridStep_iterate_bounds (s : MatrixGrid×(ℕ×ℕ)) (L n : ℕ)
    (h1 : s.2.1≤L) (h2 : s.2.2≤L) :
    (gridStepData^[n] s).1=s.1 ∧ (gridStepData^[n] s).2.1≤L+n ∧
      (gridStepData^[n] s).2.2≤L+n := by
  induction n with
  | zero => simp only [Function.iterate_zero,id_eq,Nat.add_zero];exact ⟨trivial,h1,h2⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [gridStepData]
    refine ⟨ih.1,by omega,?_⟩
    split <;> omega
instance size_gridStep : IterateSize gridStep := by
  refine ⟨⟨10*X+10,?_⟩⟩
  intro s n
  let L := (gridStateCode s).length
  have hp : (matrixGridCode s.1).length≤L := le_prodCode_left s
  have h1 : s.2.1≤L := by
    have h := (le_prodCode_left (ea:=natCode) (eb:=natCode) s.2).trans (le_prodCode_right (ea:=matrixGridCode) s)
    simpa only [natCode,List.length_replicate] using h
  have h2 : s.2.2≤L := by
    have h := (le_prodCode_right (ea:=natCode) (eb:=natCode) s.2).trans (le_prodCode_right (ea:=matrixGridCode) s)
    simpa only [natCode,List.length_replicate] using h
  have h := gridStep_iterate_bounds s L n h1 h2
  change (gridStateCode (gridStepData^[n] s)).length≤10*(L+n)+10
  simp only [gridStateCode,prodCode_length,natCode,List.length_replicate,h.1]
  omega
instance poly_gridUpper : PolyTime gridUpper := by unfold gridUpper;apply poly_congr
instance poly_fVariance : PolyTime fVariance := by unfold fVariance;apply poly_congr

lemma isPoly_faceD : IsPoly (fun p : FaceParams => (faceCode p).length) FaceParams.d := by
  have h := (RunsPoly.of_poly fD id (isPoly_self _)).output
  simp only [natCode,List.length_replicate,id_eq] at h
  exact h
lemma isPoly_faceN : IsPoly (fun p : FaceParams => (faceCode p).length) FaceParams.N := by
  have h := (RunsPoly.of_poly (fBase.then (lengthList ratCode)) id (isPoly_self _)).output
  simpa only [natCode,List.length_replicate,List.length_ofFn,id_eq] using h
lemma varianceDen_ceil (p : FaceParams) :
    ⌈(p.N:ℚ)*1000*(p.d:ℚ)^2⌉₊=1000*p.N*p.d^2 := by
  have he : (p.N:ℚ)*1000*(p.d:ℚ)^2=((1000*p.N*p.d^2:ℕ):ℚ) := by push_cast <;> ring
  rw [he,Nat.ceil_natCast]
instance poly_varianceDen : PolyTime
    (((((fBase.then (lengthList ratCode)).then natToRat).mul (constant faceCode ratCode 1000)).mul
      ((fD.then natToRat).pow 2)).then ratCeil) := by
  have he : IsPoly (fun p : FaceParams => (faceCode p).length)
      (fun p => ⌈((List.ofFn p.base).length:ℚ)*1000*(p.d:ℚ)^2⌉₊) := by
    simp only [List.length_ofFn,varianceDen_ceil]
    exact ((isPoly_const _ 1000).mul isPoly_faceN).mul (isPoly_faceD.pow 2)
  have h := RunsPoly.then_with
    (RunsPoly.of_poly ((((fBase.then (lengthList ratCode)).then natToRat).mul (constant faceCode ratCode 1000)).mul
      ((fD.then natToRat).pow 2)) id (isPoly_self _))
    (fun hw => runsPoly_ratCeil _ hw he)
  exact ⟨h.cost⟩
instance poly_fVarianceGrid : PolyTime fVarianceGrid := by unfold fVarianceGrid;apply poly_changeOutput
instance poly_varianceQuery : PolyTime varianceQuery := by unfold varianceQuery;apply poly_then
instance poly_faceNormalized : PolyTime faceNormalized := by unfold faceNormalized;apply poly_changeOutput
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_StoredBits
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faceNormalized _root_.OAI.CurrentKS.Realization.poly_gridUpper _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_upperSqrt _root_.OAI.CurrentKS.Realization.poly_varianceQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.ScheduleBits
open CurrentKS.RationalBits

private lemma eps_bits : LinearBits eps := by unfold eps;(with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma strip_bits : LinearBits strip := by unfold strip;(with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma movement_bits : LinearBits movement := by
  have he := eps_bits
  unfold movement
  dsimp only
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma coarse_bits : LinearBits coarse := by
  have he := eps_bits
  have hs := strip_bits
  unfold coarse
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma jacobian_bits : LinearBits jacobian := by
  have he := eps_bits
  unfold jacobian
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma derivative_bits : LinearBits derivative := by
  have hc := coarse_bits
  unfold derivative
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma second_bits : LinearBits second := by
  have he := eps_bits
  have hj := jacobian_bits
  have hd := derivative_bits
  unfold second
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma third_bits : LinearBits third := by
  have he := eps_bits
  have hj := jacobian_bits
  have hd := derivative_bits
  unfold third
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma curvature_bits : LinearBits curvature := by
  have hs := strip_bits
  have h2 := second_bits
  have h3 := third_bits
  unfold curvature
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma threshold_bits : LinearBits threshold := by
  have hm := movement_bits
  unfold threshold
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma step_bits : LinearBits step := by
  have hs := strip_bits
  have ht := threshold_bits
  have hc := curvature_bits
  unfold step
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))
private lemma mesh_bits : LinearBits mesh := by
  have hs := step_bits
  have ht := threshold_bits
  have hc := curvature_bits
  unfold mesh
  (with_reducible repeat' (first | assumption | exact LinearBits.coordinate _ | exact LinearBits.constant _ | apply LinearBits.add | apply LinearBits.mul | apply LinearBits.div | apply LinearBits.inv | apply LinearBits.pow | apply LinearBits.abs | apply LinearBits.min | apply LinearBits.max))

lemma step_eq (d n:ℕ) (ν lam:ℚ) :
    step (args d n ν lam)=(CurrentKS.Schedule.parameters d n ν lam).s := rfl
private lemma mesh_eq (d n:ℕ) (ν lam:ℚ) :
    mesh (args d n ν lam)=(CurrentKS.Schedule.parameters d n ν lam).ρ := rfl

theorem schedule_parts_linear : ∃ C:ℕ, 0<C ∧ ∀ (d n : ℕ) (ν lam : ℚ) (b : ℕ),
    Parts b (d:ℚ) → Parts b (n:ℚ) → Parts b ν → Parts b lam →
    Parts (C*(b+1)) (CurrentKS.Schedule.parameters d n ν lam).s ∧
      Parts (C*(b+1)) (CurrentKS.Schedule.parameters d n ν lam).ρ := by
  obtain ⟨C,hC,hstep⟩ := step_bits
  obtain ⟨D,hD,hmesh⟩ := mesh_bits
  refine ⟨C+D,by omega,?_⟩
  intro d n ν lam b hd hn hν hl
  have hx : ∀i,Parts b (args d n ν lam i) := by
    intro i
    fin_cases i <;> simp only [args] <;> assumption
  have hs := (hstep b (args d n ν lam) hx).mono (show C*(b+1)≤(C+D)*(b+1) by nlinarith)
  have hm := (hmesh b (args d n ν lam) hx).mono (show D*(b+1)≤(C+D)*(b+1) by nlinarith)
  rw [step_eq] at hs
  rw [mesh_eq] at hm
  exact ⟨hs,hm⟩
end CurrentKS.ScheduleBits
namespace CurrentKS.RationalBits
open CurrentKS.RationalGridSize

lemma Parts.natCast {b n : ℕ} (hn : n ≤ 2^b) : Parts b (n:ℚ) := by
  constructor
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using hn
  · simpa only [Rat.den_natCast] using Nat.one_le_two_pow

lemma natCast_parts (n : ℕ) : Parts n.size (n:ℚ) := Parts.natCast (Nat.lt_size_self n).le

end CurrentKS.RationalBits

namespace CurrentKS.RationalGridSize

lemma Grid.mono {D E : ℕ} {q : ℚ} (hq : Grid D q) (hDE : D ∣ E) : Grid E q := hq.trans hDE

lemma Grid.half {D : ℕ} {q : ℚ} (hq : Grid D q) : Grid (D*2) (q/2) := by
  rw [div_eq_mul_inv]
  apply (Rat.mul_den_dvd q ((2:ℚ)⁻¹)).trans
  norm_num
  exact Nat.mul_dvd_mul_right hq 2

end CurrentKS.RationalGridSize

namespace CurrentKS.RationalRoot
open CurrentKS.RationalGridSize CurrentKS.RationalBits

lemma squareInterval_grid (q : ℚ) (k : ℕ) :
    Grid (2^k) (squareInterval q k).1 ∧ Grid (2^k) (squareInterval q k).2 := by
  induction k with
  | zero => exact ⟨Grid.zero _,Grid.one _⟩
  | succ k ih =>
    have hm := (ih.1.add ih.2).half
    have hlow := ih.1.mono (dvd_mul_right (2^k) 2)
    have hupp := ih.2.mono (dvd_mul_right (2^k) 2)
    simp only [squareInterval]
    split
    · simpa only [pow_succ] using And.intro hm hupp
    · simpa only [pow_succ] using And.intro hlow hm

lemma squareInterval_cube (q : ℚ) (k : ℕ) :
    0 ≤ (squareInterval q k).1 ∧ (squareInterval q k).1 ≤ (squareInterval q k).2 ∧
      (squareInterval q k).2 ≤ 1 := by
  induction k with
  | zero => norm_num [squareInterval]
  | succ k ih =>
    simp only [squareInterval]
    split <;> dsimp only <;> constructor
    · linarith [ih.1,ih.2.1]
    · exact ⟨by linarith [ih.2.1],ih.2.2⟩
    · exact ih.1
    · constructor <;> linarith [ih.2.1,ih.2.2]

lemma upperSqrt_parts (q δ : ℚ) : Parts δ.den.size (upperSqrt q δ) := by
  have hg := (squareInterval_grid q δ.den.size).2
  have hc := squareInterval_cube q δ.den.size
  have ha : |upperSqrt q δ| ≤ 1 := by
    change |(squareInterval q δ.den.size).2| ≤ 1
    rw [abs_of_nonneg (hc.1.trans hc.2.1)]
    exact hc.2.2
  exact coordinate_size_bound (by positivity) hg ha
end CurrentKS.RationalRoot

namespace CurrentKS.RationalGrid
open CurrentKS.RationalBits

lemma upper_parts (den : ℕ) (test : ℚ → Bool) : Parts (2*den.size) (upper den test) := by
  have hn : Parts den.size (upperIndex den test den:ℚ) :=
    Parts.natCast ((upperIndex_le den test den).trans (Nat.lt_size_self den).le)
  simp only [two_mul]
  exact hn.div (natCast_parts den)
end CurrentKS.RationalGrid

namespace CurrentKS.RationalFace
open CurrentKS.RationalBits CurrentKS.RationalRoot CurrentKS.RationalSDP CurrentKS.Schedule
open scoped BigOperators

variable {d N : ℕ}

lemma variance_parts (coords : Fin N → Fin d × Fin d → ℚ) :
    Parts (2*(1000*N*d^2).size) (varianceQuery coords) :=
  CurrentKS.RationalGrid.upper_parts _ _

lemma penalty_parts (ν : ℚ) (N b : ℕ) (hν : Parts b ν) :
    Parts (b+1+(200*N).size) (penaltyParameter N ν) := by
  have hd : ν.den.size ≤ b+1 := by simpa only [Nat.size_pow] using Nat.size_le_size hν.2
  have hu := (upperSqrt_parts ν ν).mono hd
  have hc : Parts (200*N).size ((200:ℚ)*N) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using natCast_parts (200*N)
  exact hu.div hc

lemma base_parts (coords : Fin N → Fin d × Fin d → ℚ) (n : ℕ) (hn : n ≤ N) :
    Parts (baseBits d N) (d:ℚ) ∧ Parts (baseBits d N) (n:ℚ) ∧
      Parts (baseBits d N) (varianceQuery coords) ∧
      Parts (baseBits d N) (penaltyParameter N (varianceQuery coords)) := by
  have hν := variance_parts coords
  have hlam := penalty_parts (varianceQuery coords) N _ hν
  refine ⟨(natCast_parts d).mono ?_,(natCast_parts n).mono ?_,hν.mono ?_,hlam.mono ?_⟩
  all_goals dsimp only [baseBits]
  · omega
  · have h := Nat.size_le_size hn;omega
  · omega
  · omega

end CurrentKS.RationalFace
namespace CurrentKS.RationalRoot
open CurrentKS.RationalGridSize

variable {N : ℕ}

lemma roundMesh_grid {D : ℕ} {ρ : ℚ} (hρ : Grid D ρ) (v : Fin N → ℚ) :
    ∀ i,Grid D (roundMesh ρ v i) :=
  fun i => hρ.mul_integer (nearest (v i/ρ))

lemma computedCurvature_grid {D : ℕ} (H : Matrix (Fin N) (Fin N) ℚ)
    (a M s ρ : ℚ) (hρ : Grid D ρ) (q : Fin N → ℚ)
    (hq : computedCurvature H a M s ρ=some q) : ∀ i,Grid D (q i) := by
  unfold computedCurvature at hq
  cases he : negativeDirection (shiftedHessian H a) (a/(4096*M)) with
  | none => simp only [he,Option.map_none] at hq;cases hq
  | some w =>
    simp only [he,Option.map_some,Option.some.injEq] at hq
    subst q
    exact roundMesh_grid hρ _

end CurrentKS.RationalRoot

namespace CurrentKS.Difference
open CurrentKS.RationalGridSize CurrentKS.RationalRoot

variable {N : ℕ}

lemma gradientStep_grid [NeZero N] {D : ℕ} (s : ℚ) (g : Fin N → ℚ)
    (hs : Grid D s) : ∀ i,Grid D ((s • rationalGradientDirection g) i) := by
  intro i
  simp only [rationalGradientDirection,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  split_ifs <;> simp only [mul_neg,mul_one,mul_zero]
  all_goals first | exact hs | exact hs.neg | exact Grid.zero D

lemma interiorCandidates_grid [NeZero N] {D : ℕ}
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h a M s ρ : ℚ)
    (hx : ∀ i,Grid D (x i)) (hs : Grid D s) (hρ : Grid D ρ) :
    ∀ y∈interiorCandidates query x h a M s ρ,∀ i,Grid D (y i) := by
  intro y hy
  simp only [interiorCandidates,List.mem_cons] at hy
  rcases hy with rfl|hy
  · exact fun i => (hx i).add (gradientStep_grid s _ hs i)
  · cases he : computedCurvature (stencilHessian query x h) a M s ρ with
    | none => simp only [he,List.not_mem_nil] at hy
    | some q =>
      have hq := computedCurvature_grid _ a M s ρ hρ q he
      simp only [he,List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl|rfl
      · exact fun i => (hx i).add (hq i)
      · exact fun i => (hx i).sub (hq i)

lemma endpointCandidates_grid {D : ℕ} (x : Fin N → ℚ) (hx : ∀ i,Grid D (x i)) :
    ∀ y∈endpointCandidates x,∀ i,Grid D (y i) := by
  intro y hy j
  obtain ⟨i,_,hy⟩ := List.mem_flatMap.mp hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl|rfl
  all_goals
    by_cases hji : j=i
    · subst j;simp only [Function.update_self]
      exact (Grid.one D).neg
    · simpa only [Function.update_of_ne hji] using hx j

lemma allCandidates_grid [NeZero N] {D : ℕ}
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h a M s ρ : ℚ)
    (hx : ∀ i,Grid D (x i)) (hs : Grid D s) (hρ : Grid D ρ) :
    ∀ y∈allCandidates query x h a M s ρ,∀ i,Grid D (y i) := by
  intro y hy
  rcases List.mem_append.mp hy with he|hi
  · exact endpointCandidates_grid x hx y he
  · exact interiorCandidates_grid query x h a M s ρ hx hs hρ y hi

end CurrentKS.Difference

namespace CurrentKS.RationalFace

section
open CurrentKS.RationalGridSize CurrentKS.Schedule CurrentKS.Descent CurrentKS.Difference
open scoped BigOperators

variable {d N n : ℕ}

lemma meshDenominator_pos (d N : ℕ) (ν lam : ℚ) : 0 < meshDenominator d N ν lam := by
  apply Finset.prod_pos
  intro n _
  exact Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _)

lemma schedule_grid (d N n : ℕ) (ν lam : ℚ) (hn : n ≤ N) :
    Grid (meshDenominator d N ν lam) (parameters d n ν lam).s ∧
    Grid (meshDenominator d N ν lam) (parameters d n ν lam).ρ := by
  have hprod := Finset.dvd_prod_of_mem
    (fun n => (parameters d n ν lam).s.den*(parameters d n ν lam).ρ.den)
    (Finset.mem_range.mpr (show n < N+1 by omega))
  exact ⟨(dvd_mul_right _ _).trans hprod,(dvd_mul_left _ _).trans hprod⟩

lemma extend_grid {D : ℕ} (e : Fin n → Fin N) (x : Fin N → ℚ) (y : Fin n → ℚ)
    (hx : ∀ i,Grid D (x i)) (hy : ∀ i,Grid D (y i)) : ∀ i,Grid D (extend e x y i) := by
  intro i
  unfold extend
  cases lookup e i with
  | none => exact hx i
  | some j => exact hy j

lemma freezeOne_grid {D : ℕ} (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,Grid D (x i))
    (i : Fin N) : ∀ j,Grid D (freezeOne σ x i j) := by
  intro j
  unfold freezeOne
  split_ifs
  · by_cases hji : j=i
    · subst j
      simp only [Function.update_self,nearestEndpoint]
      split_ifs
      · exact Grid.one D
      · exact (Grid.one D).neg
    · simpa only [Function.update_of_ne hji] using hx j
  · exact hx j

lemma freezeList_grid {D : ℕ} (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,Grid D (x i))
    (l : List (Fin N)) : ∀ i,Grid D (freezeList σ x l i) := by
  induction l generalizing x with
  | nil => exact hx
  | cons i l ih => exact ih _ (freezeOne_grid σ x hx i)

lemma faceChoice_grid (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (ν lam : ℚ) [NeZero (activeIndices base).length]
    (hx : ∀ i,Grid (meshDenominator d N ν lam) (base i)) :
    ∀ i,Grid (meshDenominator d N ν lam) (faceChoice coords base ν lam i) := by
  have hm := select_mem (faceScore coords base ν lam) (faceState base)
    (faceCandidates coords base ν lam)
  have hp := schedule_grid d N (activeIndices base).length ν lam (activeIndices_length_le base)
  rcases List.mem_cons.mp hm with h|h
  · simp only [faceChoice,h]
    exact (fun i => hx (activeIndex base i))
  · exact allCandidates_grid _ _ _ _ _ _ _ (fun i => hx (activeIndex base i)) hp.1 hp.2 _ h

lemma transition_grid (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ)
    (x y : Fin N → ℚ) (hx : ∀ i,Grid (meshDenominator d N ν lam) (x i))
    (hs : transition coords ν lam x=some y) :
    ∀ i,Grid (meshDenominator d N ν lam) (y i) := by
  by_cases hn : (activeIndices x).length=0
  · simp only [transition,dite_eq_left hn] at hs;cases hs
  · let : NeZero (activeIndices x).length := ⟨hn⟩
    have he : y=freezeAll (lam^2/ν) (extend (activeIndex x) x (faceChoice coords x ν lam)) := by
      simpa only [transition,dite_eq_right hn,Option.some.injEq] using hs.symm
    rw [he]
    exact freezeList_grid _ _ (extend_grid _ _ _ hx (faceChoice_grid coords x ν lam hx)) _

end
open CurrentKS.RationalBits CurrentKS.RationalGridSize CurrentKS.ScheduleBits
open CurrentKS.Schedule CurrentKS.RationalSDP CurrentKS.Descent
open KS.W23
open scoped BigOperators

variable {d N : ℕ}

lemma baseBits_le (B : ℕ) (hd : d ≤ B) (hN : N ≤ B) : baseBits d N ≤ baseBitsP.eval B := by
  have hs (n : ℕ) : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self
  change d.size+N.size+2*(1000*N*d^2).size+1+(200*N).size ≤
    B+B+2*(1000*B*B^2)+1+200*B
  apply Nat.add_le_add
  · apply Nat.add_le_add_right
    apply Nat.add_le_add
    · exact Nat.add_le_add ((hs d).trans hd) ((hs N).trans hN)
    · apply Nat.mul_le_mul_left
      apply (hs _).trans
      gcongr
  · exact (hs _).trans (Nat.mul_le_mul_left _ hN)

lemma mesh_bits_bound (C : ℕ) (b : ℕ) (ν lam : ℚ)
    (hs : ∀ n ≤ N, Parts (C*(b+1)) (parameters d n ν lam).s ∧
      Parts (C*(b+1)) (parameters d n ν lam).ρ) :
    (meshDenominator d N ν lam).size ≤ 1+(N+1)*(2*(C*(b+1)+1)) := by
  apply (size_prod_le (Finset.range (N+1))
    (fun n => (parameters d n ν lam).s.den*(parameters d n ν lam).ρ.den)).trans
  apply Nat.add_le_add_left
  calc
    ∑ n∈Finset.range (N+1),((parameters d n ν lam).s.den*(parameters d n ν lam).ρ.den).size
        ≤ ∑ _n∈Finset.range (N+1),2*(C*(b+1)+1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := hs n (by have := Finset.mem_range.mp hn;omega)
      have h1 : (parameters d n ν lam).s.den.size ≤ C*(b+1)+1 := by
        simpa only [Nat.size_pow] using Nat.size_le_size hh.1.2
      have h2 : (parameters d n ν lam).ρ.den.size ≤ C*(b+1)+1 := by
        simpa only [Nat.size_pow] using Nat.size_le_size hh.2.2
      exact (size_mul_le _ _).trans (by omega)
    _ = (N+1)*(2*(C*(b+1)+1)) := by simp

theorem normalized_mesh_polynomial : ∃ C : ℕ, 0<C ∧
    ∀ (d N : ℕ) (coords : Fin N → Fin d × Fin d → ℚ),
      (meshDenominator d N (varianceQuery coords) (penaltyParameter N (varianceQuery coords))).size ≤
        (meshBitsP C).eval (d+N) := by
  obtain ⟨C,hC,hs⟩ := schedule_parts_linear
  refine ⟨C,hC,?_⟩
  intro d N coords
  have hh := mesh_bits_bound (d:=d) (N:=N) C (baseBits d N)
    (varianceQuery coords) (penaltyParameter N (varianceQuery coords)) (fun n hn => by
      have hb := base_parts coords n hn
      exact hs d n _ _ _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2)
  apply hh.trans
  change 1+(N+1)*(2*(C*(baseBits d N+1)+1)) ≤
    1+(d+N+1)*(2*(C*(baseBitsP.eval (d+N)+1)+1))
  have hb := baseBits_le (d+N) (Nat.le_add_right d N) (Nat.le_add_left N d)
  gcongr
  omega

lemma run_grid (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ) (k : ℕ) :
    ∀ i, Grid (meshDenominator d N ν lam)
      (run (transition coords ν lam) k (freezeAll (lam^2/ν) 0) i) := by
  apply run_invariant (transition coords ν lam)
    (fun x => ∀ i,Grid (meshDenominator d N ν lam) (x i))
    (fun x y hx hs => transition_grid coords ν lam x y hx hs)
  exact freezeList_grid _ _ (fun _ => Grid.zero _) _

noncomputable section
open CurrentKS.Hermitian CurrentKS.State
open scoped MatrixOrder Matrix.Norms.Frobenius

lemma run_cube [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0<lam) (hlam1 : lam≤1)
    (hvar : varianceH (rationalAtoms coords) ≤ (ν:ℝ) • (Hermitian.one : H d)) (k : ℕ) :
    ∀ i, |run (transition coords ν lam) k (freezeAll (lam^2/ν) 0) i| ≤ 1 := by
  have hP := run_invariant (transition coords ν lam) (StripCube (lam^2/ν))
    (fun x y hx hs => (transition_spec coords hA hA0 hrank htr hν hν1 hlam hlam1 hvar x y hx hs).1)
    k (freezeAll (lam^2/ν) 0) (freezeAll_stripCube (lam^2/ν) 0 (by simp))
  exact hP.1

theorem normalized_stored_bits_polynomial : ∃ p : NaturalPolynomial,
    ∀ (d N : ℕ) [NeZero d] [NeZero N] (coords : Fin N → Fin d × Fin d → ℚ),
    (∀ i,rationalAtoms coords i∈psdCone d) → (∀ i,rationalAtoms coords i≠0) →
    (∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1) →
    (∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) →
    ∀ k i, let ν := varianceQuery coords; let lam := penaltyParameter N ν
      bitSize (run (transition coords ν lam) k (freezeAll (lam^2/ν) 0) i) ≤ p.eval (d+N) := by
  obtain ⟨C,_,hC⟩ := normalized_mesh_polynomial
  refine ⟨storedBitsP C,?_⟩
  intro d N _ _ coords hA hA0 hrank htr k i
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hl := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have hvar : varianceH (rationalAtoms coords) ≤ (ν:ℝ) • (Hermitian.one : H d) :=
    (le_operatorNorm_smul_one _).trans (scalar_one_mono hν.2.2.1)
  have hc := run_cube coords hA hA0 hrank htr hν.1 hν.2.1 hl.1 hl.2 hvar k i
  have hb := coordinate_bit_bound (meshDenominator_pos d N ν lam) (run_grid coords ν lam k i) hc
  exact hb.trans (Nat.mul_le_mul_left 2 (hC d N coords))
end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceOrbit
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalSDP Hermitian
open scoped BigOperators MatrixOrder

lemma orbit_eq (p : FaceParams) (k : ℕ) :
    p.orbit k={p.normal with base := (Descent.run
      (RationalFace.transition p.coords p.normal.nu p.normal.lam) k
      (RationalFace.freezeAll (p.normal.lam^2/p.normal.nu) 0))} := by
  unfold FaceParams.orbit
  rw [next_iterate]
  rfl
lemma qparts_bitSize (q : ℚ) : QParts (RationalGridSize.bitSize q) q := by
  constructor
  · exact (Nat.lt_size_self q.num.natAbs).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · exact (Nat.lt_size_self q.den).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
lemma faceCode_base_bound (p : FaceParams) (v : Fin p.N → ℚ) :
    (faceCode {p with base := v}).length≤(faceCode p).length+2*(vectorCode (List.ofFn v)).length := by
  simp only [faceCode,FaceParams.data,faceDataCode,prodCode_length]
  omega
lemma orbit_wire_bound : ∃ q : NaturalPolynomial,∀p : FaceParams,p.GoodAtoms →∀k,
    (faceCode (p.orbit k)).length≤(faceCode p.normal).length+
      p.N*(2*(4*q.eval (p.d+p.N)+7)+1)*2 := by
  obtain ⟨q,hq⟩ := RationalFace.normalized_stored_bits_polynomial
  refine ⟨q,?_⟩
  intro p hp k
  let : NeZero p.d := ⟨hp.d_ne⟩
  let : NeZero p.N := ⟨hp.N_ne⟩
  rw [orbit_eq]
  apply (faceCode_base_bound p.normal _).trans
  apply Nat.add_le_add_left
  rw [Nat.mul_comm 2]
  apply Nat.mul_le_mul_right
  calc
    _≤(List.ofFn (Descent.run (RationalFace.transition p.coords p.normal.nu p.normal.lam) k
      (RationalFace.freezeAll (p.normal.lam^2/p.normal.nu) 0))).length*(2*(4*q.eval (p.d+p.N)+7)+1) := by
      apply listCode_length_bound
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact ((qparts_bitSize _).mono (hq p.d p.N p.coords hp.positive hp.nonzero hp.rank hp.trace k i)).length
    _=_ := by rw [List.length_ofFn]

variable {ι : Type*} {L : ι → ℕ}
lemma isPoly_face_dimensions (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) :
    IsPoly L (fun i => (a i).d+(a i).N) := by
  have hd := (RunsPoly.of_poly fD a ha).output
  have hn := (RunsPoly.of_poly (fBase.then (lengthList ratCode)) a ha).output
  have h := hd.add hn
  simp only [natCode,List.length_replicate,List.length_ofFn] at h
  exact h
lemma isPoly_face_orbit_oai (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    IsPoly (fun s : ι×ℕ => L s.1) (fun s => (faceCode ((a s.1).orbit s.2)).length) := by
  obtain ⟨q,hq⟩ := orbit_wire_bound
  have hdim := isPoly_face_dimensions a ha
  have hn : IsPoly L (fun i => (faceCode (a i).normal).length) :=
    (RunsPoly.of_poly faceNormalized a ha).output
  have h := hn.add ((hdim.mul ((((isPoly_const L 4).mul (hdim.eval q)).add
    (isPoly_const L 7)).mul (isPoly_const L 2) |>.add (isPoly_const L 1))).mul (isPoly_const L 2))
  apply (h.reindex Prod.fst).mono
  intro s
  apply (hq (a s.1) (hg s.1) s.2).trans
  dsimp only [Function.comp_apply]
  have hb : (a s.1).N≤(a s.1).d+(a s.1).N := Nat.le_add_left _ _
  nlinarith
end CurrentKS.Realization

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CurrentKS.Realization.isPoly_face_orbit_oai.{u_1} := @OAI.CurrentKS.Realization.isPoly_face_orbit_oai.{u_1}
