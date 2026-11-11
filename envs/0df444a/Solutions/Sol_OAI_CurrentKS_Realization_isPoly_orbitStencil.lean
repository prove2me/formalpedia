-- Prove2me | solution 1 for OAI.CurrentKS.Realization.isPoly_orbitStencil
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:02.658283+00:00
-- url     : https://prove2.me/submissions/899a81c3-d915-4b37-a123-aaae45cd0408

import Mathlib
import Definitions.Def_OAIQ241TT009

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_rcb7817_1 : NormedSpace ℝ (H d) := inferInstance
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

lemma coarseBudget_bounds {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    1 ≤ coarseBudget d N ε σ ∧ (d:ℝ)+1 ≤ coarseBudget d N ε σ ∧
    |ε| ≤ coarseBudget d N ε σ ∧
    200+(200/ε)*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    200*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    ((d:ℝ)+1)+N ≤ coarseBudget d N ε σ ∧
    384*N*(1+800/σ^3) ≤ coarseBudget d N ε σ := by
  have hd : 0 ≤ (d:ℝ)+1 := by positivity
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hp : 0 ≤ (200/ε)*((d:ℝ)+1) := by positivity
  have hr : 0 ≤ 384*(N:ℝ)*(1+800/σ^3) := by positivity
  have he := abs_nonneg ε
  dsimp [coarseBudget]
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

end
end CurrentKS.State

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FacePotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar CurrentKS.Calculus
open scoped BigOperators ContDiff

variable {d N : ℕ}

open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff


lemma valueCurve_bounds_nonneg {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    0 ≤ valueCurve2Bound d N ε σ ∧ 0 ≤ valueCurve3Bound d N ε σ := by
  have hB := (coarseBudget_bounds (d:=d) (N:=N) hε hσ).1
  dsimp [valueCurve2Bound,valueCurve3Bound]
  constructor <;> positivity

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_MovementBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

lemma movementBudget_one_le (n : ℕ) (ε : ℚ) : 1 ≤ movementBudget n ε := le_max_left _ _

lemma movementBudget_pos (n : ℕ) (ε : ℚ) : 0 < movementBudget n ε :=
  lt_of_lt_of_le (by norm_num) (movementBudget_one_le n ε)

lemma threshold_pos (n : ℕ) (ε : ℚ) {lam : ℚ} (hlam : 0 < lam) : 0 < threshold n ε lam := by
  unfold threshold
  have hp := movementBudget_pos n ε
  positivity

lemma threshold_le_one (n : ℕ) (ε : ℚ) {lam : ℚ} (hlam : lam ≤ 1) : threshold n ε lam ≤ 1 := by
  unfold threshold
  have hp := movementBudget_pos n ε
  have h1 := movementBudget_one_le n ε
  apply (div_le_one (by positivity)).mpr
  nlinarith

lemma stepSize_spec {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    0 < stepSize a M σ ∧ stepSize a M σ ≤ σ/4 ∧ stepSize a M σ ≤ 1/4 ∧
      M*stepSize a M σ ≤ a/4 := by
  have hp : 0 < a/(4*M) := by positivity
  have hs : stepSize a M σ ≤ a/(4*M) := min_le_right _ _ |>.trans (min_le_left _ _)
  refine ⟨by unfold stepSize;positivity,min_le_left _ _,
    (min_le_right _ _).trans (min_le_right _ _),?_⟩
  have hh := (le_div_iff₀ (show (0:ℚ) < 4*M by positivity)).mp hs
  linarith

lemma stencilSize_spec {n : ℕ} (hn : 0 < n) {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    0 < stencilSize n a M σ ∧ stencilSize n a M σ ≤ σ/8 ∧
    stencilSize n a M σ ≤ 1 ∧ stencilSize n a M σ ≤ a/(64*M*n) := by
  have hnr : (0:ℚ) < n := by exact_mod_cast hn
  refine ⟨by unfold stencilSize;positivity,min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _)⟩

lemma meshSize_spec {n : ℕ} (hn : 0 < n) {a M s : ℚ} (ha : 0 < a) (hM : 0 < M) (hs : 0 < s) :
    0 < meshSize n a M s ∧ (n:ℚ)*meshSize n a M s/2 ≤ s*(a/(1024*M))/8 := by
  have hnr : (0:ℚ) < n := by exact_mod_cast hn
  refine ⟨by unfold meshSize;positivity,?_⟩
  unfold meshSize
  apply le_of_eq
  field_simp
  ring

lemma schedule_radius {n : ℕ} (hn : 0 < n) {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    stepSize a M σ+2*stencilSize n a M σ ≤ σ/2 := by
  have hs := (stepSize_spec ha hM hσ).2.1
  have hh := (stencilSize_spec hn ha hM hσ).2.1
  linarith

open CurrentKS.State

lemma coarseBudgetQ_cast (d n : ℕ) (ε σ : ℚ) :
    (coarseBudgetQ d n ε σ:ℝ)=coarseBudget d n (ε:ℝ) (σ:ℝ) := by
  simp only [coarseBudgetQ,coarseBudget,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_abs,Rat.cast_ofNat,Rat.cast_one]

lemma curveBudget_cast (d n : ℕ) (ε σ lam : ℚ) :
    (curveBudget d n ε σ lam:ℝ)=potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
  simp only [curveBudget,potentialCurveBound,valueCurve2Q,valueCurve3Q,
    valueCurve2Bound,valueCurve3Bound,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_abs,Rat.cast_inv,Rat.cast_one,Rat.cast_ofNat,coarseBudgetQ_cast]

lemma curveBudget_one_le (d n : ℕ) {ε σ : ℚ} (hε : 0 < ε) (hσ : 0 < σ) (lam : ℚ) :
    1 ≤ curveBudget d n ε σ lam := by
  have hεr : (0:ℝ) < ε := by exact_mod_cast hε
  have hσr : (0:ℝ) < σ := by exact_mod_cast hσ
  have hh := valueCurve_bounds_nonneg (d:=d) (N:=n) hεr hσr
  have hl : (0:ℝ) ≤ |(lam:ℝ)| *(n:ℝ)*(1+800/(σ:ℝ)^3) := by positivity
  have hc : (1:ℝ) ≤ potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
    unfold potentialCurveBound
    linarith
  rw [←curveBudget_cast] at hc
  exact_mod_cast hc

end CurrentKS.Schedule

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ObjectiveCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma nearRadius_pos {δ L R r : ℚ} (hδ : 0 < δ) (hL : 0 < L)
    (hR : 0 ≤ R) (hr : 0 < r) : 0 < nearRadius δ L R r := by
  unfold nearRadius
  positivity

end
end CurrentKS.RationalSDP

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueOuterRadius
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d n : ℕ}

lemma valueOuterRadius_nonneg {ε : ℚ} (hε : 0 < ε) : 0 ≤ valueOuterRadius d ε := by
  unfold valueOuterRadius
  positivity
lemma valueInnerRadius_pos : 0 < valueInnerRadius d := by unfold valueInnerRadius; positivity
lemma valueInnerRadius_le : valueInnerRadius d ≤ 1 := by
  unfold valueInnerRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg (d:ℚ)]

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueObjectiveCoeffs
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma valueLipschitz_pos {ε : ℚ} (hε : 0 ≤ ε) : 0 < valueLipschitz d ε := by
  unfold valueLipschitz
  positivity

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters2
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

lemma stencil_error_bounds {n : ℕ} (hn : 0 < n) {a h : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1) :
    0 < a*h^2/(128*n) ∧ a*h^2/(128*n) ≤ 1 := by
  have hn0 : (0:ℚ) < n := by exact_mod_cast hn
  have hn1 : (1:ℚ) ≤ n := by exact_mod_cast hn
  refine ⟨by positivity,(div_le_one (by positivity)).mpr ?_⟩
  have hh2 : h^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ha1 (sq_nonneg h)
  nlinarith

lemma selection_error_bounds {a s : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1/4) :
    0 < a*s^2/4 ∧ a*s^2/4 ≤ 1 := by
  refine ⟨by positivity,(div_le_one (by norm_num : (0:ℚ) < 4)).mpr ?_⟩
  have hs2 : s^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ha1 (sq_nonneg s)
  nlinarith

lemma parameters_valid {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    (parameters d n ν lam).Valid n := by
  have hd0 : (0:ℚ) < d := by exact_mod_cast hd
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hep : 0 < ν/(d:ℚ) := div_pos hν hd0
  have hep1 : ν/(d:ℚ) ≤ 1 := (div_le_one hd0).mpr (hν1.trans hd1)
  have hσ : 0 < lam^2/ν := by positivity
  have ha := threshold_pos n (ν/(d:ℚ)) hlam
  have ha1 := threshold_le_one n (ν/(d:ℚ)) hlam1
  have hM := curveBudget_one_le d n hep hσ lam
  have hMp : 0 < curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam := lt_of_lt_of_le (by norm_num) hM
  have hs := stepSize_spec ha hMp hσ
  have hh := stencilSize_spec hn ha hMp hσ
  have hρ := meshSize_spec hn ha hMp hs.1
  have he := stencil_error_bounds hn ha ha1 hh.1 hh.2.2.1
  have hg := selection_error_bounds ha ha1 hs.1 hs.2.2.1
  exact ⟨hep,hep1,hσ,ha,ha1,hM,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,
    hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,hρ.1,hρ.2,schedule_radius hn ha hMp hσ,
    he.1,he.2,hg.1,hg.2⟩

end CurrentKS.Schedule

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

lemma penaltyParameter_strip {N : ℕ} (hN : 0 < N) {ν : ℚ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) :
    1/(40000*(N:ℚ)^2) ≤ (penaltyParameter N ν)^2/ν ∧
      (penaltyParameter N ν)^2/ν ≤ 1/(10000*(N:ℚ)^2) := by
  have hh := penaltyParameter_interval hN hν hν1
  have hp := penaltyParameter_pos_le hN hν hν1
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hνr : (0:ℝ) < ν := by exact_mod_cast hν
  have hp' : (0:ℝ) ≤ penaltyParameter N ν := by exact_mod_cast hp.1.le
  have hlo := sq_le_sq₀ (by positivity : (0:ℝ) ≤ Real.sqrt (ν:ℝ)/(200*N)) hp' |>.mpr hh.1
  have hhi := sq_le_sq₀ hp' (by positivity : (0:ℝ) ≤ Real.sqrt (ν:ℝ)/(100*N)) |>.mpr hh.2
  rw [div_pow,Real.sq_sqrt hνr.le] at hlo hhi
  have hlo' : 1/(40000*(N:ℝ)^2) ≤ (penaltyParameter N ν:ℝ)^2/(ν:ℝ) := by
    apply (le_div_iff₀ hνr).mpr
    convert hlo using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hhi' : (penaltyParameter N ν:ℝ)^2/(ν:ℝ) ≤ 1/(10000*(N:ℝ)^2) := by
    apply (div_le_iff₀ hνr).mpr
    convert hhi using 1
    all_goals try with_reducible_and_instances rfl
    ring
  constructor
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,
      Rat.cast_pow,Rat.cast_natCast] using hlo'
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,
      Rat.cast_pow,Rat.cast_natCast] using hhi'

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_GlobalCounts
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W23.NaturalPolynomial.eval_comp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Schedule

section
open KS.W23
open scoped BigOperators

lemma coarseBudget_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    coarseBudgetQ d n ε σ ≤ (coarseP.eval B:ℚ) := by
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  unfold coarseBudgetQ coarseP X
  simp only [NaturalPolynomial.eval_power,NaturalPolynomial.eval,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,abs_of_pos hε,
    div_eq_mul_inv,←inv_pow]
  gcongr

lemma jacobian_polynomial {d B : ℕ} (hd : d≤B) {ε : ℚ} (hε : 0<ε)
    (hei : ε⁻¹≤(B:ℚ)^4) :
    10^18*((d:ℚ)+1)*(1+ε⁻¹)^4 ≤ (jacobianP.eval B:ℚ) := by
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  unfold jacobianP X
  simp only [NaturalPolynomial.eval_power,NaturalPolynomial.eval,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  gcongr

lemma derivative_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    300*coarseBudgetQ d n ε σ^5 ≤ (derivativeP.eval B:ℚ) := by
  have hc := coarseBudget_polynomial hd hn hε hε1 hσ hei hsi
  have hc0 : 0 ≤ coarseBudgetQ d n ε σ := by unfold coarseBudgetQ;positivity
  change 300*coarseBudgetQ d n ε σ^5 ≤ ((300*(coarseP.eval B)^5:ℕ):ℚ)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  gcongr

lemma secondP_eval (B:ℕ) : (secondP.eval B:ℚ)=
    (1+2*((B:ℚ)+1))*((jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ)*
       (1+(jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ))^2) := by
  change (((1+2*(B+1))*(jacobianP.eval B*derivativeP.eval B*
       (1+jacobianP.eval B*derivativeP.eval B)^2):ℕ):ℚ)=_
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]

lemma thirdP_eval (B:ℕ) : (thirdP.eval B:ℚ)=
    (1+2*((B:ℚ)+1))*((jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ)*
       ((1+(jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ))^3+
         3*(1+(jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ))*
         ((jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ)*
          (1+(jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ))^2))) := by
  change (((1+2*(B+1))*(jacobianP.eval B*derivativeP.eval B*
       ((1+jacobianP.eval B*derivativeP.eval B)^3+
         3*(1+jacobianP.eval B*derivativeP.eval B)*
         (jacobianP.eval B*derivativeP.eval B*
          (1+jacobianP.eval B*derivativeP.eval B)^2))):ℕ):ℚ)=_
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]

lemma outer_polynomial {d B:ℕ} (hd:d≤B) {ε:ℚ} (hε:0<ε) (hε1:ε≤1):
    1+|ε| *(2*((d:ℚ)+1)) ≤ 1+2*((B:ℚ)+1) := by
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  rw [abs_of_pos hε]
  have hh := mul_le_mul_of_nonneg_right hε1 (show (0:ℚ)≤2*((d:ℚ)+1) by positivity)
  nlinarith

private lemma curve2_mono {o O j J q Q : ℚ}
    (ho: o≤O) (hj:j≤J) (hq:q≤Q) (ho0:0≤o) (hj0:0≤j) (hq0:0≤q) :
    o*(j*q*(1+j*q)^2) ≤ O*(J*Q*(1+J*Q)^2) := by
  have hO : 0≤O := ho0.trans ho
  have hJ : 0≤J := hj0.trans hj
  have hQ : 0≤Q := hq0.trans hq
  gcongr

private lemma curve3_mono {o O j J q Q : ℚ}
    (ho: o≤O) (hj:j≤J) (hq:q≤Q) (ho0:0≤o) (hj0:0≤j) (hq0:0≤q) :
    o*(j*q*((1+j*q)^3+3*(1+j*q)*(j*q*(1+j*q)^2))) ≤
    O*(J*Q*((1+J*Q)^3+3*(1+J*Q)*(J*Q*(1+J*Q)^2))) := by
  have hO : 0≤O := ho0.trans ho
  have hJ : 0≤J := hj0.trans hj
  have hQ : 0≤Q := hq0.trans hq
  gcongr

lemma valueCurve2_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    valueCurve2Q d n ε σ ≤ (secondP.eval B:ℚ) := by
  have hj := jacobian_polynomial hd hε hei
  have hD := derivative_polynomial hd hn hε hε1 hσ hei hsi
  have hc0 : 0 ≤ coarseBudgetQ d n ε σ := by unfold coarseBudgetQ;positivity
  have houter := outer_polynomial hd hε hε1
  rw [secondP_eval]
  unfold valueCurve2Q
  dsimp only
  exact curve2_mono houter hj hD (by positivity) (by positivity) (by positivity)

lemma valueCurve3_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    valueCurve3Q d n ε σ ≤ (thirdP.eval B:ℚ) := by
  have hj := jacobian_polynomial hd hε hei
  have hD := derivative_polynomial hd hn hε hε1 hσ hei hsi
  have hc0 : 0 ≤ coarseBudgetQ d n ε σ := by unfold coarseBudgetQ;positivity
  have houter := outer_polynomial hd hε hε1
  rw [thirdP_eval]
  unfold valueCurve3Q
  dsimp only
  exact curve3_mono houter hj hD (by positivity) (by positivity) (by positivity)

lemma curvatureP_eval (B : ℕ) : (curvatureP.eval B:ℚ) =
    1+(secondP.eval B:ℚ)+(thirdP.eval B:ℚ)+(B:ℚ)*(1+800*(40000*(B:ℚ)^2)^3) := by
  change (((1+secondP.eval B+thirdP.eval B+B*(1+800*(40000*B^2)^3)):ℕ):ℚ)=_
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]

lemma curveBudget_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ lam : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hlam : 0<lam) (hlam1 : lam≤1)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    curveBudget d n ε σ lam ≤ (curvatureP.eval B:ℚ) := by
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  have hpen : |lam| *(n:ℚ)*(1+800/σ^3) ≤ (B:ℚ)*(1+800*(40000*(B:ℚ)^2)^3) := by
    rw [abs_of_pos hlam]
    simp only [div_eq_mul_inv,←inv_pow]
    calc
      _ ≤ 1*(B:ℚ)*(1+800*(40000*(B:ℚ)^2)^3) := by gcongr
      _ = _ := by rw [one_mul]
  have h2 := valueCurve2_polynomial hd hn hε hε1 hσ hei hsi
  have h3 := valueCurve3_polynomial hd hn hε hε1 hσ hei hsi
  rw [curvatureP_eval]
  unfold curveBudget
  exact add_le_add (add_le_add (add_le_add le_rfl h2) h3) hpen

lemma movementBudget_polynomial {n B : ℕ} (hn : n≤B)
    {ε : ℚ} (hε : 0<ε) (hei : ε⁻¹≤(B:ℚ)^4) :
    movementBudget n ε ≤ (movementP.eval B:ℚ) := by
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  have hj : 1+(3*(n:ℚ))^2/(ε/40000) ≤ 1+(3*(B:ℚ))^2*(40000*(B:ℚ)^4) := by
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    gcongr
  have he : 2*(1+(3*(n:ℚ))^2/(ε/40000))^2*(1+3*(n:ℚ))^2 ≤
      2*(1+(3*(B:ℚ))^2*(40000*(B:ℚ)^4))^2*(1+3*(B:ℚ))^2 := by gcongr
  unfold movementBudget
  dsimp only
  have he0 : 0 ≤ 2*(1+(3*(n:ℚ))^2/(ε/40000))^2*(1+3*(n:ℚ))^2 := by positivity
  have hq : 4*(1+9*(n:ℚ)^2) ≤ 4*(1+9*(B:ℚ)^2) := by gcongr
  unfold movementP X
  simp only [NaturalPolynomial.eval_power,NaturalPolynomial.eval,
    Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  apply max_le
  · have hp : (0:ℚ) ≤ 48*(2*(1+(3*(B:ℚ))^2*(40000*(B:ℚ)^4))^2*(1+3*(B:ℚ))^2) := by positivity
    have hq0 : (0:ℚ) ≤ 4*(1+9*(B:ℚ)^2) := by positivity
    linarith
  · apply max_le
    · have hdiv := div_le_self (mul_nonneg (by norm_num : (0:ℚ)≤48) he0) (by norm_num : (1:ℚ)≤23)
      have hm := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℚ)≤48)
      have hq0 : (0:ℚ) ≤ 4*(1+9*(B:ℚ)^2) := by positivity
      linarith
    · have he' : (0:ℚ)≤48*(2*(1+(3*(B:ℚ))^2*(40000*(B:ℚ)^4))^2*(1+3*(B:ℚ))^2) := by positivity
      linarith

end

open KS.W23

lemma thresholdInvP_eval (B : ℕ) : (thresholdInvP.eval B:ℚ)=
    512*(movementP.eval B:ℚ)^2*(200*(B:ℚ)^4) := by
  change ((512*(movementP.eval B)^2*(200*B^4):ℕ):ℚ)=_
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]

lemma threshold_inv_polynomial {n B:ℕ} (hn:n≤B) {ε lam:ℚ}
    (hε:0<ε) (hlam:0<lam) (hei:ε⁻¹≤(B:ℚ)^4) (hli:lam⁻¹≤200*(B:ℚ)^4) :
    (threshold n ε lam)⁻¹ ≤ (thresholdInvP.eval B:ℚ) := by
  have hb := movementBudget_polynomial hn hε hei
  have hp := (movementBudget_pos n ε).le
  rw [threshold,inv_div,div_eq_mul_inv,thresholdInvP_eval]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hb 2) (by norm_num)
  · exact hli
  · exact (inv_pos.mpr hlam).le
  · positivity

lemma inv_min_le_sum {a b:ℚ} (ha:0<a) (hb:0<b) :
    (min a b)⁻¹ ≤ a⁻¹+b⁻¹ := by
  rcases le_total a b with h|h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hb.le)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (inv_nonneg.mpr ha.le)

lemma stepSize_inv_bound {a M σ:ℚ} (ha:0<a) (hM:0<M) (hσ:0<σ) :
    (stepSize a M σ)⁻¹ ≤ 4*σ⁻¹+4*M*a⁻¹+4 := by
  have h1 := inv_min_le_sum (div_pos hσ (by norm_num : (0:ℚ)<4))
    (lt_min (div_pos ha (mul_pos (by norm_num : (0:ℚ)<4) hM)) (by norm_num : (0:ℚ)<1/4))
  have h2 := inv_min_le_sum (div_pos ha (mul_pos (by norm_num : (0:ℚ)<4) hM)) (by norm_num : (0:ℚ)<1/4)
  have hh := h1.trans (add_le_add le_rfl h2)
  unfold stepSize
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

lemma stepInvP_eval (B:ℕ) : (stepInvP.eval B:ℚ)=
    4*(40000*(B:ℚ)^2)+4*(curvatureP.eval B:ℚ)*(thresholdInvP.eval B:ℚ)+4 := by
  change ((4*(40000*B^2)+4*curvatureP.eval B*thresholdInvP.eval B+4:ℕ):ℚ)=_
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]

lemma step_inv_polynomial {d n B:ℕ} (hd:d≤B) (hn:n≤B)
    {ε σ lam:ℚ} (hε:0<ε) (hε1:ε≤1) (hσ:0<σ) (hlam:0<lam) (hlam1:lam≤1)
    (hei:ε⁻¹≤(B:ℚ)^4) (hsi:σ⁻¹≤40000*(B:ℚ)^2) (hli:lam⁻¹≤200*(B:ℚ)^4) :
    (stepSize (threshold n ε lam) (curveBudget d n ε σ lam) σ)⁻¹ ≤ (stepInvP.eval B:ℚ) := by
  have ha := threshold_pos n ε hlam
  have hM := (show (0:ℚ)<1 by norm_num).trans_le (curveBudget_one_le d n hε hσ lam)
  have hh := stepSize_inv_bound ha hM hσ
  have hm := curveBudget_polynomial hd hn hε hε1 hσ hlam hlam1 hei hsi
  have ht := threshold_inv_polynomial hn hε hlam hei hli
  rw [stepInvP_eval]
  apply hh.trans
  apply add_le_add _ le_rfl
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hsi (by norm_num)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) ht
      (inv_nonneg.mpr ha.le) (by positivity)

end CurrentKS.Schedule

namespace CurrentKS.Schedule
noncomputable section
open CurrentKS.RationalSDP CurrentKS.Hermitian CurrentKS.State
open scoped BigOperators

variable {d N : ℕ}

theorem normalized_parameter_bounds [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
    let ν := varianceQuery coords
    let lam := penaltyParameter N ν
    ν⁻¹ ≤ (N:ℚ)*d^2 ∧ (ν/(d:ℚ))⁻¹ ≤ (N:ℚ)*d^3 ∧
      lam⁻¹ ≤ 200*(N:ℚ)^2*d^2 ∧ (lam^2/ν)⁻¹ ≤ 40000*(N:ℚ)^2 := by
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hN : (0:ℚ) < N := by exact_mod_cast NeZero.pos N
  have hlo := variance_lower_paper (rationalAtoms coords) hA hrank htr
  have hlo' : 1/((N:ℚ)*d^2) ≤ ν := by
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow]
      using hlo.trans hν.2.2.1
  have hvi : ν⁻¹ ≤ (N:ℚ)*d^2 := by
    apply (inv_le_comm₀ hν.1 (by positivity)).mpr
    simpa only [inv_eq_one_div] using hlo'
  have hei : (ν/(d:ℚ))⁻¹ ≤ (N:ℚ)*d^3 := by
    rw [inv_div]
    calc
      (d:ℚ)/ν = (d:ℚ)*ν⁻¹ := div_eq_mul_inv _ _
      _ ≤ (d:ℚ)*((N:ℚ)*d^2) := mul_le_mul_of_nonneg_left hvi hd.le
      _ = (N:ℚ)*d^3 := by ring
  have hp := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have hi := penaltyParameter_interval (NeZero.pos N) hν.1 hν.2.1
  have hνsqrt : (ν:ℝ) ≤ Real.sqrt (ν:ℝ) :=
    Real.le_sqrt_of_sq_le (by
      have ha : (0:ℝ) ≤ ν := by exact_mod_cast hν.1.le
      have hb : (ν:ℝ) ≤ 1 := by exact_mod_cast hν.2.1
      nlinarith)
  have hlamlo : ν/(200*(N:ℚ)) ≤ lam := by
    apply (Rat.cast_le (K:=ℝ)).mp
    have hN' : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast] using
      (div_le_div_of_nonneg_right hνsqrt (by positivity : (0:ℝ)≤200*N)).trans hi.1
  have hli : lam⁻¹ ≤ 200*(N:ℚ)^2*d^2 := by
    calc
      lam⁻¹ ≤ (ν/(200*(N:ℚ)))⁻¹ := inv_anti₀ (div_pos hν.1 (mul_pos (by norm_num) hN)) hlamlo
      _ = 200*(N:ℚ)*ν⁻¹ := by rw [inv_div,div_eq_mul_inv]
      _ ≤ 200*(N:ℚ)*((N:ℚ)*d^2) := mul_le_mul_of_nonneg_left hvi (by positivity)
      _ = 200*(N:ℚ)^2*d^2 := by ring
  have hstrip := (penaltyParameter_strip (NeZero.pos N) hν.1 hν.2.1).1
  have hsi : (lam^2/ν)⁻¹ ≤ 40000*(N:ℚ)^2 := by
    calc
      (lam^2/ν)⁻¹ ≤ (1/(40000*(N:ℚ)^2))⁻¹ := inv_anti₀ (by positivity) hstrip
      _ = 40000*(N:ℚ)^2 := by rw [one_div,inv_inv]
  exact ⟨hvi,hei,hli,hsi⟩

end
end CurrentKS.Schedule

namespace CurrentKS.RationalSDP
variable {n d : ℕ}

lemma searchFuel_le {r R : ℚ} (hr : 0 < r) (hR : 0≤R) {R₀ r₀ : ℕ}
    (hRb : R≤R₀) (hrb : r⁻¹ ≤ r₀) :
    searchFuel n r R ≤ 4*R₀^2*(r₀*(n+1))^2+1 := by
  unfold searchFuel
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  have hi : (searchStep n r)⁻¹ = r⁻¹*((n:ℚ)+1) := by
    simp only [searchStep,div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  rw [div_eq_mul_inv,←inv_pow,hi]
  push_cast
  gcongr

lemma optimizeFuel_le {δ : ℚ} {D : ℕ} (hδ : δ⁻¹≤D) :
    optimizeFuel δ 100 ≤ 200*D+3 := by
  unfold optimizeFuel
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  rw [div_eq_mul_inv]
  push_cast
  nlinarith

lemma valueDimension_le {B : ℕ} (hd : d≤B) : valueDimension d ≤ queryDimensionBound B := by
  unfold valueDimension queryDimensionBound
  have hh := Nat.mul_le_mul hd hd
  nlinarith

lemma valueOuterRadius_le_bound {B : ℕ} (hd : d≤B) {ε : ℚ} (he : 0<ε) (hei : ε⁻¹≤B) :
    valueOuterRadius d ε ≤ queryOuterBound B := by
  have hn : (valueDimension d:ℚ)≤queryDimensionBound B := by exact_mod_cast valueDimension_le hd
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  unfold valueOuterRadius queryOuterBound
  push_cast
  simp only [div_eq_mul_inv]
  gcongr

lemma valueLipschitz_le_bound {B : ℕ} (hd : d≤B) {ε : ℚ} (he : 0≤ε) (he1 : ε≤1) :
    valueLipschitz d ε ≤ queryLipschitzBound B := by
  have hn : (valueDimension d:ℚ)≤queryDimensionBound B := by exact_mod_cast valueDimension_le hd
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  unfold valueLipschitz queryLipschitzBound
  push_cast
  calc
    ((valueDimension d:ℚ)+1)*(1+2*ε*d) ≤
        ((queryDimensionBound B:ℚ)+1)*(1+2*1*B) := by gcongr
    _ = _ := by ring

lemma valueInnerRadius_inv_le_bound {B : ℕ} (hd : d≤B) :
    (valueInnerRadius d)⁻¹ ≤ queryInnerInvBound B := by
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  unfold valueInnerRadius queryInnerInvBound
  simp only [one_div,inv_inv,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
  gcongr

lemma valueNearRadius_inv_le_bound {B : ℕ} (hd : d≤B) {ε δ : ℚ}
    (he : 0<ε) (he1 : ε≤1) (hei : ε⁻¹≤B) (hδ : 0<δ) (hδi : δ⁻¹≤B) :
    (nearRadius δ (valueLipschitz d ε) (valueOuterRadius d ε) (valueInnerRadius d))⁻¹ ≤
      queryNearInvBound B := by
  have hL := valueLipschitz_le_bound hd he.le he1
  have hR := valueOuterRadius_le_bound hd he hei
  have hr := valueInnerRadius_inv_le_bound hd
  have hr1 := valueInnerRadius_le (d:=d)
  have hL0 := (valueLipschitz_pos (d:=d) he.le).le
  have hR0 := valueOuterRadius_nonneg (d:=d) he
  have hr0 := (valueInnerRadius_pos (d:=d)).le
  unfold nearRadius queryNearInvBound
  rw [mul_inv_rev,inv_div]
  simp only [div_eq_mul_inv]
  push_cast
  calc
    (valueInnerRadius d)⁻¹*(valueLipschitz d ε*(2*valueOuterRadius d ε+valueInnerRadius d)*δ⁻¹) ≤
      (queryInnerInvBound B:ℚ)*(queryLipschitzBound B*(2*queryOuterBound B+1)*B) := by gcongr
    _ = _ := by ring

theorem valueSearchFuel_le {B : ℕ} (hd : d≤B) {ε δ : ℚ}
    (he : 0<ε) (he1 : ε≤1) (hei : ε⁻¹≤B) (hδ : 0<δ) (hδi : δ⁻¹≤B) :
    searchFuel (valueDimension d)
      (nearRadius δ (valueLipschitz d ε) (valueOuterRadius d ε) (valueInnerRadius d))
      (valueOuterRadius d ε) ≤ querySearchBound B := by
  have hr := nearRadius_pos hδ (valueLipschitz_pos (d:=d) he.le)
    (valueOuterRadius_nonneg (d:=d) he) (valueInnerRadius_pos (d:=d))
  have h := searchFuel_le (n:=valueDimension d) hr (valueOuterRadius_nonneg (d:=d) he)
    (valueOuterRadius_le_bound hd he hei) (valueNearRadius_inv_le_bound hd he he1 hei hδ hδi)
  apply h.trans
  unfold querySearchBound
  gcongr
  exact valueDimension_le hd

theorem valueScanIterations_le {B : ℕ} (hd : d≤B) {ε δ : ℚ}
    (he : 0<ε) (he1 : ε≤1) (hei : ε⁻¹≤B) (hδ : 0<δ) (hδi : δ⁻¹≤B) :
    (optimizeFuel δ 100+1)*searchFuel (valueDimension d)
      (nearRadius δ (valueLipschitz d ε) (valueOuterRadius d ε) (valueInnerRadius d))
      (valueOuterRadius d ε) ≤ queryScanBound B := by
  have hf := optimizeFuel_le hδi
  have hs := valueSearchFuel_le hd he he1 hei hδ hδi
  apply (Nat.mul_le_mul (Nat.add_le_add_right hf 1) hs).trans
  unfold queryScanBound
  simp only [show 200*B+3+1=200*B+4 by omega, le_refl]
end CurrentKS.RationalSDP

namespace CurrentKS.Schedule
open KS.W23

lemma stencilSize_inv_bound {n : ℕ} (hn : 0<n) {a M σ : ℚ}
    (ha : 0<a) (hM : 0<M) (hσ : 0<σ) :
    (stencilSize n a M σ)⁻¹ ≤ 8*σ⁻¹+1+64*M*n*a⁻¹ := by
  have hn' : (0:ℚ)<n := by exact_mod_cast hn
  have h1 := inv_min_le_sum (div_pos hσ (by norm_num : (0:ℚ)<8))
    (lt_min (by norm_num : (0:ℚ)<1) (by positivity : (0:ℚ)<a/(64*M*n)))
  have h2 := inv_min_le_sum (by norm_num : (0:ℚ)<1) (by positivity : (0:ℚ)<a/(64*M*n))
  have h := h1.trans (add_le_add le_rfl h2)
  unfold stencilSize
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,inv_one]
  ring

lemma stencilInvP_eval (B : ℕ) : (stencilInvP.eval B:ℚ) =
    8*(40000*(B:ℚ)^2)+1+64*(curvatureP.eval B:ℚ)*B*(thresholdInvP.eval B:ℚ) := by
  change ((8*(40000*B^2)+1+64*curvatureP.eval B*B*thresholdInvP.eval B:ℕ):ℚ)=_
  push_cast
  rfl

lemma stencil_inv_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B) (hn0 : 0<n)
    {ε σ lam : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ) (hlam : 0<lam) (hlam1 : lam≤1)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) (hli : lam⁻¹≤200*(B:ℚ)^4) :
    (stencilSize n (threshold n ε lam) (curveBudget d n ε σ lam) σ)⁻¹ ≤
      (stencilInvP.eval B:ℚ) := by
  have ha := threshold_pos n ε hlam
  have hM := (show (0:ℚ)<1 by norm_num).trans_le (curveBudget_one_le d n hε hσ lam)
  have hs := stencilSize_inv_bound hn0 ha hM hσ
  have ht := threshold_inv_polynomial hn hε hlam hei hli
  have hm := curveBudget_polynomial hd hn hε hε1 hσ hlam hlam1 hei hsi
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  rw [stencilInvP_eval]
  apply hs.trans
  gcongr

lemma queryPrecisionP_eval (B : ℕ) : (queryPrecisionP.eval B:ℚ) =
    1+B+(B:ℚ)^4+512*B*(thresholdInvP.eval B:ℚ)*(stencilInvP.eval B:ℚ)^2+
      16*(thresholdInvP.eval B:ℚ)*(stepInvP.eval B:ℚ)^2 := by
  change ((1+B+B^4+512*B*thresholdInvP.eval B*(stencilInvP.eval B)^2+
    16*thresholdInvP.eval B*(stepInvP.eval B)^2:ℕ):ℚ)=_
  push_cast
  rfl

lemma queryPrecisionP_ge (B : ℕ) :
    B≤queryPrecisionP.eval B ∧ (B:ℚ)^4≤(queryPrecisionP.eval B:ℚ) := by
  constructor
  · change B≤1+B+B^4+512*B*thresholdInvP.eval B*(stencilInvP.eval B)^2+
      16*thresholdInvP.eval B*(stepInvP.eval B)^2
    omega
  · rw [queryPrecisionP_eval]
    have h1 : (0:ℚ)≤512*B*(thresholdInvP.eval B:ℚ)*(stencilInvP.eval B:ℚ)^2 := by positivity
    have h2 : (0:ℚ)≤16*(thresholdInvP.eval B:ℚ)*(stepInvP.eval B:ℚ)^2 := by positivity
    linarith [Nat.cast_nonneg (α:=ℚ) B]

lemma query_errors_inv_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B) (hn0 : 0<n)
    {ν lam : ℚ} (hε : 0<ν/(d:ℚ)) (hε1 : ν/(d:ℚ)≤1) (hσ : 0<lam^2/ν)
    (hlam : 0<lam) (hlam1 : lam≤1)
    (hei : (ν/(d:ℚ))⁻¹≤(B:ℚ)^4) (hsi : (lam^2/ν)⁻¹≤40000*(B:ℚ)^2)
    (hli : lam⁻¹≤200*(B:ℚ)^4) :
    ((parameters d n ν lam).stencilError/4)⁻¹≤(queryPrecisionP.eval B:ℚ) ∧
      ((parameters d n ν lam).selectionError/4)⁻¹≤(queryPrecisionP.eval B:ℚ) := by
  have ha := threshold_pos n (ν/(d:ℚ)) hlam
  have hM := (show (0:ℚ)<1 by norm_num).trans_le
    (curveBudget_one_le d n hε hσ lam)
  have hhp := (stencilSize_spec hn0 ha hM hσ).1
  have hsp := (stepSize_spec ha hM hσ).1
  have ht := threshold_inv_polynomial hn hε hlam hei hli
  have hh := stencil_inv_polynomial hd hn hn0 hε hε1 hσ hlam hlam1 hei hsi hli
  have hs := step_inv_polynomial hd hn hε hε1 hσ hlam hlam1 hei hsi hli
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  have h0 : (0:ℚ)≤1+B+(B:ℚ)^4 := by positivity
  have h1 : (0:ℚ)≤512*B*(thresholdInvP.eval B:ℚ)*(stencilInvP.eval B:ℚ)^2 := by positivity
  have h2 : (0:ℚ)≤16*(thresholdInvP.eval B:ℚ)*(stepInvP.eval B:ℚ)^2 := by positivity
  constructor
  · change ((threshold n (ν/(d:ℚ)) lam*(stencilSize n (threshold n (ν/(d:ℚ)) lam)
      (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))^2/(128*n))/4)⁻¹≤_
    rw [queryPrecisionP_eval]
    have heq : ((threshold n (ν/(d:ℚ)) lam*(stencilSize n (threshold n (ν/(d:ℚ)) lam)
      (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))^2/(128*n))/4)⁻¹=
        512*n*(threshold n (ν/(d:ℚ)) lam)⁻¹*
          ((stencilSize n (threshold n (ν/(d:ℚ)) lam)
          (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))⁻¹)^2 := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,←inv_pow]
      ring
    rw [heq]
    apply le_trans _ (le_add_of_nonneg_right h2)
    apply le_trans _ (le_add_of_nonneg_left h0)
    gcongr
  · change ((threshold n (ν/(d:ℚ)) lam*(stepSize (threshold n (ν/(d:ℚ)) lam)
      (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))^2/4)/4)⁻¹≤_
    rw [queryPrecisionP_eval]
    have heq : ((threshold n (ν/(d:ℚ)) lam*(stepSize (threshold n (ν/(d:ℚ)) lam)
      (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))^2/4)/4)⁻¹=
        16*(threshold n (ν/(d:ℚ)) lam)⁻¹*
          ((stepSize (threshold n (ν/(d:ℚ)) lam)
          (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))⁻¹)^2 := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,←inv_pow]
      ring
    rw [heq]
    apply le_trans _ (le_add_of_nonneg_left (add_nonneg h0 h1))
    gcongr
end CurrentKS.Schedule

namespace CurrentKS.RationalSDP
open KS.W23 CurrentKS.Schedule CurrentKS.Hermitian CurrentKS.State
open scoped BigOperators

variable {d N : ℕ}

theorem normalized_query_precisions [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank≤1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {n : ℕ} (hn0 : 0<n) (hn : n≤N) :
    let ν := varianceQuery coords
    let lam := penaltyParameter N ν
    let p := parameters d n ν lam
    ((ν/(d:ℚ))⁻¹≤(queryPrecisionP.eval (d+N):ℚ)) ∧
      (p.stencilError/4)⁻¹≤(queryPrecisionP.eval (d+N):ℚ) ∧
      (p.selectionError/4)⁻¹≤(queryPrecisionP.eval (d+N):ℚ) := by
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hl := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have b := normalized_parameter_bounds coords hA hrank htr
  have hd : (0:ℚ)<d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ)≤d := by exact_mod_cast NeZero.pos d
  have hdB : (d:ℚ)≤(d+N:ℕ) := by exact_mod_cast Nat.le_add_right d N
  have hNB : (N:ℚ)≤(d+N:ℕ) := by exact_mod_cast Nat.le_add_left N d
  have hε : 0<ν/(d:ℚ) := div_pos hν.1 hd
  have hε1 : ν/(d:ℚ)≤1 := (div_le_one hd).mpr (hν.2.1.trans hd1)
  have hσ : 0<lam^2/ν := div_pos (sq_pos_of_pos hl.1) hν.1
  have hei : (ν/(d:ℚ))⁻¹≤((d+N:ℕ):ℚ)^4 := by
    apply b.2.1.trans
    calc
      (N:ℚ)*d^3 ≤ ((d+N:ℕ):ℚ)*((d+N:ℕ):ℚ)^3 := by gcongr
      _ = ((d+N:ℕ):ℚ)^4 := by ring
  have hli : lam⁻¹≤200*((d+N:ℕ):ℚ)^4 := by
    apply b.2.2.1.trans
    calc
      200*(N:ℚ)^2*d^2 ≤ 200*((d+N:ℕ):ℚ)^2*((d+N:ℕ):ℚ)^2 := by gcongr
      _ = 200*((d+N:ℕ):ℚ)^4 := by ring
  have hsi : (lam^2/ν)⁻¹≤40000*((d+N:ℕ):ℚ)^2 := by
    apply b.2.2.2.trans
    gcongr
  exact ⟨hei.trans (queryPrecisionP_ge (d+N)).2,
    query_errors_inv_polynomial (Nat.le_add_right d N) (hn.trans (Nat.le_add_left N d)) hn0
      hε hε1 hσ hl.1 hl.2 hei hsi hli⟩

theorem normalized_query_search_iterations [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank≤1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {n : ℕ} (hn0 : 0<n) (hn : n≤N) :
    let ν := varianceQuery coords
    let lam := penaltyParameter N ν
    let p := parameters d n ν lam
    ∀ δ∈[p.stencilError/4,p.selectionError/4],
      (optimizeFuel δ 100+1)*searchFuel (valueDimension d)
        (nearRadius δ (valueLipschitz d (ν/d)) (valueOuterRadius d (ν/d)) (valueInnerRadius d))
        (valueOuterRadius d (ν/d)) ≤ (valueScanP queryPrecisionP).eval (d+N) := by
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hl := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have hp := parameters_valid (NeZero.pos d) hn0 hν.1 hν.2.1 hl.1 hl.2
  have hb := normalized_query_precisions coords hA hrank htr hn0 hn
  have hd : d≤queryPrecisionP.eval (d+N) :=
    (Nat.le_add_right d N).trans (queryPrecisionP_ge (d+N)).1
  dsimp only
  intro δ hδ
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hδ
  rcases hδ with rfl|rfl
  · exact valueScanIterations_le hd hp.epsilon_pos hp.epsilon_le hb.1
      (div_pos hp.stencilError_pos (by norm_num)) hb.2.1
  · exact valueScanIterations_le hd hp.epsilon_pos hp.epsilon_le hb.1
      (div_pos hp.selectionError_pos (by norm_num)) hb.2.2
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoutineLength
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
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
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLoops
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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

end CurrentKS.Realization

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
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma prefix_length (xs ys zs : List α) (h : xs=ys++zs) : ys.length≤xs.length := by
  rw [h,List.length_append];omega

instance poly_reverseBody (ea : α → Word) : PolyTime (reverseBody ea) := by
  unfold reverseBody;infer_instance

instance poly_mapCtxBody {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime (mapCtxBody ec ea eb r) := by
  dsimp only [mapCtxBody]
  apply poly_both
instance poly_natAdd : PolyTime natAdd := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  have h := le_prodCode_left (ea:=natCode) (eb:=natCode) p
  simp only [natCode,List.length_replicate] at h
  change 5*p.1+4≤5*(prodCode natCode natCode p).length+4
  omega

instance poly_rangeStep : PolyTime rangeStepRealizes := by dsimp only [rangeStepRealizes];apply poly_both

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

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialScalar
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

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
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialArrays
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

instance size_natMulStep : IterateSize ((first natCode natCode).both natAdd) := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s n
  change (prodCode natCode natCode ((fun a : ℕ×ℕ => (a.1,a.1+a.2))^[n] s)).length≤_
  rcases s with ⟨k,z⟩
  rw [fold_natAdd]
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*k+1+(n*k+z)≤10*(2*k+1+z+n+1)^2
  nlinarith
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCoordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*} {ea : α → Word}
instance poly_singletonList (ea : α → Word) : PolyTime (singletonList ea) := by unfold singletonList;apply poly_then
instance poly_vdD : PolyTime vdD := by unfold vdD;infer_instance
instance poly_vdRest : PolyTime vdRest := by unfold vdRest;infer_instance
instance poly_vdAtoms : PolyTime vdAtoms := by unfold vdAtoms;infer_instance
instance poly_vdParams : PolyTime vdParams := by unfold vdParams;infer_instance
instance poly_vdX : PolyTime vdX := by unfold vdX;infer_instance
instance poly_vdTheta : PolyTime vdTheta := by unfold vdTheta;infer_instance
instance poly_vdEps : PolyTime vdEps := by unfold vdEps;infer_instance

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStored
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

instance poly_singleton (ea : α → Word) : PolyTime (singleton ea) := by unfold singleton;apply poly_then
instance poly_familyFirst {n : α → ℕ} : PolyTime (familyFirst (ea:=ea) (n:=n)) := by unfold familyFirst;apply poly_reindex
instance poly_familyIndex {n : α → ℕ} : PolyTime (familyIndex (ea:=ea) (n:=n)) := by unfold familyIndex;apply poly_reindex

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCurvature
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_cuN : PolyTime cuN := by unfold cuN;apply poly_then
instance poly_cuRest : PolyTime cuRest := by unfold cuRest;apply poly_then
instance poly_cuH : PolyTime cuH := by unfold cuH;apply poly_then
instance poly_cuScalars : PolyTime cuScalars := by unfold cuScalars;apply poly_then
instance poly_cuA : PolyTime cuA := by unfold cuA;apply poly_then
instance poly_cuMore : PolyTime cuMore := by unfold cuMore;apply poly_then
instance poly_cuM : PolyTime cuM := by unfold cuM;apply poly_then
instance poly_cuLast : PolyTime cuLast := by unfold cuLast;apply poly_then
instance poly_cuS : PolyTime cuS := by unfold cuS;apply poly_then
instance poly_cuRho : PolyTime cuRho := by unfold cuRho;apply poly_then
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSchedule
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceBasics
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_fD : PolyTime fD := by unfold fD;apply poly_then
instance poly_fRest : PolyTime fRest := by unfold fRest;apply poly_then
instance poly_fAtoms : PolyTime fAtoms := by unfold fAtoms;apply poly_then
instance poly_fArgs : PolyTime fArgs := by unfold fArgs;apply poly_then
instance poly_fBase : PolyTime fBase := by unfold fBase;apply poly_then
instance poly_fScalars : PolyTime fScalars := by unfold fScalars;apply poly_then
instance poly_fNu : PolyTime fNu := by unfold fNu;apply poly_then
instance poly_fLam : PolyTime fLam := by unfold fLam;apply poly_then
instance poly_fpP : PolyTime fpP := by unfold fpP;apply poly_then
instance poly_fpY : PolyTime fpY := by unfold fpY;apply poly_then
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β γ : Type*} {L f g : ι → ℕ}

lemma IsPoly.mono (hf : IsPoly L f) (h : ∀i,g i≤f i) : IsPoly L g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => (h i).trans (hp i)⟩
lemma IsPoly.add (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i+g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun i => Nat.add_le_add (hp i) (hq i)⟩
lemma IsPoly.eval (hf : IsPoly L f) (p : NaturalPolynomial) : IsPoly L (fun i => p.eval (f i)) := by
  obtain ⟨q,hq⟩ := hf
  exact ⟨p.comp q,fun i => by simpa only [NaturalPolynomial.eval_comp] using p.eval_mono (hq i)⟩

variable {ea : α → Word} {eb : β → Word} {ec : γ → Word} {F : α → β} {G : β → γ}

lemma RunsPoly.of_poly (r : Realizes ea eb F) [PolyTime r] (a : ι → α)
    (h : IsPoly L (fun i => (ea (a i)).length)) : RunsPoly L r a := by
  refine ⟨h,?_⟩
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  exact (h.eval p).mono (fun i => hp (a i))
lemma RunsPoly.output {r : Realizes ea eb F} {a : ι → α} (h : RunsPoly L r a) :
    IsPoly L (fun i => (eb (F (a i))).length) := (h.input.add h.cost).mono (fun i => r.output_length (a i))
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoundedStep
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize
open scoped BigOperators

instance poly_statePencil : PolyTime statePencil := by unfold statePencil;apply poly_then
instance poly_stateParameters : PolyTime stateParameters := by unfold stateParameters;apply poly_then
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceFuel
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_packFace {α : Type*} {ea : α → Word} {f : α → FaceParams}
    {g : (a : α) → Fin (f a).N → ℚ}
    (p : Realizes ea faceCode f) (y : Realizes ea vectorCode (fun a => List.ofFn (g a)))
    [PolyTime p] [PolyTime y] : PolyTime (packFace p y) := by
  unfold packFace;apply poly_changeOutput
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialValueQuery
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
instance poly_veEps : PolyTime veEps := by unfold veEps;apply poly_then
instance poly_tinyMatrix : PolyTime tinyMatrix := by unfold tinyMatrix;apply poly_then
instance poly_vqData : PolyTime vqData := by unfold vqData;apply poly_then
instance poly_vqDelta : PolyTime vqDelta := by unfold vqDelta;apply poly_then
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialPotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
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
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialVariance
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_mgN : PolyTime mgN := by unfold mgN;apply poly_then
instance poly_mgRest : PolyTime mgRest := by unfold mgRest;apply poly_then
instance poly_mgM : PolyTime mgM := by unfold mgM;apply poly_then
instance poly_mgDen : PolyTime mgDen := by unfold mgDen;apply poly_then
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceOrbit
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView
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
lemma orbit_count_le (p : FaceParams) (k : ℕ) : (p.orbit k).n≤p.N := by
  rw [orbit_eq]
  exact RationalFace.activeIndices_length_le _
lemma orbit_query_bounds (p : FaceParams) (h : p.GoodAtoms) (k : ℕ) (hn : (p.orbit k).n≠0) :
    (p.orbit k).stencilCount≤(valueScanP Schedule.queryPrecisionP).eval (p.d+p.N) ∧
    (p.orbit k).scoreCount≤(valueScanP Schedule.queryPrecisionP).eval (p.d+p.N) := by
  let : NeZero p.d := ⟨h.d_ne⟩
  let : NeZero p.N := ⟨h.N_ne⟩
  have hb := normalized_query_search_iterations p.coords h.positive h.rank h.trace
    (Nat.pos_of_ne_zero hn) (orbit_count_le p k)
  have h1 := hb _ (List.mem_cons_self ..)
  have h2 := hb _ (by simp only [List.mem_cons,List.not_mem_nil,or_false];exact Or.inr rfl)
  rw [orbit_eq] at *
  exact ⟨h1,h2⟩

variable {ι : Type*} {L : ι → ℕ}
lemma isPoly_face_dimensions (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) :
    IsPoly L (fun i => (a i).d+(a i).N) := by
  have hd := (RunsPoly.of_poly fD a ha).output
  have hn := (RunsPoly.of_poly (fBase.then (lengthList ratCode)) a ha).output
  have h := hd.add hn
  simp only [natCode,List.length_replicate,List.length_ofFn] at h
  exact h
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStencil
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ}
instance poly_fiP : PolyTime fiP := by unfold fiP;apply poly_familyFirst
instance poly_fiI : PolyTime fiI := by unfold fiI;apply poly_familyIndex
instance poly_fdS : PolyTime fdS := by unfold fdS;apply poly_familyFirst
instance poly_fdP : PolyTime fdP := by unfold fdP;apply poly_then
instance poly_fdI : PolyTime fdI := by unfold fdI;apply poly_then
instance poly_fdJ : PolyTime fdJ := by unfold fdJ;apply poly_familyIndex
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceRun
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι : Type*} {L : ι → ℕ}
lemma isPoly_orbitStencil_oai (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    IsPoly (fun s : {s : ι×ℕ // ((a s.1).orbit s.2).n≠0} => L s.val.1)
      (fun s => ((a s.val.1).orbit s.val.2).stencilCount) := by
  obtain ⟨q,hq⟩ := (isPoly_face_dimensions a ha).eval (RationalSDP.valueScanP Schedule.queryPrecisionP)
  refine ⟨q,?_⟩
  intro s
  exact (orbit_query_bounds (a s.val.1) (hg s.val.1) s.val.2 s.property).1.trans (hq s.val.1)
end CurrentKS.Realization

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CurrentKS.Realization.isPoly_orbitStencil_oai.{u_1} := @OAI.CurrentKS.Realization.isPoly_orbitStencil_oai.{u_1}
