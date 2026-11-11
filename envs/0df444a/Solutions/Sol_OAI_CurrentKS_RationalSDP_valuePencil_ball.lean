-- Prove2me | solution 1 for OAI.CurrentKS.RationalSDP.valuePencil_ball
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:31.066074+00:00
-- url     : https://prove2.me/submissions/5345f5a9-5b31-4154-ace2-2cec727b7a57

import Mathlib
import Definitions.Def_OAIQ241TT006

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

open scoped Matrix.Norms.Frobenius

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

theorem inverse_antitone {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef) (hab : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨u, rfl⟩ := hA.isUnit
  obtain ⟨v, rfl⟩ := hB.isUnit
  simpa only [Matrix.coe_units_inv] using CStarAlgebra.inv_le_inv hA.posSemidef.nonneg hab

lemma scalar_posDef {a : ℝ} (ha : 0 < a) : ((a : ℂ) • (1 : Mat d)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast ha)

lemma scalar_inv (a : ℝ) : (((a : ℂ) • (1 : Mat d))⁻¹) = (a⁻¹ : ℂ) • (1 : Mat d) := by
  by_cases ha : a = 0
  · simp [ha]
  · let : Invertible (a : ℂ) := invertibleOfNonzero (by exact_mod_cast ha)
    rw [Matrix.inv_smul _ _ (by simp), invOf_eq_inv]
    simp

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_OperatorNorm
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
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

lemma operatorNorm_eq_matrix (A : H d) : operatorNorm A = ‖(A : Mat d)‖ := rfl

lemma scalarOne_eq_algebraMap (r : ℝ) : ((r • (one : H d) : H d) : Mat d) = algebraMap ℝ (Mat d) r := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

lemma le_operatorNorm_smul_one (A : H d) : A ≤ operatorNorm A • one := by
  let : CStarAlgebra (Mat d) := {}
  change (A : Mat d) ≤ ((operatorNorm A • one : H d) : Mat d)
  rw [scalarOne_eq_algebraMap,operatorNorm_eq_matrix]
  exact A.property.isSelfAdjoint.le_algebraMap_norm_self

end

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma operatorNorm_le_frobenius (A : H d) : operatorNorm A ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  have hm := Matrix.frobenius_norm_mul (A : Mat d) (Matrix.replicateCol (Fin 1) (WithLp.ofLp v))
  rw [← Matrix.replicateCol_mulVec] at hm
  have hn (w : Fin d → ℂ) : ‖Matrix.replicateCol (Fin 1) w‖ = ‖WithLp.toLp 2 w‖ := by
    simp [Matrix.frobenius_norm_def, Matrix.replicateCol_apply, PiLp.norm_eq_of_L2,
      Real.sqrt_eq_rpow]
  rw [hn,hn] at hm
  exact hm

lemma scalar_one_mono_frob {r s : ℝ} (h : r ≤ s) :
    r • (one : H d) ≤ s • one := by
  apply sub_nonneg.mp
  erw [← sub_smul]
  change (0 : Mat d) ≤ ((s-r : ℝ) • (1 : Mat d))
  exact (Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr h :
    (0 : ℂ) ≤ ((s-r : ℝ) : ℂ))).nonneg

lemma le_norm_smul_one (A : H d) : A ≤ ‖A‖ • one :=
  (le_operatorNorm_smul_one A).trans (scalar_one_mono_frob (operatorNorm_le_frobenius A))

lemma neg_norm_smul_one_le (A : H d) : -‖A‖ • one ≤ A := by
  have h := le_norm_smul_one (-A)
  rw [norm_neg] at h
  have hh := neg_le_neg h
  simp only [neg_neg] at hh
  convert hh using 1 <;> first | rfl | module

lemma ball_order_bounds (A B : H d) {r : ℝ} (h : ‖A-B‖ ≤ r) :
    B-r • one ≤ A ∧ A ≤ B+r • one := by
  have hi : A-B ≤ r • one :=
    (le_norm_smul_one (A-B)).trans (scalar_one_mono_frob h)
  have hl : -r • one ≤ A-B :=
    (scalar_one_mono_frob (neg_le_neg h)).trans (neg_norm_smul_one_le (A-B))
  constructor
  · have hle := add_le_add_right hl B
    convert hle using 1 <;> first | rfl | module
  · exact sub_le_iff_le_add.mp hi |>.trans_eq (add_comm _ _)

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Space
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.HermitianCoordinates
noncomputable section
open CurrentKS.Hermitian Matrix
open scoped BigOperators Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.HermitianCoordinates.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r791565_1 : NormedSpace ℝ (H d) := inferInstance
lemma assemble_extract (A : H d) : assemble (extract A)=A := by
  apply Subtype.ext
  ext i j
  have hh := Matrix.IsHermitian.apply A.property i j
  have hd := Matrix.IsHermitian.apply A.property i i
  rcases lt_trichotomy i j with hij | hij | hji
  · apply Complex.ext <;>
      simp [assemble,extract,encode,decode,hij,hij.le,not_le.mpr hij]
  · subst j
    apply Complex.ext
    · simp [assemble,extract,encode,decode]
    · have him := congrArg Complex.im hd
      simp only [Complex.star_def,Complex.conj_im] at him
      simp [assemble,extract,encode,decode]
      linarith
  · apply Complex.ext
    · have hre := congrArg Complex.re hh
      simp only [Complex.star_def,Complex.conj_re] at hre
      simpa [assemble,extract,encode,decode,hji,hji.le,not_le.mpr hji,
        min_eq_right hji.le,max_eq_left hji.le] using hre
    · have him := congrArg Complex.im hh
      simp only [Complex.star_def,Complex.conj_im] at him
      simpa [assemble,extract,encode,decode,hji,hji.le,not_lt.mpr hji.le,
        not_le.mpr hji] using him

lemma norm_decode_entry (x : Fin d × Fin d → ℝ) (i j : Fin d) :
    ‖decode x i j‖^2 ≤ x (i,j)^2+x (j,i)^2 := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply]
  rcases lt_trichotomy i j with hij | hij | hji
  · simp [decode,min_eq_left hij.le,max_eq_right hij.le,hij,pow_two]
  · subst j
    simp only [decode,min_self,max_self,lt_self_iff_false,ite_false, if_false]
    nlinarith [sq_nonneg (x (i,i))]
  · simp [decode,min_eq_right hji.le,max_eq_left hji.le,hji,not_lt.mpr hji.le,pow_two]
    ring_nf
    rfl

local instance instNormedAddCommGroupSpace_r791565_1 : NormedAddCommGroup (Space d) := inferInstance
local instance instNormedSpaceRealSpace_r791565_1 : NormedSpace ℝ (Space d) := inferInstance
lemma norm_assemble_sq (x : Space d) : ‖assemble x‖^2 ≤ 2*‖x‖^2 := by
  have hm : ‖assemble x‖^2 = ∑ i : Fin d, ∑ j : Fin d, ‖decode x i j‖^2 := by
    change ‖asL2 (decode x)‖^2 = _
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [asL2,PiLp.toLp_apply,PiLp.norm_sq_eq_of_L2]
  rw [hm,PiLp.norm_sq_eq_of_L2]
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => norm_decode_entry x i j))
  have he : (∑ i : Fin d, ∑ j : Fin d, x (j,i)^2) = ∑ i : Fin d, ∑ j : Fin d, x (i,j)^2 :=
    Finset.sum_comm
  simpa only [Finset.sum_add_distrib,Fintype.sum_prod_type,Real.norm_eq_abs,sq_abs,
    two_mul,he] using hb

lemma norm_assemble (x : Space d) : ‖assemble x‖ ≤ 2*‖x‖ := by
  have h := norm_assemble_sq x
  nlinarith [norm_nonneg x,norm_nonneg (assemble x)]

end
end CurrentKS.HermitianCoordinates

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

lemma realDecode_eq_realify (x : Fin d × Fin d → ℝ) :
    realDecode x = KS.W08.realify (decode x) := by
  ext i j
  cases i <;> cases j <;> rfl

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

@[simp] lemma traceCLM_apply (A : H d) : traceCLM A = realTrace A := inner_one A

lemma pd_of_lower {a : ℝ} (ha : 0 < a) {A : H d} (hA : a • one ≤ A) : A ∈ pd d := by
  have hp : ((A : Mat d) - (a : ℂ) • 1).PosSemidef := hA
  have hs := (scalar_posDef ha).add_posSemidef hp
  simp only [add_sub_cancel] at hs
  exact hs

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

lemma smul_order {A B : H d} (h : A ≤ B) {r : ℝ} (hr : 0 ≤ r) : r • A ≤ r • B := by
  apply sub_nonneg.mp
  rw [← smul_sub r B A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h)) hr)

lemma scalar_mono_psd {A : H d} (hA : A ∈ psdCone d) {r s : ℝ} (hrs : r ≤ s) : r • A ≤ s • A := by
  apply sub_nonneg.mp
  rw [← sub_smul s r A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul hA (sub_nonneg.mpr hrs))

lemma invH_scalar (a : ℝ) : invH (a • (Hermitian.one : H d)) = a⁻¹ • (Hermitian.one : H d) := by
  apply Subtype.ext
  change (a • (1 : Mat d))⁻¹ = a⁻¹ • (1 : Mat d)
  have h (r : ℝ) : r • (1 : Mat d) = (r : ℂ) • (1 : Mat d) := by
    ext i j
    exact Complex.real_smul
  rw [h a, h a⁻¹, Complex.ofReal_inv]
  exact scalar_inv a

end
end CurrentKS.Hermitian

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

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Affine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m p : ℕ}

lemma blockDiagonal_posSemidef (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin p) (Fin p) ℝ) :
    (blockDiagonal A B).PosSemidef ↔ A.PosSemidef ∧ B.PosSemidef := by
  let C := Matrix.fromBlocks A (0 : Matrix (Fin m) (Fin p) ℝ) 0 B
  have he : (blockDiagonal A B).PosSemidef ↔ C.PosSemidef := by
    constructor
    · intro h
      have hd := h.submatrix (fun i : Fin m ⊕ Fin p => finSumFinEquiv i)
      simp only [blockDiagonal,Matrix.submatrix_submatrix,Function.comp_def,
        Equiv.symm_apply_apply] at hd
      exact hd
    · exact fun h => h.submatrix _
  rw [he]
  constructor
  · intro h
    exact ⟨h.submatrix (Sum.inl : Fin m → Fin m ⊕ Fin p),h.submatrix (Sum.inr : Fin p → Fin m ⊕ Fin p)⟩
  · rintro ⟨hA,hB⟩
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_,?_⟩
    · apply Matrix.isHermitian_fromBlocks_iff.mpr
      exact ⟨hA.isHermitian,by simp,by simp,hB.isHermitian⟩
    · intro x
      have ha := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
      have hb := hB.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
      simpa only [C,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,add_zero,zero_add,
        dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.star_apply,
        star_trivial,Function.comp_def] using add_nonneg ha hb

lemma blockDiagonal_realMap (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin p) (Fin p) ℚ) :
    (blockDiagonal A B).map (fun x => (x:ℝ)) =
      blockDiagonal (A.map (fun x => (x:ℝ))) (B.map (fun x => (x:ℝ))) := by
  ext i j
  change ((Matrix.fromBlocks A 0 0 B) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j):ℝ)=_
  change _=(Matrix.fromBlocks (A.map (fun x => (x:ℝ))) 0 0 (B.map (fun x => (x:ℝ))))
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp

lemma Pencil.blockDiagonal_realEval (A : Pencil n m) (B : Pencil n p) (z : Fin n → ℝ) :
    (A.blockDiagonal B).realEval z = CurrentKS.RationalSDP.blockDiagonal (A.realEval z) (B.realEval z) := by
  ext i j
  simp only [Pencil.realEval,Pencil.blockDiagonal,blockDiagonal_realMap,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [CurrentKS.RationalSDP.blockDiagonal,hi,hj,Matrix.sum_apply]

end CurrentKS.RationalSDP

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

lemma Pencil.ofAffine_realEval (C : Matrix (Fin m) (Fin m) ℚ)
    (L : (Fin n → ℚ) →ₗ[ℚ] Matrix (Fin m) (Fin m) ℚ)
    (hC : C.IsSymm) (hL : ∀ y,(L y).IsSymm)
    (L' : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hcast : ∀ y,(L y).map (fun q => (q:ℝ))=L' (fun i => (y i:ℝ))) (y : Fin n → ℝ) :
    (Pencil.ofAffine C L hC hL).realEval y=C.map (fun q => (q:ℝ))+L' y := by
  change _+∑ i,y i • (L (Pi.single i 1)).map (fun q => (q:ℝ))=_
  simp_rw [hcast]
  have hs (i : Fin n) : (fun j => ((Pi.single i 1 : Fin n → ℚ) j:ℝ))=Pi.single i 1 := by
    ext j
    simp [Pi.single_apply,apply_ite]
  simp_rw [hs]
  congr 1
  conv_rhs => rw [vector_eq_sum_single y]
  simp

lemma realFinDecode_cast (x : Fin d × Fin d → ℚ) :
    (realFinDecode d x).map (fun q => (q:ℝ))=realFinDecode d (fun i => (x i:ℝ)) := by
  change ((realDecode x).submatrix _ _).map _=(realDecode _).submatrix _ _
  rw [← Matrix.submatrix_map,realDecode_ratCast]

lemma matrixVariable_cast (second : Bool) (v : Fin (valueDimension d) → ℚ) :
    (matrixVariable d second v).map (fun q => (q:ℝ))=
      matrixVariable d second (fun i => (v i:ℝ)) := by
  change (realFinDecode d _).map _=realFinDecode d _
  rw [realFinDecode_cast]
  rfl

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
lemma cast_matrix_zero : (0 : Matrix (Fin m) (Fin m) ℚ).map (fun q => (q:ℝ))=0 := by
  ext i j
  simp
lemma cast_matrix_sub (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A-B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))-B.map (fun q => (q:ℝ)) := by
  ext i j
  simp
lemma cast_matrix_neg (A : Matrix (Fin m) (Fin m) ℚ) :
    (-A).map (fun q => (q:ℝ))= -A.map (fun q => (q:ℝ)) := by
  ext i j
  simp
lemma cast_matrix_mul (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A*B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))*B.map (fun q => (q:ℝ)) := by
  exact Matrix.map_mul (f := algebraMap ℚ ℝ)

lemma rationalSum_cast (coords : Fin N → Fin d × Fin d → ℚ) (x : Fin N → ℚ) :
    (rationalSum coords x).map (fun q => (q:ℝ))=
      rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)) := by
  simp only [rationalSum,cast_matrix_sum,cast_matrix_smul,realFinDecode_cast]

lemma rationalEta_cast (coords : Fin N → Fin d × Fin d → ℚ) (θ : Fin N → ℚ)
    (Z : Matrix (Fin (d+d)) (Fin (d+d)) ℚ) :
    (rationalEta coords θ Z).map (fun q => (q:ℝ))=
      rationalEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)) (Z.map (fun q => (q:ℝ))) := by
  simp only [rationalEta,LinearMap.sum_apply,LinearMap.smul_apply,cast_matrix_sum,
    cast_matrix_smul,sandwichLinear,LinearMap.coe_mk,AddHom.coe_mk,cast_matrix_mul,
    realFinDecode_cast,Rat.cast_mul,Rat.cast_ofNat]

lemma schurPencil_realEval (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    (schurPencil coords x θ second).realEval v =
    (Matrix.fromBlocks
      (timeCoordinate d v • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℝ)+
        (if second then rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ))
          else -rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)))-
        rationalEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)) (matrixVariable d (!second) v))
      1 1 (matrixVariable d second v)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  let L' := diagonalLinear (identityLinear (d+d) (timeCoordinate d)-
    (rationalEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ))).comp
      (matrixVariable d (!second))) (matrixVariable d second)
  have hcast (y : Fin (valueDimension d) → ℚ) :
      (diagonalLinear (identityLinear (d+d) (timeCoordinate d)-
        (rationalEta coords θ).comp (matrixVariable d (!second))) (matrixVariable d second) y).map
          (fun q => (q:ℝ))=L' (fun i => (y i:ℝ)) := by
    change (blockDiagonal _ _).map _=blockDiagonal _ _
    rw [blockDiagonal_realMap]
    congr 1
    · change ((timeCoordinate d y : ℚ) • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)-rationalEta coords θ _).map _=_
      rw [cast_matrix_sub,cast_matrix_smul,cast_matrix_one,rationalEta_cast,matrixVariable_cast]
      rfl
    · exact matrixVariable_cast _ _
  erw [schurPencil,Pencil.ofAffine_realEval _ _ _ _ L' hcast]
  have hS : ((if second then rationalSum coords x else -rationalSum coords x).map
      (fun q => (q:ℝ))) = if second then rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ))
        else -rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)) := by
    split <;> simp only [rationalSum_cast,cast_matrix_neg]
  ext i j
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [L',diagonalLinear,blockDiagonal,hi,hj,identityLinear,Matrix.add_apply,Matrix.sub_apply]
  · rename_i i' j'
    have hs := congrFun (congrFun hS i') j'
    change ((if second=true then rationalSum coords x else -rationalSum coords x) _ _ : ℝ)=_ at hs
    rw [hs]
    abel
  · simp [Matrix.one_apply,apply_ite]
  · simp [Matrix.one_apply,apply_ite]

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

lemma lowerMatrixPencil_realEval (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    (lowerMatrixPencil d second).realEval v = matrixVariable d second v-(1/400:ℝ) • 1 := by
  rw [lowerMatrixPencil,Pencil.ofAffine_realEval _ _ _ _ (matrixVariable d second)
    (matrixVariable_cast second),cast_matrix_smul,cast_matrix_one]
  norm_num
  abel
lemma upperMatrixPencil_realEval (ε : ℚ) (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    (upperMatrixPencil d ε second).realEval v = (200/(ε:ℝ)) • 1-matrixVariable d second v := by
  have hc (y : Fin (valueDimension d) → ℚ) :
      ((-(matrixVariable (R := ℚ) d second)) y).map (fun q => (q:ℝ))=
        (-(matrixVariable (R := ℝ) d second)) (fun i => (y i:ℝ)) := by
    simp only [LinearMap.neg_apply,cast_matrix_neg,matrixVariable_cast]
  erw [upperMatrixPencil,Pencil.ofAffine_realEval _ _ _ _ (-(matrixVariable (R := ℝ) d second)) hc,
    cast_matrix_smul,cast_matrix_one]
  simp only [Rat.cast_div,Rat.cast_ofNat,LinearMap.neg_apply,sub_eq_add_neg]
lemma lowerTimePencil_realEval (v : Fin (valueDimension d) → ℝ) :
    (lowerTimePencil d).realEval v=timeCoordinate d v • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hc (y : Fin (valueDimension d) → ℚ) :
      (identityLinear 1 (timeCoordinate d) y).map (fun q => (q:ℝ))=
        identityLinear 1 (timeCoordinate d) (fun i => (y i:ℝ)) := by
    change ((timeCoordinate d y : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ)).map _=_
    rw [cast_matrix_smul,cast_matrix_one]
    rfl
  erw [lowerTimePencil,Pencil.ofAffine_realEval _ _ _ _ (identityLinear 1 (timeCoordinate d)) hc,
    cast_matrix_zero,zero_add]
  rfl
lemma upperTimePencil_realEval (v : Fin (valueDimension d) → ℝ) :
    (upperTimePencil d).realEval v=(100-timeCoordinate d v) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hc (y : Fin (valueDimension d) → ℚ) :
      ((-(identityLinear (R := ℚ) 1 (timeCoordinate d))) y).map (fun q => (q:ℝ))=
        (-(identityLinear (R := ℝ) 1 (timeCoordinate d))) (fun i => (y i:ℝ)) := by
    change (-((timeCoordinate d y : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ))).map _=_
    rw [cast_matrix_neg,cast_matrix_smul,cast_matrix_one]
    rfl
  erw [upperTimePencil,Pencil.ofAffine_realEval _ _ _ _ (-(identityLinear (R := ℝ) 1 (timeCoordinate d))) hc,
    cast_matrix_smul,cast_matrix_one]
  norm_num only [Rat.cast_ofNat]
  change (100:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) + -(timeCoordinate d v • 1)=_
  module

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
lemma finRealify_decode (x : Fin d × Fin d → ℝ) : finRealify (decode x)=realFinDecode d x := by
  unfold finRealify
  rw [← realDecode_eq_realify]
  rfl
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

lemma realify_schur (T X : Matrix (Fin d) (Fin d) ℂ) :
    (realify (Matrix.fromBlocks T 1 1 X)).submatrix
      (Equiv.sumSumSumComm (Fin d) (Fin d) (Fin d) (Fin d))
      (Equiv.sumSumSumComm (Fin d) (Fin d) (Fin d) (Fin d))=
    Matrix.fromBlocks (realify T) 1 1 (realify X) := by
  ext i j
  rcases i with i | i <;> rcases i with i | i <;>
    rcases j with j | j <;> rcases j with j | j <;>
    simp [realify,Matrix.fromBlocks,Equiv.sumSumSumComm,Matrix.one_apply,apply_ite]

lemma finRealify_schur_psd (T X : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.fromBlocks (finRealify T) 1 1 (finRealify X)).PosSemidef ↔
      (Matrix.fromBlocks T (1 : Matrix (Fin d) (Fin d) ℂ) 1 X).PosSemidef := by
  let e := (finSumFinEquiv.symm : Fin (d+d) ≃ Fin d ⊕ Fin d).sumCongr
    (finSumFinEquiv.symm : Fin (d+d) ≃ Fin d ⊕ Fin d)
  have he : Matrix.fromBlocks (finRealify T) 1 1 (finRealify X)=
      (Matrix.fromBlocks (realify T) 1 1 (realify X)).submatrix e e := by
    ext i j
    cases i <;> cases j <;> simp [finRealify,e,Matrix.one_apply]
  rw [he,posSemidef_reindex_iff,← realify_schur,posSemidef_reindex_iff,realify_posSemidef_iff]

lemma finRealify_complexSum (coords : Fin N → Fin d × Fin d → ℝ) (x : Fin N → ℝ) :
    finRealify (complexSum coords x)=rationalSum coords x := by
  simp only [complexSum,finRealify_sum,finRealify_smul,finRealify_decode,rationalSum]
lemma finRealify_complexEta (coords : Fin N → Fin d × Fin d → ℝ) (θ : Fin N → ℝ)
    (Z : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (complexEta coords θ Z)=rationalEta coords θ (finRealify Z) := by
  simp only [complexEta,finRealify_sum,finRealify_smul,finRealify_mul,finRealify_decode,
    rationalEta,LinearMap.sum_apply,LinearMap.smul_apply,sandwichLinear,LinearMap.coe_mk,AddHom.coe_mk]

lemma schurPencil_psd (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    ((schurPencil coords x θ second).realEval v).PosSemidef ↔
    (Matrix.fromBlocks
      (timeCoordinate d v • (1 : Matrix (Fin d) (Fin d) ℂ)+
        (if second then complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ))
          else -complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)))-
        complexEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ))
          (decode (matrixCoordinate d (!second) v)))
      1 1 (decode (matrixCoordinate d second v))).PosSemidef := by
  rw [schurPencil_realEval,posSemidef_reindex_iff,← finRealify_schur_psd]
  simp only [finRealify_sub,finRealify_add,finRealify_smul,finRealify_one,
    finRealify_complexEta,finRealify_decode]
  split <;> simp only [finRealify_complexSum,finRealify_neg,matrixVariable,LinearMap.comp_apply]

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ComplexValueProgram
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators ComplexOrder

variable {d N : ℕ}

lemma scalar_one_psd_iff (r : ℝ) :
    (r • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef ↔ 0 ≤ r := by
  constructor
  · intro h
    simpa using h.diag_nonneg (i := (0 : Fin 1))
  · intro hr
    exact (Matrix.PosSemidef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef).smul hr

lemma lowerMatrixPencil_psd (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    ((lowerMatrixPencil d second).realEval v).PosSemidef ↔
    (decode (matrixCoordinate d second v)-(1/400:ℝ) •
      (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
  rw [lowerMatrixPencil_realEval,← finRealify_psd]
  simp only [finRealify_sub,finRealify_smul,finRealify_one,finRealify_decode,
    matrixVariable,LinearMap.comp_apply]
lemma upperMatrixPencil_psd (ε : ℚ) (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    ((upperMatrixPencil d ε second).realEval v).PosSemidef ↔
    ((200/(ε:ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)-
      decode (matrixCoordinate d second v)).PosSemidef := by
  rw [upperMatrixPencil_realEval,← finRealify_psd]
  simp only [finRealify_sub,finRealify_smul,finRealify_one,finRealify_decode,
    matrixVariable,LinearMap.comp_apply]

lemma valuePencil_psd (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (ε : ℚ) (v : Fin (valueDimension d) → ℝ) :
    ((valuePencil coords x θ ε).realEval v).PosSemidef ↔
    complexValueProgram (ε:ℝ)
      (complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)))
      (complexEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)))
      (timeCoordinate d v) (decode (matrixCoordinate d false v))
      (decode (matrixCoordinate d true v)) := by
  simp only [valuePencil,Pencil.blockDiagonal_realEval,blockDiagonal_posSemidef,
    schurPencil_psd,lowerMatrixPencil_psd,upperMatrixPencil_psd,
    lowerTimePencil_realEval,upperTimePencil_realEval,scalar_one_psd_iff,
    Bool.false_eq_true,ite_false, if_false,Bool.not_false,ite_true, if_true,Bool.not_true,
    complexValueProgram,sub_eq_add_neg]
  simp only [← sub_eq_add_neg,sub_nonneg]
  tauto

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Point
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma feasible_iff (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z.2.1 ∈ pd d ∧ z.2.2 ∈ pd d ∧
      invH z.2.1 + S + η z.2.2 ≤ z.1 • (Hermitian.one : H d) ∧
      invH z.2.2 - S + η z.2.1 ≤ z.1 • (Hermitian.one : H d) := by
  simp only [feasible, domain, residual, mem_ofPred_eq, sub_nonpos]
  tauto

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SchurBlock
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma schurBlock_psd_iff (T X : H d) (hX : X ∈ pd d) :
    (schurBlock T X).PosSemidef ↔ invH X ≤ T := by
  let : Invertible (X : Mat d) := hX.isUnit.invertible
  have hh := Matrix.PosDef.fromBlocks₂₂ (T : Mat d) (1 : Mat d) hX
  simp only [Matrix.conjTranspose_one,one_mul,mul_one] at hh
  change (schurBlock T X).PosSemidef ↔ ((T-invH X : H d) : Mat d).PosSemidef at hh
  rw [← mem_psdCone,mem_psd_iff_nonneg,sub_nonneg] at hh
  exact hh

lemma valueBlocks_iff (S : H d) (η : H d →L[ℝ] H d) (z : Point d)
    (hX : z.2.1 ∈ pd d) (hY : z.2.2 ∈ pd d) :
    (valueBlock₁ S η z).PosSemidef ∧ (valueBlock₂ S η z).PosSemidef ↔ z ∈ feasible S η := by
  rw [valueBlock₁,valueBlock₂,schurBlock_psd_iff _ _ hX,schurBlock_psd_iff _ _ hY,feasible_iff]
  have h₁ : (invH z.2.1 ≤ z.1 • (Hermitian.one : H d)-S-η z.2.2) ↔
      invH z.2.1+S+η z.2.2 ≤ z.1 • (Hermitian.one : H d) := by
    rw [le_sub_iff_add_le,le_sub_iff_add_le]
    rw [show invH z.2.1+η z.2.2+S = invH z.2.1+S+η z.2.2 by module]
  have h₂ : (invH z.2.2 ≤ z.1 • (Hermitian.one : H d)+S-η z.2.1) ↔
      invH z.2.2-S+η z.2.1 ≤ z.1 • (Hermitian.one : H d) := by
    rw [le_sub_iff_add_le,← sub_le_iff_le_add]
    rw [show invH z.2.2+η z.2.1-S = invH z.2.2-S+η z.2.1 by module]
  rw [h₁,h₂]
  exact ⟨fun h => ⟨hX,hY,h.1,h.2⟩,fun h => ⟨h.2.2.1,h.2.2.2⟩⟩

lemma mem_valueSpectrahedron (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ valueSpectrahedron ε S η ↔ oracleBox ε z ∧ z ∈ feasible S η := by
  constructor
  · rintro ⟨hb,h₁,h₂⟩
    exact ⟨hb,(valueBlocks_iff S η z
      (pd_of_lower (by norm_num : (0:ℝ)<1/400) hb.2.1.1)
      (pd_of_lower (by norm_num : (0:ℝ)<1/400) hb.2.2.1)).mp ⟨h₁,h₂⟩⟩
  · rintro ⟨hb,hz⟩
    obtain ⟨hX,hY,_,_⟩ := (feasible_iff S η z).mp hz
    exact ⟨hb,(valueBlocks_iff S η z hX hY).mpr hz⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PackValue
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
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

variable {d : ℕ}

lemma time_packValue (z : Point d) : timeCoordinate d (packValue z) = z.1 := by
  simp [timeCoordinate,packValue]
lemma matrix_packValue (z : Point d) (second : Bool) :
    matrixCoordinate d second (packValue z) = encode (if second then z.2.2 else z.2.1) := by
  funext ij
  cases second <;> simp [matrixCoordinate,packValue]
lemma unpack_packValue (z : Point d) : unpackValue (packValue z)=z := by
  simp only [unpackValue,time_packValue,matrix_packValue,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  change (z.1,assemble (extract z.2.1),assemble (extract z.2.2))=z
  rw [assemble_extract,assemble_extract]

lemma complexValueProgram_iff (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (ηm : Mat d → Mat d) (hηm : ∀ W : H d,ηm W=(η W : Mat d)) (z : Point d) :
    complexValueProgram ε S ηm z.1 z.2.1 z.2.2 ↔ z ∈ valueSpectrahedron ε S η := by
  have ho (A B : H d) : ((B : Mat d)-A).PosSemidef ↔ A ≤ B := by
    change ((B-A : H d) : Mat d).PosSemidef ↔ _
    rw [← mem_psdCone,mem_psd_iff_nonneg,sub_nonneg]
  simp only [complexValueProgram,hηm]
  change (valueBlock₁ S η z).PosSemidef ∧ (valueBlock₂ S η z).PosSemidef ∧
    ((z.2.1 : Mat d)-((1/400:ℝ) • Hermitian.one : H d)).PosSemidef ∧
    (((200/ε:ℝ) • Hermitian.one : H d)- (z.2.1 : Mat d)).PosSemidef ∧
    ((z.2.2 : Mat d)-((1/400:ℝ) • Hermitian.one : H d)).PosSemidef ∧
    (((200/ε:ℝ) • Hermitian.one : H d)- (z.2.2 : Mat d)).PosSemidef ∧
    0 ≤ z.1 ∧ z.1 ≤ 100 ↔ _
  rw [ho,ho,ho,ho]
  simp only [valueSpectrahedron,Set.mem_ofPred_eq,oracleBox,Set.mem_Icc]
  tauto

lemma matrixCoordinate_norm (v : EuclideanSpace ℝ (Fin (valueDimension d))) (s : Bool) :
    ‖(WithLp.toLp 2 (matrixCoordinate d s v) : Space d)‖ ≤ ((d:ℝ)^2+1)*‖v‖ := by
  have he (ij : Fin d × Fin d) : ‖matrixCoordinate d s v ij‖ ≤ ‖v‖ := by
    exact PiLp.norm_apply_le _ _
  have hs := Finset.sum_le_sum (fun ij (_ : ij ∈ (Finset.univ : Finset (Fin d × Fin d))) =>
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (he ij))
  have hh : ‖(WithLp.toLp 2 (matrixCoordinate d s v) : Space d)‖^2 ≤ (d:ℝ)^2*‖v‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_mul,pow_two] using hs
  have hd : 0 ≤ (d:ℝ)^2 := sq_nonneg _
  have hb : (d:ℝ)^2 ≤ ((d:ℝ)^2+1)^2 := by nlinarith
  have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
  have hp : 0 ≤ ((d:ℝ)^2+1)*‖v‖ := by positivity
  nlinarith [norm_nonneg (WithLp.toLp 2 (matrixCoordinate d s v) : Space d)]

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PositiveMapMono
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma positiveMap_mono (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d) {A B : H d} (h : A ≤ B) : η A ≤ η B := by
  apply sub_nonneg.mp
  rw [← map_sub]
  exact psd_nonneg (hη (B-A) ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h)))

lemma invH_order_bound {X : H d} {r : ℝ} (hr : 0 < r)
    (h : r • (Hermitian.one : H d) ≤ X) : invH X ≤ r⁻¹ • Hermitian.one := by
  have hX := pd_of_lower hr h
  have hi := inverse_antitone (scalar_posDef hr) hX h
  change invH X ≤ invH (r • (Hermitian.one : H d)) at hi
  rwa [invH_scalar] at hi

lemma value_center_neighborhood (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d)
    (hη1 : η Hermitian.one ≤ (384:ℝ) • Hermitian.one)
    (hSlo : -(1:ℝ) • (Hermitian.one : H d) ≤ S)
    (hShi : S ≤ (1:ℝ) • (Hermitian.one : H d))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : Point d)
    (ht : |z.1-50| ≤ 1/1000)
    (hX : ‖z.2.1-(1/20:ℝ) • (Hermitian.one : H d)‖ ≤ 1/1000)
    (hY : ‖z.2.2-(1/20:ℝ) • (Hermitian.one : H d)‖ ≤ 1/1000) :
    z ∈ valueSpectrahedron ε S η := by
  have bounds (X : H d) (hX : ‖X-(1/20:ℝ) • (Hermitian.one : H d)‖ ≤ 1/1000) :
      (1/21:ℝ) • (Hermitian.one : H d) ≤ X ∧ X ≤ (51/1000:ℝ) • Hermitian.one := by
    obtain ⟨hl,hu⟩ := ball_order_bounds X ((1/20:ℝ) • (Hermitian.one : H d)) hX
    have hl' : ((1/20-1/1000:ℝ) • (Hermitian.one : H d)) ≤ X := by
      convert hl using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | module
    rw [← add_smul] at hu
    exact ⟨(scalar_one_mono (by norm_num : (1/21:ℝ)≤1/20-1/1000)).trans hl',by
      convert hu using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | module⟩
  obtain ⟨hXlo,hXhi⟩ := bounds z.2.1 hX
  obtain ⟨hYlo,hYhi⟩ := bounds z.2.2 hY
  have htlo : (49:ℝ) ≤ z.1 := by have := (abs_le.mp ht).1; linarith
  have hthi : z.1 ≤ (51:ℝ) := by have := (abs_le.mp ht).2; linarith
  have hXpd := pd_of_lower (by norm_num : (0:ℝ)<1/21) hXlo
  have hYpd := pd_of_lower (by norm_num : (0:ℝ)<1/21) hYlo
  have hXinv : invH z.2.1 ≤ (21:ℝ) • Hermitian.one := by
    simpa using invH_order_bound (by norm_num : (0:ℝ)<1/21) hXlo
  have hYinv : invH z.2.2 ≤ (21:ℝ) • Hermitian.one := by
    simpa using invH_order_bound (by norm_num : (0:ℝ)<1/21) hYlo
  have hmap (X : H d) (hX : X ≤ (51/1000:ℝ) • Hermitian.one) :
      η X ≤ (20:ℝ) • Hermitian.one := by
    calc
      _ ≤ η ((51/1000:ℝ) • Hermitian.one) := positiveMap_mono η hη hX
      _ = (51/1000:ℝ) • η Hermitian.one := map_smul η _ _
      _ ≤ (51/1000:ℝ) • ((384:ℝ) • Hermitian.one) := smul_order hη1 (by norm_num)
      _ ≤ (20:ℝ) • Hermitian.one := by rw [smul_smul]; exact scalar_one_mono (by norm_num)
  have hfit : (42:ℝ) • (Hermitian.one : H d) ≤ z.1 • Hermitian.one := scalar_one_mono (by linarith)
  have hminus : -S ≤ (1:ℝ) • (Hermitian.one : H d) := by
    convert neg_le_neg hSlo using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | module
  have hf : z ∈ feasible S η := by
    apply (feasible_iff S η z).mpr
    refine ⟨hXpd,hYpd,?_,?_⟩
    · have hh := add_le_add (add_le_add hXinv hShi) (hmap z.2.2 hYhi)
      apply le_trans hh
      convert hfit using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | module
    · have hh := add_le_add (add_le_add hYinv hminus) (hmap z.2.1 hXhi)
      change invH z.2.2 + -S + η z.2.1 ≤ _
      apply le_trans hh
      convert hfit using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | module
  have hlo : (1/400:ℝ) • (Hermitian.one : H d) ≤ (1/21:ℝ) • Hermitian.one := scalar_one_mono (by norm_num)
  have hr : (51/1000:ℝ) ≤ 200/ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hup := scalar_one_mono (d := d) hr
  apply (mem_valueSpectrahedron ε S η z).mpr
  exact ⟨⟨⟨by linarith,by linarith⟩,⟨hlo.trans hXlo,hXhi.trans hup⟩,
    ⟨hlo.trans hYlo,hYhi.trans hup⟩⟩,hf⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueOuterRadius
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
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

lemma unpackValue_sub (v w : EuclideanSpace ℝ (Fin (valueDimension d))) :
    unpackValue (v-w)=unpackValue v-unpackValue w := by
  apply Prod.ext
  · change timeCoordinate d (v.ofLp-w.ofLp)=_
    exact (timeCoordinate (R := ℝ) d).map_sub _ _
  · apply Prod.ext
    all_goals
      simp only [unpackValue,WithLp.ofLp_sub,map_sub,WithLp.toLp_sub]
      exact (assembleLinear d).map_sub _ _

lemma timeCoordinate_norm (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    |timeCoordinate d v| ≤ ‖v‖ := by
  simpa only [timeCoordinate,LinearMap.proj_apply,Real.norm_eq_abs] using
    PiLp.norm_apply_le v (valueIndex d (.inl 0))

lemma unpackValue_matrix_norm (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    ‖(unpackValue v).2.1‖ ≤ 2*((d:ℝ)^2+1)*‖v‖ ∧
    ‖(unpackValue v).2.2‖ ≤ 2*((d:ℝ)^2+1)*‖v‖ := by
  constructor
  all_goals
    apply (norm_assemble _).trans
    exact (mul_le_mul_of_nonneg_left (matrixCoordinate_norm v _) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

lemma value_center_coordinate_ball (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d)
    (hη1 : η Hermitian.one ≤ (384:ℝ) • Hermitian.one)
    (hSlo : -(1:ℝ) • (Hermitian.one : H d) ≤ S)
    (hShi : S ≤ (1:ℝ) • (Hermitian.one : H d))
    {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : EuclideanSpace ℝ (Fin (valueDimension d)))
    (hv : v ∈ Metric.closedBall (packValue (50,(1/20:ℝ) • (Hermitian.one : H d),
      (1/20:ℝ) • (Hermitian.one : H d))) (valueInnerRadius d:ℝ)) :
    unpackValue v ∈ valueSpectrahedron (ε:ℝ) S η := by
  let c : Point d := (50,(1/20:ℝ) • (Hermitian.one : H d),(1/20:ℝ) • Hermitian.one)
  have hr : ‖v-packValue c‖ ≤ (valueInnerRadius d:ℝ) := by
    rw [← dist_eq_norm]
    exact hv
  have hD : 0 < (d:ℝ)^2+1 := by positivity
  have hs : (valueInnerRadius d:ℝ) ≤ 1/1000 := by
    simp only [valueInnerRadius,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add,Rat.cast_pow,Rat.cast_natCast]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (d:ℝ)]
  have hm : 2*((d:ℝ)^2+1)*(valueInnerRadius d:ℝ) ≤ 1/1000 := by
    simp only [valueInnerRadius,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add,Rat.cast_pow,Rat.cast_natCast]
    field_simp
    nlinarith [sq_nonneg (d:ℝ)]
  have ht := (timeCoordinate_norm (v-packValue c)).trans (hr.trans hs)
  have hxy := unpackValue_matrix_norm (v-packValue c)
  have hx := hxy.1.trans ((mul_le_mul_of_nonneg_left hr (by positivity)).trans hm)
  have hy := hxy.2.trans ((mul_le_mul_of_nonneg_left hr (by positivity)).trans hm)
  have he := unpackValue_sub v (packValue c)
  rw [unpack_packValue] at he
  rw [he] at hx hy
  apply value_center_neighborhood S η hη hη1 hSlo hShi (by exact_mod_cast hε)
    (by exact_mod_cast hε1) (unpackValue v)
  · change |timeCoordinate d (v.ofLp) - 50| ≤ _
    change |timeCoordinate d (v.ofLp - (packValue c).ofLp)| ≤ _ at ht
    simp only [map_sub,time_packValue,c] at ht
    exact ht
  · exact hx
  · exact hy

end
end CurrentKS.RationalSDP

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r791565_2 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma sum_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) : (∑ i, A i) ≤ (Hermitian.one : H d) := by
  have hp := trace_bound_above (psd_sum Finset.univ A fun i _ => hA i)
  simpa only [realTrace_sum,htr,one_smul] using hp

lemma S_bounds (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) {x : Coordinates N} (hx : Cube x) :
    -(Hermitian.one : H d) ≤ S A x ∧ S A x ≤ (Hermitian.one : H d) := by
  have hsum := sum_le_one A hA htr
  have hupper : S A x ≤ ∑ i, A i := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [one_smul] using scalar_mono_psd (hA i) (abs_le.mp (hx i)).2
  have hlower : -(∑ i, A i) ≤ S A x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := scalar_mono_psd (hA i) (abs_le.mp (hx i)).1
    have he : (-1 : ℝ) • A i = -A i := neg_one_smul ℝ (A i)
    rw [he] at hh
    exact hh
  exact ⟨(neg_le_neg hsum).trans hlower,hupper.trans hsum⟩

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ParameterCube
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma etaTheta_apply (c : ℝ) (A : Fin N → H d) (θ : Coordinates N) (Z : H d) :
    etaTheta c A θ Z = ∑ i,(c*θ i) • sandwich (A i) Z := by
  exact sum_apply Finset.univ (fun i => (c*θ i) • sandwichCLM (A i)) Z

lemma etaTheta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {θ : Coordinates N}
    (hθ : ParameterCube θ) : ∀ Z ∈ psdCone d, etaTheta c A θ Z ∈ psdCone d := by
  intro Z hZ
  rw [etaTheta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (hθ i).1)

lemma etaTheta_one_bound {c ν : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hν : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    {θ : Coordinates N} (hθ : ParameterCube θ) :
    etaTheta c A θ (Hermitian.one : H d) ≤ (c*ν) • (Hermitian.one : H d) := by
  rw [etaTheta_apply,SemigroupAction.mul_smul]
  apply le_trans _ (smul_order hν hc)
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact scalar_mono_psd (sandwich_psd _ _ one_mem_psdCone)
    (mul_le_of_le_one_right hc (hθ i).2)

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RationalAtoms
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalSDP
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma complexSum_rationalAtoms (coords : Fin N → Fin d × Fin d → ℚ) (x : Fin N → ℚ) :
    complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)) =
      ((S (rationalAtoms coords) (fun i => (x i:ℝ))) : Mat d) := by
  simp only [complexSum,S,Submodule.coe_sum,Submodule.coe_smul_of_tower,
    rationalAtoms,assemble]

lemma complexEta_rationalAtoms (coords : Fin N → Fin d × Fin d → ℚ) (θ : Fin N → ℚ)
    (Z : H d) :
    complexEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)) Z =
      ((etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ))) Z : Mat d) := by
  rw [etaTheta_apply]
  simp only [complexEta,Submodule.coe_sum,Submodule.coe_smul_of_tower,rationalAtoms,assemble]
  rfl

lemma valuePencil_feasible (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (ε : ℚ) (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    v ∈ (valuePencil coords x θ ε).feasible ↔
      unpackValue v ∈ valueSpectrahedron (ε:ℝ)
        (S (rationalAtoms coords) (fun i => (x i:ℝ)))
        (etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ))) := by
  change ((valuePencil coords x θ ε).realEval v).PosSemidef ↔ _
  rw [valuePencil_psd,complexSum_rationalAtoms]
  exact complexValueProgram_iff _ _ _ _ (complexEta_rationalAtoms coords θ) (unpackValue v)

lemma valuePencil_ball_oai (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν : ℝ} (hν : ν ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (hx : Cube (fun i => (x i:ℝ))) (hθ : ParameterCube (fun i => (θ i:ℝ)))
    {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Metric.closedBall (packValue (50,(1/20:ℝ) • (Hermitian.one : H d),
      (1/20:ℝ) • (Hermitian.one : H d))) (valueInnerRadius d:ℝ) ⊆
      (valuePencil coords x θ ε).feasible := by
  intro v hv
  apply (valuePencil_feasible coords x θ ε v).mpr
  apply value_center_coordinate_ball _ _ (etaTheta_positive (by norm_num) _ hθ) _ _ _ hε hε1 v hv
  · exact (etaTheta_one_bound (by norm_num) _ hvar hθ).trans
      (scalar_one_mono (by linarith : 384*ν≤384))
  · convert (S_bounds _ hA htr hx).1 using 1
    all_goals try with_reducible_and_instances rfl
    exact neg_one_smul ℝ (Hermitian.one : H d)
  · simpa only [one_smul] using (S_bounds _ hA htr hx).2

end CurrentKS.RationalSDP

end

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.RationalSDP.valuePencil_ball_oai := @OAI.CurrentKS.RationalSDP.valuePencil_ball_oai
