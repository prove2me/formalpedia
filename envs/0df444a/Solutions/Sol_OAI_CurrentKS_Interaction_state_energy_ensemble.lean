-- Prove2me | solution 1 for OAI.CurrentKS.Interaction.state_energy_ensemble
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:28.613244+00:00
-- url     : https://prove2.me/submissions/777a6dcd-923c-4c83-866f-dd1d0ca1dcba

import Mathlib
import Definitions.Def_OAIQ241TT002

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

@[simp] lemma traceCLM_apply (A : H d) : traceCLM A = realTrace A := inner_one A

lemma psd_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ A := hA.nonneg

lemma mem_psd_iff_nonneg (A : H d) : A ∈ psdCone d ↔ 0 ≤ A := by
  constructor
  · exact psd_nonneg
  · intro hA
    have hh : (0 : Mat d) ≤ (A : Mat d) := hA
    exact hh.posSemidef

lemma trace_bound_above {A : H d} (hA : A ∈ psdCone d) : A ≤ realTrace A • one :=
  le_trace_smul_one hA

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InnerMonoRightPsd
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

lemma inner_mono_right_psd (A : H d) (hA : A ∈ psdCone d) {B C : H d} (hBC : B ≤ C) :
    inner ℝ A B ≤ inner ℝ A C := by
  have hh := inner_nonneg_of_psd A (C-B) hA ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hBC))
  rw [inner_sub_right] at hh
  linarith

lemma inner_le_trace_mul_trace (A B : H d) (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    inner ℝ A B ≤ realTrace A * realTrace B := by
  have hh := inner_mono_right_psd A hA (trace_bound_above hB)
  rw [real_inner_smul_right A (one : H d) (realTrace B),inner_one'] at hh
  nlinarith

lemma sandwich_inverse_left (X A : H d) (hX : X ∈ pd d) :
    sandwich X (sandwich (invH X) A) = A := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  apply Subtype.ext
  change (X : Mat d)*((X : Mat d)⁻¹*(A : Mat d)*(X : Mat d)⁻¹)*(X : Mat d) = (A : Mat d)
  simp only [← mul_assoc, Matrix.mul_nonsing_inv _ hx,one_mul]
  rw [mul_assoc,Matrix.nonsing_inv_mul _ hx,mul_one]

section SquareRoot
open scoped Matrix.Norms.L2Operator

lemma exists_psd_square (X : H d) (hX : X ∈ psdCone d) :
    ∃ R : H d, R ∈ psdCone d ∧ (R : Mat d)*(R : Mat d) = (X : Mat d) := by
  let : CStarAlgebra (Mat d) := {}
  have hr : (CFC.sqrt (X : Mat d)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  exact ⟨⟨CFC.sqrt (X : Mat d),hr.isHermitian⟩,hr,CFC.sqrt_mul_sqrt_self _ hX.nonneg⟩
end SquareRoot

lemma inner_sandwich_square (R A B : H d) :
    inner ℝ (sandwich R A) (sandwich R B) = inner ℝ A (sandwich (sandwich R one) B) := by
  rw [inner_eq_trace,inner_eq_trace]
  change (((R : Mat d)*(A : Mat d)*(R : Mat d))*((R : Mat d)*(B : Mat d)*(R : Mat d))).trace.re =
    ((A : Mat d)*(((R : Mat d)*1*(R : Mat d))*(B : Mat d)*((R : Mat d)*1*(R : Mat d)))).trace.re
  simp only [mul_one]
  simp only [mul_assoc]
  rw [Matrix.trace_mul_comm (R : Mat d)]
  simp only [mul_assoc]

lemma inner_sandwich_le (X A B : H d) (hX : X ∈ psdCone d)
    (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    inner ℝ A (sandwich X B) ≤ inner ℝ A X * inner ℝ B X := by
  obtain ⟨R,hR,hRX⟩ := exists_psd_square X hX
  have he : sandwich R one = X := by
    apply Subtype.ext
    change (R : Mat d)*1*(R : Mat d) = (X : Mat d)
    simpa only [mul_one] using hRX
  have hh := inner_le_trace_mul_trace (sandwich R A) (sandwich R B)
    (sandwich_psd _ _ hA) (sandwich_psd _ _ hB)
  rw [inner_sandwich_square,he,← inner_one (sandwich R A),← inner_one (sandwich R B),
    inner_sandwich R A one, inner_sandwich R B one, he,
    real_inner_comm A X,real_inner_comm B X] at hh
  exact hh

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_JordanCLM
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

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r6ae1d0_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
lemma jordanCLM_val (A B U : H d) :
    ((jordanCLM A B U : H d) : Mat d) =
      (A : Mat d) * (U : Mat d) * (B : Mat d) + (B : Mat d) * (U : Mat d) * (A : Mat d) := by
  change ((A : Mat d)+(B : Mat d)) * (U : Mat d) * ((A : Mat d)+(B : Mat d)) -
    (A : Mat d)*(U : Mat d)*(A : Mat d) - (B : Mat d)*(U : Mat d)*(B : Mat d) = _
  noncomm_ring

lemma jordanCLM_symmetric (A B : H d) : (jordanCLM A B).toLinearMap.IsSymmetric := by
  intro U V
  change inner ℝ (sandwich (A+B) U - sandwich A U - sandwich B U) V =
    inner ℝ U (sandwich (A+B) V - sandwich A V - sandwich B V)
  simp only [inner_sub_left, inner_sub_right, inner_sandwich]

lemma jordanCLM_quadratic (A B U : H d) :
    inner ℝ U (jordanCLM A B U) = 2 * inner ℝ B (sandwich U A) := by
  rw [inner_eq_trace, inner_eq_trace, jordanCLM_val, sandwich_val, mul_add, Matrix.trace_add,
    Complex.add_re]
  have h₁ : ((U : Mat d) * ((A : Mat d)*(U : Mat d)*(B : Mat d))).trace =
      ((B : Mat d)* ((U : Mat d)*(A : Mat d)*(U : Mat d))).trace := by
    rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm]
  have h₂ : ((U : Mat d) * ((B : Mat d)*(U : Mat d)*(A : Mat d))).trace =
      ((B : Mat d)* ((U : Mat d)*(A : Mat d)*(U : Mat d))).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [h₁, h₂]
  ring

end
end CurrentKS.Hermitian

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CovarianceE
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open scoped BigOperators
open Matrix

variable {m : ℕ}

attribute [local instance] OAI.CurrentKS.Covariance.instInnerProductSpaceReal_solutions
local instance instLocallyConvexSpaceRealMat : LocallyConvexSpace ℝ (Mat m) :=
  inferInstanceAs (LocallyConvexSpace ℝ (Fin m → Fin m → ℝ))

theorem projectionMatrix_toEuclideanLin (G : Submodule ℝ (E m)) :
    Matrix.toEuclideanLin (projectionMatrix G) = G.starProjection.toLinearMap := by
  simp [projectionMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal]

theorem projectionMatrix_posSemidef (G : Submodule ℝ (E m)) :
    (projectionMatrix G).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, projectionMatrix_toEuclideanLin]
  exact ⟨G.starProjection_isSymmetric, G.re_inner_starProjection_nonneg⟩

theorem projectionMatrix_trace (G : Submodule ℝ (E m)) :
    (projectionMatrix G).trace = Module.finrank ℝ G := by
  rw [projectionMatrix, ← LinearMap.trace_eq_matrix_trace]
  have hp : LinearMap.IsProj G G.starProjection.toLinearMap :=
    ⟨G.starProjection_apply_mem, fun x hx => G.starProjection_eq_self_iff.mpr hx⟩
  exact hp.trace

theorem projectionMatrix_add_orthogonal (G : Submodule ℝ (E m)) :
    projectionMatrix G + projectionMatrix Gᗮ = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [map_add, projectionMatrix_toEuclideanLin, projectionMatrix_toEuclideanLin]
  rw [Matrix.toLpLin_one]
  ext w i
  have h := G.starProjection_add_starProjection_orthogonal w
  exact congrArg (fun v : E m => v i) h

theorem projectionMatrix_diag_le_one (G : Submodule ℝ (E m)) (i : Fin m) :
    projectionMatrix G i i ≤ 1 := by
  have hp := (projectionMatrix_posSemidef Gᗮ).diag_nonneg (i := i)
  have he := congrFun (congrFun (projectionMatrix_add_orthogonal G) i) i
  simp only [Matrix.add_apply, Matrix.one_apply_eq] at he
  linarith

theorem abs_entry_le_trace {A : Mat m} (hA : A.PosSemidef) (i j : Fin m) :
    |A i j| ≤ A.trace := by
  have hi : A i i ≤ A.trace :=
    Finset.single_le_sum (fun k _ => hA.diag_nonneg (i := k)) (Finset.mem_univ i)
  have hj : A j j ≤ A.trace :=
    Finset.single_le_sum (fun k _ => hA.diag_nonneg (i := k)) (Finset.mem_univ j)
  have hsym : A j i = A i j := by simpa using hA.isHermitian.apply i j
  have hp := hA.2 (Finsupp.single i 1 + Finsupp.single j 1)
  have hm := hA.2 (Finsupp.single i 1 + Finsupp.single j (-1))
  simp [Finsupp.sum_add_index, mul_add, add_mul, hsym, -Finsupp.single_neg] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem isClosed_psd : IsClosed {A : Mat m | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · exact isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

theorem isClosed_psdTraceBound (B : ℝ) : IsClosed (psdTraceBound (m := m) B) :=
  isClosed_psd.inter (isClosed_le continuous_id.matrix_trace continuous_const)

theorem isCompact_psdTraceBound (B : ℝ) : IsCompact (psdTraceBound (m := m) B) := by
  refine (isCompact_Icc : IsCompact
    (Set.Icc (fun (_ : Fin m) (_ : Fin m) => -B) (fun _ _ => B))).of_isClosed_subset
      (isClosed_psdTraceBound B) ?_
  intro A hA
  constructor
  · intro i j
    exact (abs_le.mp ((abs_entry_le_trace hA.1 i j).trans hA.2)).1
  · intro i j
    exact (abs_le.mp ((abs_entry_le_trace hA.1 i j).trans hA.2)).2

theorem isClosed_supported (G : Submodule ℝ (E m)) :
    IsClosed {A : Mat m | Supported G A} := by
  let : ContinuousSMul ℝ (E m) := IsBoundedSMul.continuousSMul
  simp only [Supported, Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  let f : Mat m →ₗ[ℝ] E m :=
    (LinearMap.applyₗ x).comp Matrix.toEuclideanLin.toLinearMap
  exact G.closed_of_finiteDimensional.preimage f.continuous_of_finiteDimensional

theorem isClosed_feasible (G : Submodule ℝ (E m)) : IsClosed (feasible G) := by
  unfold feasible
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact isClosed_psd.inter ((isClosed_supported G).inter
    (isClosed_iInter fun i => isClosed_le (continuous_id.matrix_elem i i) continuous_const))

theorem feasible_trace_le (G : Submodule ℝ (E m)) {A : Mat m} (hA : A ∈ feasible G) :
    A.trace ≤ m := by
  calc
    A.trace ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ => hA.2.2 i
    _ = m := by simp

theorem isCompact_feasible (G : Submodule ℝ (E m)) : IsCompact (feasible G) := by
  exact (isCompact_psdTraceBound (m : ℝ)).of_isClosed_subset (isClosed_feasible G)
    (fun A hA => ⟨hA.1, feasible_trace_le G hA⟩)

theorem convex_feasible (G : Submodule ℝ (E m)) : Convex ℝ (feasible G) := by
  intro A hA B hB a b ha hb hab
  refine ⟨(hA.1.smul ha).add (hB.1.smul hb), ?_, ?_⟩
  · intro x
    simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
      using G.add_mem (G.smul_mem a (hA.2.1 x)) (G.smul_mem b (hB.2.1 x))
  · intro i
    change a * A i i + b * B i i ≤ 1
    calc
      _ ≤ a * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left (hA.2.2 i) ha)
        (mul_le_mul_of_nonneg_left (hB.2.2 i) hb)
      _ = 1 := by simpa using hab

theorem projectionMatrix_mem_feasible {G W : Submodule ℝ (E m)} (hWG : W ≤ G) :
    projectionMatrix W ∈ feasible G := by
  refine ⟨projectionMatrix_posSemidef W, ?_, projectionMatrix_diag_le_one W⟩
  intro x
  rw [projectionMatrix_toEuclideanLin]
  exact hWG (W.starProjection_apply_mem x)

theorem entry_sq_le_diag_mul {A : Mat m} (hA : A.PosSemidef) (i j : Fin m) :
    (A i j) ^ 2 ≤ A i i * A j j := by
  have hsym : A j i = A i j := by simpa using hA.isHermitian.apply i j
  have hq : ∀ t : ℝ, 0 ≤ A i i * (t * t) + (2 * A i j) * t + A j j := by
    intro t
    have hp := hA.2 (Finsupp.single i t + Finsupp.single j 1)
    simp [Finsupp.sum_add_index, mul_add, add_mul, hsym] at hp
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

theorem entry_eq_zero_of_diag_eq_zero {A : Mat m} (hA : A.PosSemidef)
    (i j : Fin m) (hi : A i i = 0) : A i j = 0 := by
  have h := entry_sq_le_diag_mul hA i j
  rw [hi, zero_mul] at h
  nlinarith [sq_nonneg (A i j)]

theorem whiten_posSemidef {A : Mat m} (hA : A.PosSemidef) :
    (whiten A).PosSemidef := by
  simpa only [whiten, Matrix.diagonal_conjTranspose, star_trivial] using
    hA.mul_mul_conjTranspose_same (Matrix.diagonal fun i => (Real.sqrt (A i i))⁻¹)

theorem whiten_apply (A : Mat m) (i j : Fin m) :
    whiten A i j = (Real.sqrt (A i i))⁻¹ * A i j * (Real.sqrt (A j j))⁻¹ := by
  simp [whiten, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem whiten_diag_le_one {A : Mat m} (hA : A.PosSemidef) (i : Fin m) :
    whiten A i i ≤ 1 := by
  rw [whiten_apply]
  by_cases hi : A i i = 0
  · simp [hi]
  · have hs : Real.sqrt (A i i) ≠ 0 := Real.sqrt_ne_zero'.mpr <|
      lt_of_le_of_ne hA.diag_nonneg (Ne.symm hi)
    have he : (Real.sqrt (A i i))⁻¹ * A i i * (Real.sqrt (A i i))⁻¹ = 1 := by
      calc
        _ = (Real.sqrt (A i i))⁻¹ * (Real.sqrt (A i i)) ^ 2 *
            (Real.sqrt (A i i))⁻¹ := by rw [Real.sq_sqrt hA.diag_nonneg]
        _ = 1 := by field_simp
    exact he.le

theorem whiten_trace_le {A : Mat m} (hA : A.PosSemidef) : (whiten A).trace ≤ m := by
  calc
    (whiten A).trace ≤ ∑ _i : Fin m, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => whiten_diag_le_one hA i
    _ = m := by simp

theorem reconstruct_whiten {A : Mat m} (hA : A.PosSemidef) :
    sqrtDiagonal A * whiten A * sqrtDiagonal A = A := by
  ext i j
  simp only [sqrtDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, whiten_apply]
  by_cases hi : A i i = 0
  · simp [hi, entry_eq_zero_of_diag_eq_zero hA i j hi]
  by_cases hj : A j j = 0
  · have hz : A i j = 0 := by
      have hsym : A j i = A i j := by simpa using hA.isHermitian.apply i j
      rw [← hsym]
      exact entry_eq_zero_of_diag_eq_zero hA j i hj
    simp [hz]
  have hsi : Real.sqrt (A i i) ≠ 0 := Real.sqrt_ne_zero'.mpr <|
    lt_of_le_of_ne hA.diag_nonneg (Ne.symm hi)
  have hsj : Real.sqrt (A j j) ≠ 0 := Real.sqrt_ne_zero'.mpr <|
    lt_of_le_of_ne hA.diag_nonneg (Ne.symm hj)
  field_simp

theorem sqrtDiagonal_sq {A : Mat m} (hA : A.PosSemidef) :
    sqrtDiagonal A * sqrtDiagonal A = Matrix.diagonal (Matrix.diag A) := by
  rw [sqrtDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt hA.diag_nonneg

theorem toEuclideanLin_mul (A B : Mat m) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B :=
  Matrix.toLpLin_mul 2 2 2 A B

theorem quad_sub (A B : Mat m) (x : E m) :
    quad (A - B) x = quad A x - quad B x := by
  simp only [quad, map_sub, LinearMap.sub_apply]
  exact inner_sub_right _ _ _

theorem quad_smul (r : ℝ) (A : Mat m) (x : E m) :
    quad (r • A) x = r * quad A x := by
  simp only [quad, map_smul, LinearMap.smul_apply]
  exact real_inner_smul_right _ _ _

theorem quad_congr (A B : Mat m) (hB : B.IsHermitian) (x : E m) :
    quad (B * A * B) x = quad A (Matrix.toEuclideanLin B x) := by
  simp only [quad, toEuclideanLin_mul, LinearMap.comp_apply]
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB _ _).symm

theorem posSemidef_iff_quad_nonneg {A : Mat m} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ x, 0 ≤ quad A x := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, LinearMap.IsPositive]
  simp only [Matrix.isSymmetric_toEuclideanLin_iff, hA, true_and, quad,
    RCLike.re_to_real]
  exact forall_congr' (fun x => by rw [real_inner_comm x])

theorem eigenvector_toEuclideanLin {A : Mat m} (hA : A.IsHermitian) (i : Fin m) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  apply PiLp.ext
  intro j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

theorem quad_eq_sum_eigenvalues {A : Mat m} (hA : A.IsHermitian) (x : E m) :
    quad A x = ∑ i, hA.eigenvalues i * (inner ℝ (hA.eigenvectorBasis i) x) ^ 2 := by
  unfold quad
  rw [← hA.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin A x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.isSymmetric_toEuclideanLin_iff.mpr hA, eigenvector_toEuclideanLin,
    real_inner_smul_left, real_inner_comm (hA.eigenvectorBasis i) x]
  ring

theorem inner_self_eq_sum_eigenbasis {A : Mat m} (hA : A.IsHermitian) (x : E m) :
    inner ℝ x x = ∑ i, (inner ℝ (hA.eigenvectorBasis i) x) ^ 2 := by
  rw [← hA.eigenvectorBasis.sum_inner_mul_inner x x]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (hA.eigenvectorBasis i) x, pow_two]

theorem low_eigen_quad_le {A : Mat m} (hA : A.IsHermitian) (κ : ℝ) (x : E m)
    (hx : ∀ i, κ < hA.eigenvalues i → inner ℝ (hA.eigenvectorBasis i) x = 0) :
    quad A x ≤ κ * inner ℝ x x := by
  rw [quad_eq_sum_eigenvalues hA, inner_self_eq_sum_eigenbasis hA, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : κ < hA.eigenvalues i
  · simp [hx i hi]
  · exact mul_le_mul_of_nonneg_right (le_of_not_gt hi) (sq_nonneg _)

theorem high_count_mul_le_trace {A : Mat m} (hA : A.PosSemidef) (κ : ℝ) :
    (Fintype.card (High hA.isHermitian κ) : ℝ) * κ ≤ A.trace := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i => κ < hA.isHermitian.eigenvalues i)
  have hc : Fintype.card (High hA.isHermitian κ) = s.card := by
    simp [High, s, Fintype.card_subtype]
  rw [hc, hA.isHermitian.trace_eq_sum_eigenvalues]
  calc
    (s.card : ℝ) * κ = ∑ _i ∈ s, κ := by simp
    _ ≤ ∑ i ∈ s, hA.isHermitian.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ ≤ ∑ i, hA.isHermitian.eigenvalues i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ => hA.eigenvalues_nonneg i)

theorem finrank_inf_ker_add {ι : Type*} [Fintype ι]
    (G : Submodule ℝ (E m)) (F : E m →ₗ[ℝ] (ι → ℝ)) :
    Module.finrank ℝ G ≤ Module.finrank ℝ (G ⊓ F.ker : Submodule ℝ (E m)) + Fintype.card ι := by
  have hr := F.finrank_range_add_finrank_ker
  have hi := G.finrank_sup_add_finrank_inf_eq F.ker
  have hs := Submodule.finrank_le (G ⊔ F.ker)
  have hf := Submodule.finrank_le F.range
  simp only [finrank_euclideanSpace, Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at *
  omega

theorem sqrtDiagonal_isHermitian (A : Mat m) : (sqrtDiagonal A).IsHermitian := by
  simp [sqrtDiagonal, Matrix.IsHermitian]

theorem quad_diag_eq {A : Mat m} (hA : A.PosSemidef) (x : E m) :
    quad (Matrix.diagonal (Matrix.diag A)) x =
      inner ℝ (Matrix.toEuclideanLin (sqrtDiagonal A) x)
        (Matrix.toEuclideanLin (sqrtDiagonal A) x) := by
  rw [← sqrtDiagonal_sq hA]
  simp only [quad, toEuclideanLin_mul, LinearMap.comp_apply]
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr (sqrtDiagonal_isHermitian A) _ _).symm

theorem quad_whiten_eq {A : Mat m} (hA : A.PosSemidef) (x : E m) :
    quad A x = quad (whiten A) (Matrix.toEuclideanLin (sqrtDiagonal A) x) := by
  calc
    quad A x = quad (sqrtDiagonal A * whiten A * sqrtDiagonal A) x :=
      congrArg (fun B => quad B x) (reconstruct_whiten hA).symm
    _ = _ := quad_congr _ _ (sqrtDiagonal_isHermitian A) x

theorem exists_good_subspace (G : Submodule ℝ (E m)) {A : Mat m}
    (hA : A.PosSemidef) {κ : ℝ} (hκ : 0 < κ) :
    ∃ W : Submodule ℝ (E m), W ≤ G ∧
      (Module.finrank ℝ G : ℝ) - (m : ℝ) / κ ≤ Module.finrank ℝ W ∧
      ∀ x ∈ W, 0 ≤ quad (κ • Matrix.diagonal (Matrix.diag A) - A) x := by
  classical
  let C := whiten A
  have hC : C.PosSemidef := whiten_posSemidef hA
  let F := (highCoordinates hC.isHermitian κ).comp
    (Matrix.toEuclideanLin (sqrtDiagonal A))
  let W := G ⊓ F.ker
  refine ⟨W, inf_le_left, ?_, ?_⟩
  · have hd := finrank_inf_ker_add G F
    have hc : (Fintype.card (High hC.isHermitian κ) : ℝ) ≤ (m : ℝ) / κ := by
      apply (le_div_iff₀ hκ).mpr
      exact (high_count_mul_le_trace hC κ).trans (whiten_trace_le hA)
    have hdr : (Module.finrank ℝ G : ℝ) ≤
        Module.finrank ℝ W + (Fintype.card (High hC.isHermitian κ) : ℝ) := by
      exact_mod_cast hd
    linarith
  · intro x hx
    have hx0 : F x = 0 := hx.2
    have hl : ∀ i, κ < hC.isHermitian.eigenvalues i →
        inner ℝ (hC.isHermitian.eigenvectorBasis i)
          (Matrix.toEuclideanLin (sqrtDiagonal A) x) = 0 := by
      intro i hi
      exact congrFun hx0 ⟨i, hi⟩
    have hq := low_eigen_quad_le hC.isHermitian κ _ hl
    rw [quad_sub, quad_smul, quad_diag_eq hA, quad_whiten_eq hA]
    exact sub_nonneg.mpr hq

theorem linearFunctional_expansion (f : Mat m →ₗ[ℝ] ℝ) (A : Mat m) :
    f A = ∑ i, ∑ j, A i j * f (Matrix.single i j 1) := by
  calc
    f A = f (∑ i, ∑ j, A i j • Matrix.single i j 1) := by
      congr 1
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
        Matrix.matrix_eq_sum_single A
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

theorem rawDualMatrix_trace (f : Mat m →ₗ[ℝ] ℝ) (A : Mat m) :
    (rawDualMatrix f * A).trace = f A := by
  rw [linearFunctional_expansion f A]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rawDualMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem dualMatrix_isHermitian (f : Mat m →ₗ[ℝ] ℝ) : (dualMatrix f).IsHermitian := by
  ext i j
  simp [dualMatrix, rawDualMatrix, add_comm, mul_add]

theorem transpose_eq_of_isHermitian {A : Mat m} (hA : A.IsHermitian) : A.transpose = A := by
  ext i j
  exact hA.apply i j

theorem dualMatrix_trace (f : Mat m →ₗ[ℝ] ℝ) {A : Mat m} (hA : A.IsHermitian) :
    (dualMatrix f * A).trace = f A := by
  have ht : ((rawDualMatrix f).transpose * A).trace = (rawDualMatrix f * A).trace := by
    rw [← Matrix.trace_transpose ((rawDualMatrix f).transpose * A), Matrix.transpose_mul,
      Matrix.transpose_transpose, transpose_eq_of_isHermitian hA, Matrix.trace_mul_comm]
  simp only [dualMatrix, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul, ht, rawDualMatrix_trace]
  ring

theorem trace_mul_vecMulVec (A : Mat m) (x : E m) :
    (A * Matrix.vecMulVec (fun i => x i) (fun i => x i)).trace = quad A x := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, quad]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rfl

theorem dualMatrix_posSemidef (f : Mat m →ₗ[ℝ] ℝ)
    (hf : ∀ A : Mat m, A.PosSemidef → 0 ≤ f A) : (dualMatrix f).PosSemidef := by
  apply (posSemidef_iff_quad_nonneg (dualMatrix_isHermitian f)).mpr
  intro x
  rw [← trace_mul_vecMulVec]
  have hp : (Matrix.vecMulVec (fun i => x i) (fun i => x i)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (fun i => x i)
  rw [dualMatrix_trace f hp.isHermitian]
  exact hf _ hp

theorem projectionMatrix_mul_self (G : Submodule ℝ (E m)) :
    projectionMatrix G * projectionMatrix G = projectionMatrix G := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul, projectionMatrix_toEuclideanLin]
  ext x i
  exact congrArg (fun y : E m => y i)
    (G.starProjection_eq_self_iff.mpr (G.starProjection_apply_mem x))

theorem trace_mul_projection_nonneg {A : Mat m} (hA : A.IsHermitian)
    (W : Submodule ℝ (E m)) (hW : ∀ x ∈ W, 0 ≤ quad A x) :
    0 ≤ (A * projectionMatrix W).trace := by
  let P := projectionMatrix W
  have hP : P.IsHermitian := (projectionMatrix_posSemidef W).isHermitian
  have hPA : (P * A * P).IsHermitian := by
    simpa only [hP.eq] using Matrix.isHermitian_conjTranspose_mul_mul P hA
  have hp : (P * A * P).PosSemidef := by
    apply (posSemidef_iff_quad_nonneg hPA).mpr
    intro x
    rw [quad_congr A P hP]
    apply hW
    rw [projectionMatrix_toEuclideanLin]
    exact W.starProjection_apply_mem x
  have ht : (P * A * P).trace = (A * P).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, projectionMatrix_mul_self,
      Matrix.trace_mul_comm]
  rw [← ht]
  exact hp.trace_nonneg

theorem exists_dual_projection (G : Submodule ℝ (E m)) {A : Mat m}
    (hA : A.PosSemidef) {κ ζ : ℝ} (hκ : 0 < κ)
    (hdim : ((1 / κ + ζ) * m) ≤ Module.finrank ℝ G) :
    ∃ P ∈ feasible G, ζ * m ≤ P.trace ∧
      0 ≤ ((κ • Matrix.diagonal (Matrix.diag A) - A) * P).trace := by
  obtain ⟨W, hWG, hd, hW⟩ := exists_good_subspace G hA hκ
  refine ⟨projectionMatrix W, projectionMatrix_mem_feasible hWG, ?_, ?_⟩
  · rw [projectionMatrix_trace]
    have he : (1 / κ + ζ) * m = (m : ℝ) / κ + ζ * m := by ring
    rw [he] at hdim
    linarith
  · apply trace_mul_projection_nonneg _ W hW
    exact (by simp [Matrix.IsHermitian, transpose_eq_of_isHermitian hA.isHermitian])

theorem slack_isHermitian {A : Mat m} (hA : A.IsHermitian) (κ : ℝ) :
    (slack κ A).IsHermitian := by
  simp [slack, Matrix.IsHermitian, transpose_eq_of_isHermitian hA]

theorem trace_slack_commutes (κ : ℝ) (A B : Mat m) :
    (A * slack κ B).trace = (slack κ A * B).trace := by
  have he : (A * Matrix.diagonal (Matrix.diag B)).trace =
      (Matrix.diagonal (Matrix.diag A) * B).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [slack, Matrix.mul_sub, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, he]

theorem convex_psd : Convex ℝ {A : Mat m | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

theorem nonneg_of_ray_lower_bound {a b c : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → c < t * a + b) : 0 ≤ a := by
  by_contra hn
  have ha : a < 0 := lt_of_not_ge hn
  have ha0 : a ≠ 0 := ne_of_lt ha
  let t := (|b - c| + 1) / (-a)
  have ht : 0 ≤ t := div_nonneg (by positivity) (neg_nonneg.mpr ha.le)
  have he : t * a = -(|b - c| + 1) := by
    dsimp [t]
    field_simp
  have hc := h t ht
  rw [he] at hc
  have hab := le_abs_self (b - c)
  linarith

theorem subspace_covariance (G : Submodule ℝ (E m)) {κ ζ : ℝ}
    (hκ : 1 < κ) (_hζ : 0 < ζ)
    (hdim : (1 / κ + ζ) * (m : ℝ) ≤ Module.finrank ℝ G) :
    ∃ Γ : Mat m, Γ.PosSemidef ∧ Supported G Γ ∧
      (∀ i, Γ i i ≤ 1) ∧ (slack κ Γ).PosSemidef ∧ ζ * m ≤ Γ.trace := by
  classical
  let b : ℝ := ζ * m
  let S := (constraintMap (m := m) κ) '' feasible G
  let T : Set (Mat m × ℝ) := {A : Mat m | A.PosSemidef} ×ˢ Set.Ici b
  by_contra hnone
  have hd : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro _ ⟨Γ, hΓ, rfl⟩ hT
    exact hnone ⟨Γ, hΓ.1, hΓ.2.1, hΓ.2.2, hT.1, hT.2⟩
  have hSc : Convex ℝ S := (convex_feasible G).linear_image (constraintMap κ)
  have hSk : IsCompact S := (isCompact_feasible G).image
    (constraintMap κ).continuous_of_finiteDimensional
  have hTc : Convex ℝ T := convex_psd.prod (convex_Ici b)
  have hTk : IsClosed T := isClosed_psd.prod isClosed_Ici
  obtain ⟨f, u, v, hS, huv, hT⟩ :=
    geometric_hahn_banach_compact_closed hSc hSk hTc hTk hd
  let g : Mat m →ₗ[ℝ] ℝ := f.toLinearMap.comp (LinearMap.inl ℝ (Mat m) ℝ)
  let a : ℝ := f (0, 1)
  have hsplit : ∀ B : Mat m, ∀ t : ℝ, f (B, t) = g B + a * t := by
    intro B t
    calc
      f (B, t) = f ((B, 0) + t • (0, 1)) := by simp
      _ = f (B, 0) + t * f (0, 1) := by rw [map_add, map_smul]; rfl
      _ = _ := by change f (B, 0) + t * f (0, 1) = f (B, 0) + f (0, 1) * t; ring
  have hg : ∀ B : Mat m, B.PosSemidef → 0 ≤ g B := by
    intro B hB
    apply nonneg_of_ray_lower_bound (b := a * b) (c := v)
    intro t ht
    have h := hT (t • B, b) ⟨hB.smul ht, by change b ≤ b; rfl⟩
    rw [hsplit, map_smul, smul_eq_mul] at h
    exact h
  have ha : 0 ≤ a := by
    apply nonneg_of_ray_lower_bound (b := a * b) (c := v)
    intro t ht
    have h := hT (0, b + t) ⟨Matrix.PosSemidef.zero, le_add_of_nonneg_right ht⟩
    rw [hsplit, map_zero, zero_add] at h
    nlinarith
  have hA : (dualMatrix g).PosSemidef := dualMatrix_posSemidef g hg
  obtain ⟨P, hP, htr, hpair⟩ := exists_dual_projection G hA (lt_trans zero_lt_one hκ) hdim
  have hgp : 0 ≤ g (slack κ P) := by
    rw [← dualMatrix_trace g (slack_isHermitian hP.1.isHermitian κ), trace_slack_commutes]
    exact hpair
  have hpS := hS (constraintMap κ P) ⟨P, hP, rfl⟩
  have hpT := hT (0, b) ⟨Matrix.PosSemidef.zero, by change b ≤ b; rfl⟩
  change f (slack κ P, P.trace) < u at hpS
  rw [hsplit] at hpS hpT
  simp only [map_zero, zero_add] at hpT
  have hmul : a * b ≤ a * P.trace := mul_le_mul_of_nonneg_left htr ha
  linarith

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Column
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {m n : ℕ}

lemma trace_mul_nonneg {Q Γ : Mat m} (hQ : Q.PosSemidef) (hΓ : Γ.PosSemidef) :
    0 ≤ (Q*Γ).trace := by
  have hS : (CFC.sqrt Γ).IsHermitian := (CFC.sqrt_nonneg Γ).posSemidef.isHermitian
  have hp := (hQ.conjTranspose_mul_mul_same (CFC.sqrt Γ)).trace_nonneg
  rw [hS.eq,Matrix.trace_mul_cycle,CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg,Matrix.trace_mul_comm] at hp
  exact hp

lemma trace_mul_diagonal_eq (Q : Mat m) (a : Fin m → ℝ) :
    (Q*Matrix.diagonal a).trace = ∑ i, Q i i*a i := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal]

lemma energy_trace_domination (Q Γ : Mat m) (hQ : Q.PosSemidef) {κ : ℝ}
    (hΓ : (κ • Matrix.diagonal (Matrix.diag Γ)-Γ).PosSemidef) :
    (Q*Γ).trace ≤ κ*(∑ i, Q i i*Γ i i) := by
  have hp := trace_mul_nonneg hQ hΓ
  rw [mul_sub,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul,
    trace_mul_diagonal_eq] at hp
  exact sub_nonneg.mp hp

attribute [local instance] OAI.CurrentKS.Covariance.columnInnerProductSpace
lemma sqrt_range_eq {Γ : Mat m} (hΓ : Γ.PosSemidef) :
    (CFC.sqrt Γ).toEuclideanLin.range = Γ.toEuclideanLin.range := by
  have hS : (CFC.sqrt Γ).IsHermitian := (CFC.sqrt_nonneg Γ).posSemidef.isHermitian
  have hr := LinearMap.range_self_comp_adjoint (CFC.sqrt Γ).toEuclideanLin
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hS.eq,← toEuclideanLin_mul,
    CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg] at hr
  exact hr.symm

lemma on_sqrt_range {Γ : Mat m} (hΓ : Γ.PosSemidef) (P : E m → Prop)
    (hP : ∀ x, P (Γ.toEuclideanLin x)) : ∀ x, P ((CFC.sqrt Γ).toEuclideanLin x) := by
  intro x
  have hr : (CFC.sqrt Γ).toEuclideanLin x ∈ Γ.toEuclideanLin.range := by
    rw [← sqrt_range_eq hΓ]
    exact ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := hr
  rw [← hy]
  exact hP y

lemma column_eq_apply_basis (A : Mat m) (j : Fin m) :
    column A j = A.toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ j) := by
  ext i
  simp [column,Matrix.toLpLin_apply,EuclideanSpace.basisFun_apply,Matrix.mulVec_single]

lemma sqrt_column_range {Γ : Mat m} (hΓ : Γ.PosSemidef) (P : E m → Prop)
    (hP : ∀ x, P (Γ.toEuclideanLin x)) (j : Fin m) : P (column (CFC.sqrt Γ) j) := by
  rw [column_eq_apply_basis]
  exact on_sqrt_range hΓ P hP _

lemma sum_column_quadratic (Q C : Mat m) :
    (∑ j, quad Q (column C j)) = (C.conjTranspose*Q*C).trace := by
  simp only [quad,column,Matrix.toLpLin_apply,EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_trivial,Matrix.mulVec,dotProduct,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma sqrt_moments {Γ : Mat m} (hΓ : Γ.PosSemidef) (Q : Mat m) :
    (∑ j, quad Q (column (CFC.sqrt Γ) j)) = (Q*Γ).trace := by
  rw [sum_column_quadratic,(CFC.sqrt_nonneg Γ).posSemidef.isHermitian.eq,
    Matrix.trace_mul_cycle,CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg,Matrix.trace_mul_comm]

lemma row_moments {Γ : Mat m} (hΓ : Γ.PosSemidef) (i : Fin m) :
    (∑ j, (column (CFC.sqrt Γ) j i)^2) = Γ i i := by
  have hS : (CFC.sqrt Γ).IsHermitian := (CFC.sqrt_nonneg Γ).posSemidef.isHermitian
  have hh := congrArg (fun A : Mat m => A i i) (CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg)
  try dsimp only at hh
  rw [Matrix.mul_apply] at hh
  have hs : ∀ j, CFC.sqrt Γ j i = CFC.sqrt Γ i j := by
    intro j
    have he := congrArg (fun A : Mat m => A i j) hS.eq
    simpa only [Matrix.conjTranspose_apply,star_trivial] using he
  simpa only [hs,column,sq] using hh

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r6ae1d0_2 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma eta_apply (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z : H d) :
    eta c A x Z = ∑ i, (c * psi (x i)) • sandwich (A i) Z := by
  simp [eta]

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Energy
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

lemma eta_rank_one (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    eta c A x Z = ∑ i, (c*psi (x i)*inner ℝ (A i) Z) • A i := by
  rw [eta_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) Z (hA i) (hrank i),smul_smul]

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Interaction
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Interaction
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.State Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma interaction_symm (c : ℝ) (A : Fin N → H d) (l : Fin N → ℝ) (X : H d) :
    (interaction c A l X).IsHermitian := by
  ext i j
  change c*l j*l i*inner ℝ (A j) (sandwich X (A i)) = c*l i*l j*inner ℝ (A i) (sandwich X (A j))
  rw [inner_sandwich,real_inner_comm (sandwich X (A j)) (A i)]
  ring

lemma interaction_nonneg {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hA : ∀ i, A i ∈ psdCone d) (l : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i) (X : H d) (i j : Fin N) :
    0 ≤ interaction c A l X i j := by
  exact mul_nonneg (mul_nonneg (mul_nonneg hc (hl i)) (hl j))
    (inner_nonneg_of_psd _ _ (hA i) (sandwich_psd _ _ (hA j)))

lemma sandwich_responseInput (A : Fin N → H d) (l F : Fin N → ℝ) (X : H d) :
    sandwich X (responseInput A l F) = ∑ i, (l i*F i) • sandwich X (A i) := by
  change sandwichCLM X (∑ i, (l i*F i) • A i) = _
  simp only [map_sum,map_smul,sandwichCLM_apply]

lemma interaction_mulVec (c : ℝ) (A : Fin N → H d) (l F : Fin N → ℝ) (X : H d) (i : Fin N) :
    (interaction c A l X *ᵥ F) i = c*l i*inner ℝ (A i) (sandwich X (responseInput A l F)) := by
  rw [sandwich_responseInput,inner_sum]
  simp only [Matrix.mulVec,dotProduct,interaction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_right (A i) (sandwich X (A j)) (l j*F j)]
  ring

lemma interaction_entry_bound {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hA : ∀ i, A i ∈ psdCone d) (l : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i)
    (X : H d) (hX : X ∈ psdCone d) (i j : Fin N) :
    interaction c A l X i j ≤ c*(l i*inner ℝ (A i) X)*(l j*inner ℝ (A j) X) := by
  have hh := mul_le_mul_of_nonneg_left (inner_sandwich_le X (A i) (A j) hX (hA i) (hA j))
    (mul_nonneg (mul_nonneg hc (hl i)) (hl j))
  change c*l i*l j*inner ℝ (A i) (sandwich X (A j)) ≤ _
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

lemma interaction_entry_square {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hA : ∀ i, A i ∈ psdCone d) (l : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i)
    (X : H d) (hX : X ∈ psdCone d) (i j : Fin N) :
    (interaction c A l X i j)^2 ≤ c*(l i*inner ℝ (A i) X)*(l j*inner ℝ (A j) X)*interaction c A l X i j := by
  have hh := mul_le_mul_of_nonneg_right (interaction_entry_bound hc A hA l hl X hX i j)
    (interaction_nonneg hc A hA l hl X i j)
  simpa only [pow_two] using hh

lemma eta_as_response (c : ℝ) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hlm : ∀ i, l i*m i = psi (x i)) (Q : H d) :
    eta c A x Q = c • responseInput A l (fun i => m i*inner ℝ (A i) Q) := by
  rw [eta_rank_one c A x Q hA hrank]
  simp only [responseInput,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hlm i]
  congr 1
  ring

lemma interaction_duality (c ε : ℝ) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hlm : ∀ i, l i*m i = psi (x i))
    (X P Q : H d) (hX : X ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q + ε • (Hermitian.one : H d)) (i : Fin N) :
    (interaction c A l X *ᵥ (fun j => m j*inner ℝ (A j) Q)) i =
      l i*inner ℝ (A i) P - ε*l i*inner ℝ (A i) (sandwich X one) := by
  have hp := congrArg (sandwichCLM X) hP
  change sandwich X (sandwich (invH X) P) = sandwichCLM X (eta c A x Q + ε • (Hermitian.one : H d)) at hp
  rw [sandwich_inverse_left X P hX,map_add,map_smul,eta_as_response c A x hA hrank l m hlm Q,
    map_smul] at hp
  change P = c • sandwich X (responseInput A l (fun j => m j*inner ℝ (A j) Q)) +
      ε • sandwich X one at hp
  rw [interaction_mulVec,hp,inner_add_right,
    real_inner_smul_right (A i) _ c,real_inner_smul_right (A i) _ ε]
  ring

end
end CurrentKS.Interaction

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EnergyMatrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Interaction
noncomputable section
open CurrentKS.Hermitian CurrentKS.State Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma energyMatrix_symm (A : Fin N → H d) (l : Fin N → ℝ) (X P : H d) :
    (energyMatrix A l X P).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,energyMatrix]
  have hh := jordanCLM_symmetric X P (A i) (A j)
  change inner ℝ (jordanCLM X P (A i)) (A j) = inner ℝ (A i) (jordanCLM X P (A j)) at hh
  rw [real_inner_comm (A j) (jordanCLM X P (A i))] at hh
  rw [hh]
  ring

lemma energyMatrix_quad (A : Fin N → H d) (l F : Fin N → ℝ) (X P : H d) :
    F ⬝ᵥ (energyMatrix A l X P *ᵥ F) =
      inner ℝ P (sandwich (responseInput A l F) X) := by
  have hh := jordanCLM_quadratic X P (responseInput A l F)
  have he : inner ℝ (responseInput A l F) (jordanCLM X P (responseInput A l F)) =
      2*(F ⬝ᵥ (energyMatrix A l X P *ᵥ F)) := by
    simp only [responseInput,map_sum,map_smul,sum_inner,inner_sum,
      energyMatrix,Matrix.mulVec,dotProduct,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_left (A j) ((l i*F i) • jordanCLM X P (A i)),
      real_inner_smul_right (A j) (jordanCLM X P (A i))]
    have hj := jordanCLM_symmetric X P (A i) (A j)
    change inner ℝ (jordanCLM X P (A i)) (A j) = inner ℝ (A i) (jordanCLM X P (A j)) at hj
    rw [real_inner_comm (A j) (jordanCLM X P (A i))] at hj
    rw [hj]
    ring
  linarith

lemma energyMatrix_psd (A : Fin N → H d) (l : Fin N → ℝ) (X P : H d)
    (hX : X ∈ psdCone d) (hP : P ∈ psdCone d) : (energyMatrix A l X P).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨energyMatrix_symm A l X P,fun F => ?_⟩
  simp only [star_trivial,energyMatrix_quad]
  exact inner_nonneg_of_psd _ _ hP (sandwich_psd _ _ hX)

lemma energyMatrix_diag (A : Fin N → H d) (l : Fin N → ℝ) (X P : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (i : Fin N) :
    energyMatrix A l X P i i = (l i*inner ℝ (A i) X)*(l i*inner ℝ (A i) P) := by
  rw [energyMatrix,jordanCLM_quadratic,sandwich_rank_one (A i) X (hA i) (hrank i),
    real_inner_smul_right P (A i),real_inner_comm P (A i)]
  ring

lemma response_energy_cancel (X C : H d) (hX : X ∈ pd d) :
    sandwich (invH X) (sandwich (sandwich X C) (invH X)) = sandwich C X := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  apply Subtype.ext
  change (X : Mat d)⁻¹*(((X : Mat d)*(C : Mat d)*(X : Mat d))*(X : Mat d)⁻¹*
    ((X : Mat d)*(C : Mat d)*(X : Mat d)))*(X : Mat d)⁻¹ = (C : Mat d)*(X : Mat d)*(C : Mat d)
  simp only [mul_assoc,Matrix.mul_nonsing_inv _ hx,mul_one]
  simp only [← mul_assoc,Matrix.nonsing_inv_mul _ hx,one_mul]

lemma proposed_energy (A : Fin N → H d) (l m F G : Fin N → ℝ) (X Y P Q : H d)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) :
    energy X Y P Q (sandwich X (responseInput A l F)) (sandwich Y (responseInput A m G)) =
      F ⬝ᵥ (energyMatrix A l X P *ᵥ F)+G ⬝ᵥ (energyMatrix A m Y Q *ᵥ G) := by
  rw [energy,response_energy_cancel X _ hX,response_energy_cancel Y _ hY,
    energyMatrix_quad,energyMatrix_quad]

end
end CurrentKS.Interaction

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_QuadGram
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance

section
open scoped BigOperators
open Matrix

variable {m : ℕ}

attribute [local instance] OAI.CurrentKS.Covariance.instInnerProductSpaceReal_solutions_1
lemma quad_gram (C : Mat m) (x : E m) :
    quad (C.conjTranspose * C) x = inner ℝ (C.toEuclideanLin x) (C.toEuclideanLin x) := by
  simp only [quad,toEuclideanLin_mul,LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _

theorem exists_singular_subspace (C : Mat m) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ G : Submodule ℝ (E m),
      (m : ℝ) - (C.conjTranspose*C).trace / ρ ≤ Module.finrank ℝ G ∧
      ∀ x ∈ G, inner ℝ (C.toEuclideanLin x) (C.toEuclideanLin x) ≤ ρ * inner ℝ x x := by
  classical
  have hC := Matrix.posSemidef_conjTranspose_mul_self C
  let F := highCoordinates hC.isHermitian ρ
  refine ⟨F.ker,?_,?_⟩
  · have hd := finrank_inf_ker_add (⊤ : Submodule ℝ (E m)) F
    have he : (⊤ : Submodule ℝ (E m)) ⊓ F.ker = F.ker := top_inf_eq _
    rw [he] at hd
    simp only [finrank_top,finrank_euclideanSpace,Fintype.card_fin] at hd
    have hcount := high_count_mul_le_trace hC ρ
    have hd' : (m : ℝ) ≤ (Module.finrank ℝ F.ker : ℝ) + Fintype.card (High hC.isHermitian ρ) := by
      exact_mod_cast hd
    have hcount' := (le_div_iff₀ hρ).mpr hcount
    linarith
  · intro x hx
    rw [← quad_gram]
    apply low_eigen_quad_le hC.isHermitian
    intro i hi
    have hh := congrFun hx (⟨i,hi⟩ : High hC.isHermitian ρ)
    exact hh

lemma gram_trace (C : Mat m) : (C.conjTranspose*C).trace = ∑ i, ∑ j, (C i j)^2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end

open scoped BigOperators
open Matrix

variable {m n : ℕ}

attribute [local instance] OAI.CurrentKS.Covariance.instInnerProductSpaceReal_solutions_2
lemma weighted_singular_subspace (C : Mat m) (W : E m ≃ₗ[ℝ] E m) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ G : Submodule ℝ (E m),
      (m : ℝ) - (C.conjTranspose*C).trace / ρ ≤ Module.finrank ℝ G ∧
      ∀ x ∈ G, inner ℝ (C.toEuclideanLin (W x)) (C.toEuclideanLin (W x)) ≤
        ρ * inner ℝ (W x) (W x) := by
  obtain ⟨G,hG,hq⟩ := exists_singular_subspace C hρ
  refine ⟨G.map W.symm.toLinearMap,?_,?_⟩
  · rw [LinearEquiv.finrank_map_eq W.symm G]
    exact hG
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using hq y hy

lemma coupled_singular_subspace (C : Mat m) (W : E m ≃ₗ[ℝ] E m)
    (L : E m →ₗ[ℝ] E n) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ G : Submodule ℝ (E m),
      (m : ℝ) - (C.conjTranspose*C).trace / ρ - n ≤ Module.finrank ℝ G ∧
      (∀ x ∈ G, L x = 0) ∧
      ∀ x ∈ G, inner ℝ (C.toEuclideanLin (W x)) (C.toEuclideanLin (W x)) ≤
        ρ * inner ℝ (W x) (W x) := by
  obtain ⟨G,hG,hq⟩ := weighted_singular_subspace C W hρ
  refine ⟨G ⊓ L.ker,?_,fun x hx => hx.2,fun x hx => hq x hx.1⟩
  have hd : Module.finrank ℝ G ≤ Module.finrank ℝ (G ⊓ L.ker : Submodule ℝ (E m)) + n := by
    have hr := L.finrank_range_add_finrank_ker
    have hi := G.finrank_sup_add_finrank_inf_eq L.ker
    have hs := Submodule.finrank_le (G ⊔ L.ker)
    have hf := Submodule.finrank_le L.range
    simp only [finrank_euclideanSpace,Fintype.card_fin] at *
    omega
  have hd' : (Module.finrank ℝ G : ℝ) ≤ Module.finrank ℝ (G ⊓ L.ker : Submodule ℝ (E m)) + n := by
    exact_mod_cast hd
  linarith

theorem coupled_covariance (C : Mat (2*n)) (W : E (2*n) ≃ₗ[ℝ] E (2*n))
    (L : E (2*n) →ₗ[ℝ] E n)
    (htr : (C.conjTranspose*C).trace ≤ (2*n : ℝ)/384) :
    ∃ Γ : Mat (2*n), Γ.PosSemidef ∧
      (∀ i, Γ i i ≤ 1) ∧ (slack 4 Γ).PosSemidef ∧
      (23/48 : ℝ)*n ≤ Γ.trace ∧
      (∀ x, L (Γ.toEuclideanLin x) = 0) ∧
      ∀ x, inner ℝ (C.toEuclideanLin (W (Γ.toEuclideanLin x)))
          (C.toEuclideanLin (W (Γ.toEuclideanLin x))) ≤
        (1/4 : ℝ)*inner ℝ (W (Γ.toEuclideanLin x)) (W (Γ.toEuclideanLin x)) := by
  obtain ⟨G,hG,hL,hq⟩ := coupled_singular_subspace C W L (by norm_num : (0 : ℝ) < 1/4)
  have hd : (1/(4 : ℝ)+23/96)*(2*n : ℝ) ≤ Module.finrank ℝ G := by
    push_cast at hG
    linarith
  obtain ⟨Γ,hΓ,hsupp,hdiag,hslack,ht⟩ := subspace_covariance G
    (by norm_num : (1 : ℝ) < 4) (by norm_num : (0 : ℝ) < 23/96) (by simpa using hd)
  refine ⟨Γ,hΓ,hdiag,hslack,?_,fun x => hL _ (hsupp x),fun x => hq _ (hsupp x)⟩
  push_cast at ht
  linarith

end CurrentKS.Covariance

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_WhitenWeighted
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix
open scoped BigOperators

variable {n : ℕ}

lemma whiten_entry_bound {c ai aj bi wi zj t : ℝ} (hc : 0 < c)
    (haj : 0 < aj) (hbi : 0 ≤ bi) (hwi : 0 ≤ wi) (hzj : 0 < zj)
    (ht : 0 ≤ t) (hab : ai*bi ≤ c⁻¹^2) (htsq : t^2 ≤ c*ai*aj*t) :
    (bi*wi)*t^2/(aj*zj) ≤ (wi*t)/(c*zj) := by
  have hc0 := ne_of_gt hc
  have hcoef : c*ai*bi ≤ c⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hab hc.le
    calc
      _ = c*(ai*bi) := by ring
      _ ≤ c*c⁻¹^2 := h
      _ = c⁻¹ := by field_simp
  calc
    _ ≤ (bi*wi)*(c*ai*aj*t)/(aj*zj) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htsq (mul_nonneg hbi hwi))
        (mul_pos haj hzj).le
    _ = (c*ai*bi)*(wi*t)/zj := by field_simp
    _ ≤ c⁻¹*(wi*t)/zj :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (mul_nonneg hwi ht)) hzj.le
    _ = (wi*t)/(c*zj) := by ring

theorem weighted_frobenius_bound {c : ℝ} (hc : 0 < c)
    (a b z w : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i)
    (hz : ∀ i, 0 < z i) (hw : ∀ i, 0 ≤ w i)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (hm : ∀ i j, 0 ≤ M i j)
    (hab : ∀ i, a i*b i ≤ c⁻¹^2)
    (hsq : ∀ i j, (M i j)^2 ≤ c*a i*a j*M i j)
    (hdual : ∀ i, (M *ᵥ w) i ≤ z i) :
    (∑ i, ∑ j, (b i*w i)*(M i j)^2/(a j*z j)) ≤ (n : ℝ)/c := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : Fin n, (1/c : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ i : Fin n, (w i*M i j)/(c*z j) := by
          apply Finset.sum_le_sum
          intro i _
          exact whiten_entry_bound hc (ha j) (hb i) (hw i) (hz j) (hm i j) (hab i) (hsq i j)
        _ = (M *ᵥ w) j/(c*z j) := by
          rw [← Finset.sum_div]
          congr 1
          unfold Matrix.mulVec dotProduct
          apply Finset.sum_congr rfl
          intro i _
          have he : M i j = M j i := by simpa using (hM.apply i j).symm
          rw [he,mul_comm]
        _ ≤ z j/(c*z j) := div_le_div_of_nonneg_right (hdual j) (mul_pos hc (hz j)).le
        _ = 1/c := by field_simp [ne_of_gt (hz j)]
    _ = _ := by simp [div_eq_mul_inv]

lemma whitenWeighted_sq (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (whitenWeighted a b M i j)^2 = b i*(M i j)^2/a j := by
  simp only [whitenWeighted,div_pow,mul_pow,Real.sq_sqrt (hb i),Real.sq_sqrt (ha j)]

lemma gram_trace_sum_squares (M : Matrix (Fin n) (Fin n) ℝ) :
    (M.conjTranspose*M).trace = ∑ i, ∑ j, (M i j)^2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma whitenWeighted_trace (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ((whitenWeighted a b M).conjTranspose * whitenWeighted a b M).trace =
      ∑ i, ∑ j, b i*(M i j)^2/a j := by
  rw [gram_trace_sum_squares]
  simp only [whitenWeighted_sq a b ha hb]

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairIndex
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance

section
open Matrix WithLp
open scoped BigOperators

variable {n m : ℕ}

lemma offBlock_gram_trace (A B : Mat n) :
    ((offBlock A B).conjTranspose*offBlock A B).trace =
      (A.conjTranspose*A).trace+(B.conjTranspose*B).trace := by
  rw [gram_trace,gram_trace,gram_trace]
  simp only [offBlock,Matrix.reindex_apply,Matrix.submatrix_apply]
  have hm (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
      (∑ i : Fin (2*n), ∑ j : Fin (2*n), (D ((pairIndex n).symm i) ((pairIndex n).symm j))^2) =
        ∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n, (D i j)^2 := by
    calc
      _ = ∑ i : Fin (2*n), ∑ j : Fin n ⊕ Fin n, (D ((pairIndex n).symm i) j)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact (pairIndex n).symm.sum_comp (fun j : Fin n ⊕ Fin n => (D ((pairIndex n).symm i) j)^2)
      _ = _ := (pairIndex n).symm.sum_comp (fun i : Fin n ⊕ Fin n => ∑ j : Fin n ⊕ Fin n, (D i j)^2)
  rw [hm]
  simp only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero,zero_add,add_zero]
  ac_rfl

lemma weightEquiv_apply (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (x : E m) (i : Fin m) :
    weightEquiv a ha x i = Real.sqrt (a i)*x i := by rfl

lemma whiten_mul_weight (a b : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (M : Mat m) (x : E m) :
    (whitenWeighted a b M).toEuclideanLin (weightEquiv a ha x) =
      weightEquiv b hb (M.toEuclideanLin x) := by
  ext i
  change (∑ j, whitenWeighted a b M i j * (weightEquiv a ha x) j) =
    Real.sqrt (b i)*(∑ j, M i j*x j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [whitenWeighted,weightEquiv_apply]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (ha j))]

lemma combined_weighted_response {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (W : V →L[ℝ] V) (M : V →L[ℝ] V) (x y : V)
    (he : x = y+M x) (hc : ‖W (M x)‖^2 ≤ (1/4 : ℝ)*‖W x‖^2) :
    ‖W x‖^2 ≤ 4*‖W y‖^2 := by
  have hq : ‖W (M x)‖ ≤ ‖W x‖/2 := by
    nlinarith [norm_nonneg (W x),norm_nonneg (W (M x))]
  have ht : ‖W x‖ ≤ ‖W y‖+‖W (M x)‖ := by
    calc
      _ = ‖W y+W (M x)‖ := by rw [← map_add,← he]
      _ ≤ _ := norm_add_le _ _
  have hnorm : ‖W x‖ ≤ 2*‖W y‖ := by linarith
  nlinarith [norm_nonneg (W x),norm_nonneg (W y)]

end

open Matrix WithLp
open scoped BigOperators

variable {n : ℕ}

lemma whiten_offBlock (a b : Fin n → ℝ) (A B : Mat n) :
    whitenWeighted (pairWeight a b) (pairWeight a b) (offBlock A B) =
      offBlock (whitenWeighted a b A) (whitenWeighted b a B) := by
  ext i j
  simp only [whitenWeighted,offBlock,Matrix.reindex_apply,Matrix.submatrix_apply,pairWeight,
    Function.comp_apply]
  cases (pairIndex n).symm i <;> cases (pairIndex n).symm j <;>
    simp only [Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply,mul_zero,zero_div] <;> rfl

lemma whiten_offBlock_gram (a b : Fin n → ℝ) (A B : Mat n)
    (hA : ((whitenWeighted a b A).conjTranspose*whitenWeighted a b A).trace ≤ (n : ℝ)/384)
    (hB : ((whitenWeighted b a B).conjTranspose*whitenWeighted b a B).trace ≤ (n : ℝ)/384) :
    let C := whitenWeighted (pairWeight a b) (pairWeight a b) (offBlock A B)
    (C.conjTranspose*C).trace ≤ (2*n : ℝ)/384 := by
  dsimp only
  rw [whiten_offBlock,offBlock_gram_trace]
  linarith

attribute [local instance] OAI.CurrentKS.Covariance.instInnerProductSpaceReal_solutions_3
theorem weighted_block_covariance (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A B : Mat n) (L : E (2*n) →ₗ[ℝ] E n)
    (hA : ((whitenWeighted a b A).conjTranspose*whitenWeighted a b A).trace ≤ (n : ℝ)/384)
    (hB : ((whitenWeighted b a B).conjTranspose*whitenWeighted b a B).trace ≤ (n : ℝ)/384) :
    ∃ Γ : Mat (2*n), Γ.PosSemidef ∧
      (∀ i, Γ i i ≤ 1) ∧ (slack 4 Γ).PosSemidef ∧ (23/48 : ℝ)*n ≤ Γ.trace ∧
      (∀ x, L (Γ.toEuclideanLin x) = 0) ∧
      ∀ x, ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb)
        ((offBlock A B).toEuclideanLin (Γ.toEuclideanLin x))‖^2 ≤
        (1/4 : ℝ)*‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) (Γ.toEuclideanLin x)‖^2 := by
  let D := pairWeight a b
  have hD := pairWeight_pos a b ha hb
  obtain ⟨Γ,hΓ,hd,hs,ht,hL,hq⟩ := coupled_covariance
    (whitenWeighted D D (offBlock A B)) (weightEquiv D hD) L (whiten_offBlock_gram a b A B hA hB)
  refine ⟨Γ,hΓ,hd,hs,ht,hL,?_⟩
  intro x
  have hh := hq x
  rw [whiten_mul_weight D D hD hD] at hh
  simpa only [real_inner_self_eq_norm_sq] using hh

end CurrentKS.Covariance

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairVec
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

variable {n : ℕ}

lemma pairVec_left (F G : E n) (i : Fin n) : pairVec F G (pairIndex n (.inl i)) = F i := by
  simp [pairVec]
lemma pairVec_right (F G : E n) (i : Fin n) : pairVec F G (pairIndex n (.inr i)) = G i := by
  simp [pairVec]

lemma sum_pair (f : Fin (2*n) → ℝ) :
    (∑ i, f i) = (∑ i, f (pairIndex n (.inl i)))+(∑ i, f (pairIndex n (.inr i))) := by
  rw [← (pairIndex n).sum_comp f,Fintype.sum_sum_type]

lemma offBlock_apply_left (A B : Mat n) (v : E (2*n)) (i : Fin n) :
    ((offBlock A B).toEuclideanLin v) (pairIndex n (.inl i)) = B.toEuclideanLin (sndVec v) i := by
  change (∑ j,offBlock A B (pairIndex n (.inl i)) j*v j) = _
  rw [sum_pair]
  simp only [offBlock,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,zero_mul,
    Finset.sum_const_zero,zero_add]
  rfl

lemma offBlock_apply_right (A B : Mat n) (v : E (2*n)) (i : Fin n) :
    ((offBlock A B).toEuclideanLin v) (pairIndex n (.inr i)) = A.toEuclideanLin (fstVec v) i := by
  change (∑ j,offBlock A B (pairIndex n (.inr i)) j*v j) = _
  rw [sum_pair]
  simp only [offBlock,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_mul,
    Finset.sum_const_zero,add_zero]
  rfl

lemma response_decomposition (A B : Mat n) (v : E (2*n)) (hv : constraintLin A B v = 0) :
    v = pairVec (responseLin B v) (-responseLin B v)+(offBlock A B).toEuclideanLin v := by
  have he : fstVec v-B.toEuclideanLin (sndVec v) = A.toEuclideanLin (fstVec v)-sndVec v := by
    exact sub_eq_zero.mp hv
  ext i
  obtain ⟨i,rfl⟩ := (pairIndex n).surjective i
  cases i with
  | inl i =>
    simp only [WithLp.ofLp_add,Pi.add_apply,pairVec_left,offBlock_apply_left]
    change fstVec v i = (fstVec v i-B.toEuclideanLin (sndVec v) i)+B.toEuclideanLin (sndVec v) i
    ring
  | inr i =>
    simp only [WithLp.ofLp_add,Pi.add_apply,pairVec_right,offBlock_apply_right]
    rw [show responseLin B v = A.toEuclideanLin (fstVec v)-sndVec v from he]
    change sndVec v i = -(A.toEuclideanLin (fstVec v) i-sndVec v i)+A.toEuclideanLin (fstVec v) i
    ring

lemma weight_norm_sq (a : Fin (2*n) → ℝ) (ha : ∀ i, 0 < a i) (v : E (2*n)) :
    ‖weightEquiv a ha v‖^2 = ∑ i,a i*(v i)^2 := by
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,weightEquiv_apply,mul_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.sq_sqrt (ha i).le]

lemma pair_weighted_energy (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (H : E n) :
    ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) (pairVec H (-H))‖^2 =
      ∑ i,(a i+b i)*(H i)^2 := by
  rw [weight_norm_sq,sum_pair,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pairWeight,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,pairVec_left,pairVec_right,
    WithLp.ofLp_neg,Pi.neg_apply,neg_sq]
  ring

attribute [local instance] OAI.CurrentKS.Covariance.instInnerProductSpaceReal_solutions_4
lemma weighted_response_bound (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A B : Mat n) (v : E (2*n)) (hv : constraintLin A B v = 0)
    (hc : ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) ((offBlock A B).toEuclideanLin v)‖^2 ≤
      (1/4 : ℝ)*‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) v‖^2) :
    ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) v‖^2 ≤
      4*(∑ i,(a i+b i)*(responseLin B v i)^2) := by
  let : ContinuousSMul ℝ (E (2*n)) := IsBoundedSMul.continuousSMul
  let W := (weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb)).toLinearMap.toContinuousLinearMap
  have hh := combined_weighted_response W (offBlock A B).toEuclideanLin.toContinuousLinearMap v
    (pairVec (responseLin B v) (-responseLin B v)) (response_decomposition A B v hv) hc
  change ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) v‖^2 ≤
    4*‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb)
      (pairVec (responseLin B v) (-responseLin B v))‖^2 at hh
  rw [pair_weighted_energy a b ha hb] at hh
  exact hh

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_RowSquareSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance

section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {m n : ℕ}

lemma diagonal_bound_to_scalar {Γ : Mat m} (hΓ : Γ.PosSemidef)
    (hd : ∀ i, Γ i i ≤ 1) {κ : ℝ} (hκ : 0 ≤ κ) (hs : (slack κ Γ).PosSemidef) :
    (κ • (1 : Mat m)-Γ).PosSemidef := by
  have hh : (1-Matrix.diagonal (Matrix.diag Γ) : Mat m).PosSemidef := by
    rw [← Matrix.diagonal_one,Matrix.diagonal_sub,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (hd i)
  have hp := (hh.smul hκ).add hs
  refine ⟨(Matrix.isHermitian_one.smul (IsSelfAdjoint.of_nonneg hκ)).sub hΓ.isHermitian, ?_⟩
  have decomposition : κ • (1 : Mat m)-Γ =
      κ • (1-Matrix.diagonal (Matrix.diag Γ)) + slack κ Γ := by
    unfold slack
    module
  rw [decomposition]
  exact hp.2

end

open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

lemma weighted_column_moments (D : Fin (2*n) → ℝ) (hD : ∀ i, 0 < D i) {Γ : Mat (2*n)}
    (hΓ : Γ.PosSemidef) :
    (∑ j, ‖weightEquiv D hD (column (CFC.sqrt Γ) j)‖^2) = ∑ i,D i*Γ i i := by
  simp_rw [weight_norm_sq]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,row_moments hΓ]

lemma weighted_energy_moments (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (B : Mat n) (Q Γ : Mat (2*n)) (hQ : Q.PosSemidef) (hΓ : Γ.PosSemidef)
    (hdiag : ∀ i, Q i i = pairWeight a b i)
    (hslack : (slack 4 Γ).PosSemidef)
    (hrange : ∀ x, ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) (Γ.toEuclideanLin x)‖^2 ≤
      4*(∑ i,(a i+b i)*(responseLin B (Γ.toEuclideanLin x) i)^2)) :
    (∑ j, quad Q (column (CFC.sqrt Γ) j)) ≤
      16*(∑ i,(a i+b i)*(∑ j,(responseLin B (column (CFC.sqrt Γ) j) i)^2)) := by
  rw [sqrt_moments hΓ]
  have hd := energy_trace_domination Q Γ hQ hslack
  simp only [hdiag] at hd
  rw [← weighted_column_moments (pairWeight a b) (pairWeight_pos a b ha hb) hΓ] at hd
  have hw : (∑ j, ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) (column (CFC.sqrt Γ) j)‖^2) ≤
      ∑ j,4*(∑ i,(a i+b i)*(responseLin B (column (CFC.sqrt Γ) j) i)^2) := by
    apply Finset.sum_le_sum
    intro j _
    exact sqrt_column_range hΓ (fun v => ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) v‖^2 ≤
      4*(∑ i,(a i+b i)*(responseLin B v i)^2)) hrange j
  have he : (∑ j,4*(∑ i,(a i+b i)*(responseLin B (column (CFC.sqrt Γ) j) i)^2)) =
      4*(∑ i,(a i+b i)*(∑ j,(responseLin B (column (CFC.sqrt Γ) j) i)^2)) := by
    rw [← Finset.mul_sum,Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [he] at hw
  linarith

theorem weighted_block_ensemble (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A B : Mat n) (Q : Mat (2*n)) (hQ : Q.PosSemidef) (hdiag : ∀ i, Q i i = pairWeight a b i)
    (hA : ((whitenWeighted a b A).conjTranspose*whitenWeighted a b A).trace ≤ (n : ℝ)/384)
    (hB : ((whitenWeighted b a B).conjTranspose*whitenWeighted b a B).trace ≤ (n : ℝ)/384) :
    ∃ Γ : Mat (2*n), Γ.PosSemidef ∧ (∀ i, Γ i i ≤ 1) ∧
      ((4 : ℝ) • (1 : Mat (2*n))-Γ).PosSemidef ∧ (23/48 : ℝ)*n ≤ Γ.trace ∧
      (∀ j, constraintLin A B (column (CFC.sqrt Γ) j) = 0) ∧
      (∑ j, quad Q (column (CFC.sqrt Γ) j)) ≤
        16*(∑ i,(a i+b i)*(∑ j,(responseLin B (column (CFC.sqrt Γ) j) i)^2)) := by
  obtain ⟨Γ,hΓ,hd,hs,ht,hL,hc⟩ := weighted_block_covariance a b ha hb A B (constraintLin A B) hA hB
  refine ⟨Γ,hΓ,hd,diagonal_bound_to_scalar hΓ hd (by norm_num) hs,ht,?_,?_⟩
  · intro j
    exact sqrt_column_range hΓ (fun v => constraintLin A B v = 0) hL j
  · exact weighted_energy_moments a b ha hb B Q Γ hQ hΓ hdiag hs
      (fun x => weighted_response_bound a b ha hb A B _ (hL x) (hc x))

end CurrentKS.Covariance

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_DiagBlock
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance
open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

variable {n : ℕ}

lemma diagBlock_symm {A B : Mat n} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (diagBlock A B).IsHermitian := by
  exact (Matrix.IsHermitian.fromBlocks hA (by simp) hB).submatrix _

lemma diagBlock_apply_left (A B : Mat n) (v : E (2*n)) (i : Fin n) :
    ((diagBlock A B).toEuclideanLin v) (pairIndex n (.inl i)) = A.toEuclideanLin (fstVec v) i := by
  change (∑ j,diagBlock A B (pairIndex n (.inl i)) j*v j) = _
  rw [sum_pair]
  simp only [diagBlock,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,zero_mul,
    Finset.sum_const_zero,add_zero]
  rfl

lemma diagBlock_apply_right (A B : Mat n) (v : E (2*n)) (i : Fin n) :
    ((diagBlock A B).toEuclideanLin v) (pairIndex n (.inr i)) = B.toEuclideanLin (sndVec v) i := by
  change (∑ j,diagBlock A B (pairIndex n (.inr i)) j*v j) = _
  rw [sum_pair]
  simp only [diagBlock,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_mul,
    Finset.sum_const_zero,zero_add]
  rfl

lemma quad_diagBlock (A B : Mat n) (v : E (2*n)) :
    quad (diagBlock A B) v = quad A (fstVec v)+quad B (sndVec v) := by
  simp only [quad,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
  rw [sum_pair]
  simp only [diagBlock_apply_left,diagBlock_apply_right]
  rfl

lemma diagBlock_psd {A B : Mat n} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (diagBlock A B).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr (diagBlock_symm hA.1 hB.1),?_⟩
  intro v
  change 0 ≤ inner ℝ ((diagBlock A B).toEuclideanLin v) v
  rw [real_inner_comm v ((diagBlock A B).toEuclideanLin v)]
  change 0 ≤ quad (diagBlock A B) v
  rw [quad_diagBlock]
  apply add_nonneg
  · have hh := (Matrix.isPositive_toEuclideanLin_iff.mpr hA).2 (fstVec v)
    change 0 ≤ inner ℝ (A.toEuclideanLin (fstVec v)) (fstVec v) at hh
    simpa only [quad,real_inner_comm] using hh
  · have hh := (Matrix.isPositive_toEuclideanLin_iff.mpr hB).2 (sndVec v)
    change 0 ≤ inner ℝ (B.toEuclideanLin (sndVec v)) (sndVec v) at hh
    simpa only [quad,real_inner_comm] using hh

lemma diagBlock_diag (A B : Mat n) (i : Fin (2*n)) :
    diagBlock A B i i = pairWeight (fun j => A j j) (fun j => B j j) i := by
  obtain ⟨i,rfl⟩ := (pairIndex n).surjective i
  cases i <;> simp [diagBlock,pairWeight]

end CurrentKS.Covariance

namespace CurrentKS.Interaction
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Covariance Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma coordinate_pos [NeZero d] (A X : H d) (hA : A ∈ psdCone d) (hA0 : A ≠ 0) (hX : X ∈ pd d) :
    0 < inner ℝ A X := by
  have hh := inner_nonneg_of_psd A X hA hX.posSemidef
  apply lt_of_le_of_ne hh
  intro he
  apply hA0
  apply eq_zero_of_inner_pd hX hA
  simpa only [real_inner_comm] using he.symm

lemma interaction_duality_le {c ε : ℝ} (hε : 0 ≤ ε) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i) (hlm : ∀ i, l i*m i = psi (x i))
    (X P Q : H d) (hX : X ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q+ε • (Hermitian.one : H d)) (i : Fin N) :
    (interaction c A l X *ᵥ (fun j => m j*inner ℝ (A j) Q)) i ≤ l i*inner ℝ (A i) P := by
  rw [interaction_duality c ε A x hA hrank l m hlm X P Q hX hP i]
  exact sub_le_self _ (mul_nonneg (mul_nonneg hε (hl i))
    (inner_nonneg_of_psd _ _ (hA i) (sandwich_psd _ _ one_mem_psdCone)))

lemma interaction_whiten_trace [NeZero d] {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hA : ∀ i, A i ∈ psdCone d)
    (hA0 : ∀ i, A i ≠ 0) (hrank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hl : ∀ i, 0 < l i) (hm : ∀ i, 0 < m i)
    (hlm : ∀ i, l i*m i = psi (x i))
    (X Y P Q : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d) (hPpos : P ∈ pd d) (hQpos : Q ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q+ε • (Hermitian.one : H d))
    (hab : ∀ i, (l i*inner ℝ (A i) X)*(m i*inner ℝ (A i) Y) ≤ c⁻¹^2) :
    let a := fun i => (l i*inner ℝ (A i) X)*(l i*inner ℝ (A i) P)
    let b := fun i => (m i*inner ℝ (A i) Y)*(m i*inner ℝ (A i) Q)
    ((whitenWeighted a b (interaction c A l X)).conjTranspose *
      whitenWeighted a b (interaction c A l X)).trace ≤ (N : ℝ)/c := by
  dsimp only
  have hxp i := coordinate_pos (A i) X (hA i) (hA0 i) hX
  have hyp i := coordinate_pos (A i) Y (hA i) (hA0 i) hY
  have hpp i := coordinate_pos (A i) P (hA i) (hA0 i) hPpos
  have hqp i := coordinate_pos (A i) Q (hA i) (hA0 i) hQpos
  rw [whitenWeighted_trace _ _ (fun i => (mul_pos (mul_pos (hl i) (hxp i)) (mul_pos (hl i) (hpp i))).le)
    (fun i => (mul_pos (mul_pos (hm i) (hyp i)) (mul_pos (hm i) (hqp i))).le)]
  exact weighted_frobenius_bound hc _ _ _ _ (fun i => mul_pos (hl i) (hxp i))
    (fun i => (mul_pos (hm i) (hyp i)).le) (fun i => mul_pos (hl i) (hpp i))
    (fun i => (mul_pos (hm i) (hqp i)).le) _ (interaction_symm c A l X)
    (interaction_nonneg hc.le A hA l (fun i => (hl i).le) X) hab
    (interaction_entry_square hc.le A hA l (fun i => (hl i).le) X hX.posSemidef)
    (interaction_duality_le hε A x hA hrank l m (fun i => (hl i).le) hlm X P Q hX hP)

theorem state_energy_ensemble_oai [NeZero d] {c ε : ℝ} (hc : 384 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hA : ∀ i, A i ∈ psdCone d)
    (hA0 : ∀ i, A i ≠ 0) (hrank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hl : ∀ i, 0 < l i) (hm : ∀ i, 0 < m i)
    (hlm : ∀ i, l i*m i = psi (x i))
    (X Y P Q : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d) (hPpos : P ∈ pd d) (hQpos : Q ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q+ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P+ε • (Hermitian.one : H d))
    (hab : ∀ i, (l i*inner ℝ (A i) X)*(m i*inner ℝ (A i) Y) ≤ c⁻¹^2) :
    let IA := interaction c A l X
    let IB := interaction c A m Y
    ∃ Γ : Covariance.Mat (2*N), Γ.PosSemidef ∧ (∀ i, Γ i i ≤ 1) ∧
      ((4 : ℝ) • (1 : Covariance.Mat (2*N))-Γ).PosSemidef ∧ (23/48 : ℝ)*N ≤ Γ.trace ∧
      (∀ j, constraintLin IA IB (column (CFC.sqrt Γ) j) = 0) ∧
      (∑ j, energy X Y P Q
        (sandwich X (responseInput A l (fstVec (column (CFC.sqrt Γ) j))))
        (sandwich Y (responseInput A m (sndVec (column (CFC.sqrt Γ) j))))) ≤
      16*(∑ i, ((l i*inner ℝ (A i) X)*(l i*inner ℝ (A i) P)+
          (m i*inner ℝ (A i) Y)*(m i*inner ℝ (A i) Q))*
        (∑ j, (responseLin IB (column (CFC.sqrt Γ) j) i)^2)) := by
  dsimp only
  let a := fun i => (l i*inner ℝ (A i) X)*(l i*inner ℝ (A i) P)
  let b := fun i => (m i*inner ℝ (A i) Y)*(m i*inner ℝ (A i) Q)
  have ha : ∀ i, 0 < a i := fun i => mul_pos
    (mul_pos (hl i) (coordinate_pos (A i) X (hA i) (hA0 i) hX))
    (mul_pos (hl i) (coordinate_pos (A i) P (hA i) (hA0 i) hPpos))
  have hb : ∀ i, 0 < b i := fun i => mul_pos
    (mul_pos (hm i) (coordinate_pos (A i) Y (hA i) (hA0 i) hY))
    (mul_pos (hm i) (coordinate_pos (A i) Q (hA i) (hA0 i) hQpos))
  have h384 : (N : ℝ)/c ≤ (N : ℝ)/384 := div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by norm_num) hc
  have hc0 : 0 < c := by linarith
  have hWA := (interaction_whiten_trace hc0 hε A x hA hA0 hrank l m hl hm hlm
    X Y P Q hX hY hPpos hQpos hP hab).trans h384
  have hm' : ∀ i, m i*l i = psi (x i) := fun i => by rw [mul_comm,hlm i]
  have hab' : ∀ i, (m i*inner ℝ (A i) Y)*(l i*inner ℝ (A i) X) ≤ c⁻¹^2 := fun i => by
    rw [mul_comm]; exact hab i
  have hWB := (interaction_whiten_trace hc0 hε A x hA hA0 hrank m l hm hl hm'
    Y X Q P hY hX hQpos hPpos hQ hab').trans h384
  let EM := diagBlock (energyMatrix A l X P) (energyMatrix A m Y Q)
  have hEM : EM.PosSemidef := diagBlock_psd (energyMatrix_psd A l X P hX.posSemidef hPpos.posSemidef)
    (energyMatrix_psd A m Y Q hY.posSemidef hQpos.posSemidef)
  have hdiag : ∀ i, EM i i = pairWeight a b i := by
    intro i
    dsimp only [EM]
    rw [diagBlock_diag]
    congr 1 <;> funext j <;> exact energyMatrix_diag A _ _ _ hA hrank j
  obtain ⟨Γ,hΓ,hd,hs,ht,hcouple,he⟩ := weighted_block_ensemble a b ha hb
    (interaction c A l X) (interaction c A m Y) EM hEM hdiag hWA hWB
  refine ⟨Γ,hΓ,hd,hs,ht,hcouple,?_⟩
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j _
  rw [proposed_energy A l m _ _ X Y P Q hX hY,quad_diagBlock]
  simp only [quad,EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  congr 1 <;> exact dotProduct_comm _ _

end CurrentKS.Interaction

end

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.Interaction.state_energy_ensemble_oai := @OAI.CurrentKS.Interaction.state_energy_ensemble_oai
