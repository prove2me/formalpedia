-- Prove2me | solution 1 for OAI.CurrentKS.Variational.contDiffAt_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:41.606467+00:00
-- url     : https://prove2.me/submissions/0fb1bc91-c9e6-4c88-bff4-2367e7efd16f

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_Variational_exists_smooth_kkt_branch
import Theorems.Thm_OAI_CurrentKS_Variational_kkt

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

theorem posDef_mem_interior [NeZero d] (A : H d) (hA : (A : Mat d).PosDef) :
    A ∈ interior (psdCone d : Set (H d)) := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨r, hr, hrA⟩ := (CFC.exists_pos_algebraMap_le_iff (a := (A : Mat d)) hA.isHermitian).mpr
    ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (A : Mat d)).mp hA.isStrictlyPositive)
  have hc : Continuous (fun B : H d => (B : Mat d) - (A : Mat d)) :=
    continuous_subtype_val.sub continuous_const
  have hn : Continuous (fun B : H d => ‖(B : Mat d) - (A : Mat d)‖) :=
    continuous_norm.comp hc
  have ho : IsOpen {B : H d | ‖(B : Mat d) - (A : Mat d)‖ < r} :=
    isOpen_lt hn continuous_const
  have hs : {B : H d | ‖(B : Mat d) - (A : Mat d)‖ < r} ⊆ (psdCone d : Set (H d)) := by
    intro B hB
    have hnorm : ‖(A : Mat d) - (B : Mat d)‖ < r := by
      rwa [norm_sub_rev]
    have hle : (A : Mat d) - (B : Mat d) ≤ (algebraMap ℝ (Mat d)) r :=
      (A.property.sub B.property).isSelfAdjoint.le_algebraMap_norm_self.trans
        (by
          change ((algebraMap ℝ (Mat d)) r - (algebraMap ℝ (Mat d)) ‖(A : Mat d) - (B : Mat d)‖).PosSemidef
          have hp := (Matrix.PosSemidef.one (n := Fin d) (R := ℂ)).smul
            (a := ((r - ‖(A : Mat d) - (B : Mat d)‖ : ℝ) : ℂ))
            (by exact_mod_cast sub_nonneg.mpr hnorm.le)
          convert hp using 1
          all_goals try with_reducible_and_instances rfl
          ext i j
          simp only [Algebra.algebraMap_eq_smul_one, Matrix.sub_apply,
            Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub]
          simp only [Complex.real_smul]
          ring)
    have hh := hle.trans hrA
    exact (show 0 ≤ (B : Mat d) by simpa using hh).posSemidef
  apply interior_maximal hs ho
  simpa using hr

end OperatorNorm

open scoped Matrix.Norms.Frobenius

lemma inner_smul_leftH (A B : H d) (r : ℝ) :
    inner ℝ (r • A) B = r * inner ℝ A B := by
  exact real_inner_smul_left A B r

lemma inner_smul_rightH (A B : H d) (r : ℝ) :
    inner ℝ A (r • B) = r * inner ℝ A B := by
  exact real_inner_smul_right A B r

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

theorem rankOne_mem_psdCone (v : Fin d → ℂ) : rankOne v ∈ psdCone d :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem inner_rankOne (A : H d) (v : Fin d → ℂ) :
    inner ℝ A (rankOne v) = (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re := by
  rw [inner_eq_trace]
  change ((A : Mat d) * Matrix.vecMulVec v (star v)).trace.re = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem psd_of_inner_nonneg (A : H d)
    (h : ∀ B ∈ psdCone d, 0 ≤ inner ℝ A B) : A ∈ psdCone d := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨A.property, fun v => ?_⟩
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [inner_rankOne] using h (rankOne v) (rankOne_mem_psdCone v)
  · exact (A.property.im_star_dotProduct_mulVec_self v).symm

theorem isClosed_psdCone : IsClosed (psdCone d : Set (H d)) := by
  have he : (psdCone d : Set (H d)) =
      {A : H d | ∀ v : Fin d → ℂ, 0 ≤ (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re} := by
    ext A
    constructor
    · intro hA v
      exact hA.re_dotProduct_nonneg v
    · intro hA
      apply psd_of_inner_nonneg A

      have hp : (A : Mat d).PosSemidef :=
        Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨A.property, fun v =>
          Complex.nonneg_iff.mpr ⟨hA v, (A.property.im_star_dotProduct_mulVec_self v).symm⟩⟩
      exact fun B hB => inner_nonneg_of_psd A B hp hB
  rw [he]
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_le continuous_const
  exact Complex.continuous_re.comp (continuous_const.dotProduct
    (continuous_subtype_val.matrix_mulVec continuous_const))

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

lemma scalar_posDef {a : ℝ} (ha : 0 < a) : ((a : ℂ) • (1 : Mat d)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast ha)

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

lemma isOpen_pd [NeZero d] : IsOpen (pd d) := by
  let : CStarAlgebra (Mat d) := {}
  have he : pd d = interior (psdCone d : Set (H d)) ∩
      {A : H d | IsUnit (A : Mat d)} := by
    ext A
    constructor
    · intro hA
      exact ⟨posDef_mem_interior A hA, hA.isUnit⟩
    · rintro ⟨hA, hu⟩
      exact (interior_subset hA).posDef_iff_isUnit.mpr hu
  rw [he]
  exact isOpen_interior.inter (Units.isOpen.preimage continuous_subtype_val)

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

lemma inner_right_one (A : H d) : inner ℝ A (one : H d) = realTrace A := by
  rw [real_inner_comm, inner_one]

lemma sandwich_inverse_cancel (X P : H d) (hX : X ∈ pd d) :
    sandwich X (sandwich (invH X) P) = P := by
  apply Subtype.ext
  let : Invertible (X : Mat d) := hX.isUnit.invertible
  change (X : Mat d) * ((X : Mat d)⁻¹ * (P : Mat d) * (X : Mat d)⁻¹) * (X : Mat d) = _
  have hu := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  simp only [mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hu]

lemma sandwich_pd (A B : H d) (hA : A ∈ pd d) (hB : B ∈ pd d) :
    sandwich A B ∈ pd d := by
  have hh := hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hA.isUnit)
  rw [A.property.eq] at hh
  exact hh

lemma trace_zero_psd {A : H d} (hA : A ∈ psdCone d) (htr : realTrace A = 0) : A = 0 := by
  apply le_antisymm
  · simpa only [htr, zero_smul] using trace_bound_above hA
  · exact psd_nonneg hA

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SandwichCLM
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

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p7
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_rf66cc3_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p7
lemma sandwich_sub (A U V : H d) : sandwich A (U-V) = sandwich A U - sandwich A V := by
  apply Subtype.ext
  change (A : Mat d) * ((U : Mat d)-(V : Mat d)) * (A : Mat d) = _
  simp only [mul_sub, sub_mul]
  rfl

lemma psd_pointed (A : H d) (hA : A ∈ psdCone d) (hnA : -A ∈ psdCone d) : A = 0 := by
  have h0 := (mem_psd_iff_nonneg A).mp hA
  have h1 := (mem_psd_iff_nonneg (-A)).mp hnA
  exact le_antisymm (neg_nonneg.mp h1) h0

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_rf66cc3_2 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
lemma jordanCLM_val (A B U : H d) :
    ((jordanCLM A B U : H d) : Mat d) =
      (A : Mat d) * (U : Mat d) * (B : Mat d) + (B : Mat d) * (U : Mat d) * (A : Mat d) := by
  change ((A : Mat d)+(B : Mat d)) * (U : Mat d) * ((A : Mat d)+(B : Mat d)) -
    (A : Mat d)*(U : Mat d)*(A : Mat d) - (B : Mat d)*(U : Mat d)*(B : Mat d) = _
  noncomm_ring

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

lemma inverse_remainder (X Z : H d) (hX : X ∈ pd d) (hZ : Z ∈ pd d) :
    invH Z - invH X + sandwich (invH X) (Z-X) =
      sandwich (invH X) (sandwich (Z-X) (invH Z)) := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  have hz := (Matrix.isUnit_iff_isUnit_det (Z : Mat d)).mp hZ.isUnit
  apply Subtype.ext
  change (Z : Mat d)⁻¹ - (X : Mat d)⁻¹ +
    (X : Mat d)⁻¹ * ((Z : Mat d)-(X : Mat d)) * (X : Mat d)⁻¹ =
    (X : Mat d)⁻¹ * (((Z : Mat d)-(X : Mat d)) * (Z : Mat d)⁻¹ *
      ((Z : Mat d)-(X : Mat d))) * (X : Mat d)⁻¹
  symm
  calc
    _ = ((X : Mat d)⁻¹ - (Z : Mat d)⁻¹) * ((Z : Mat d)-(X : Mat d)) * (X : Mat d)⁻¹ := by
      rw [Matrix.inv_sub_inv (show IsUnit (X : Mat d) ↔ IsUnit (Z : Mat d) from
        ⟨fun _ => hZ.isUnit, fun _ => hX.isUnit⟩)]
      simp only [mul_assoc]
    _ = _ := by
      simp only [sub_mul, mul_sub, mul_assoc,
        Matrix.mul_nonsing_inv _ hx,
        Matrix.nonsing_inv_mul_cancel_left _ _ hz, mul_one]
      abel

lemma inverse_trace_gap (P X Z : H d) (hX : X ∈ pd d) (hZ : Z ∈ pd d) :
    (inner ℝ P (invH Z) + inner ℝ (sandwich (invH X) P) Z) -
      (inner ℝ P (invH X) + inner ℝ (sandwich (invH X) P) X) =
      inner ℝ P (sandwich (invH X) (sandwich (Z-X) (invH Z))) := by
  rw [← inverse_remainder X Z hX hZ, inner_add_right, inner_sub_right,
    inner_sandwich, inner_sub_right]
  ring

lemma inverse_trace_gap_nonneg (P X Z : H d) (hP : P ∈ psdCone d)
    (hX : X ∈ pd d) (hZ : Z ∈ pd d) :
    inner ℝ P (invH X) + inner ℝ (sandwich (invH X) P) X ≤
      inner ℝ P (invH Z) + inner ℝ (sandwich (invH X) P) Z := by
  apply sub_nonneg.mp
  rw [inverse_trace_gap P X Z hX hZ]
  exact inner_nonneg_of_psd P _ hP
    (sandwich_psd _ _ (sandwich_psd _ _ hZ.inv.posSemidef))

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_JordanCLMStrictPos
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
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

lemma jordanCLM_strict_pos [NeZero d] (A B : H d) (hA : A ∈ pd d) (hB : B ∈ pd d)
    (U : H d) (hU : U ≠ 0) : 0 < inner ℝ U (jordanCLM A B U) := by
  rw [jordanCLM_quadratic]
  apply mul_pos (by norm_num)
  have hn := inner_nonneg_of_psd B (sandwich U A) hB.posSemidef
    (sandwich_psd U A hA.posSemidef)
  apply lt_of_le_of_ne hn
  intro he
  have hz := eq_zero_of_inner_pd hB (sandwich_psd U A hA.posSemidef) he.symm
  exact hU ((sandwich_eq_zero_iff U A hA).mp hz)

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_EquivSymmetricMap
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.KKT
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma equiv_symmetric_of_map_eq (L : E ≃L[ℝ] E) (F : E →L[ℝ] E)
    (he : L.toContinuousLinearMap = F) (hF : F.toLinearMap.IsSymmetric) :
    L.toLinearEquiv.toLinearMap.IsSymmetric := by
  intro u v
  change inner ℝ (L.toContinuousLinearMap u) v = inner ℝ u (L.toContinuousLinearMap v)
  rw [he]
  exact hF u v

end
end CurrentKS.KKT

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Variables
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.KKT
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem jacobian_injective (e : E) (he : e ≠ 0) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (hH : ∀ u, u ≠ 0 → 0 < inner ℝ u (H u)) :
    Function.Injective (jacobian e L.toContinuousLinearMap H) := by
  suffices hk : ∀ z, jacobian e L.toContinuousLinearMap H z = 0 → z = 0 by
    intro z w hzw
    exact sub_eq_zero.mp (hk (z-w) (by rw [map_sub, hzw, sub_self]))
  intro z hz
  have hr : inner ℝ e z.2.2 = 0 := congrArg Prod.fst hz
  have hf : L z.2.1 + z.1 • e = 0 := congrArg (fun w : Variables E => w.2.1) hz
  have hg : L z.2.2 - H z.2.1 = 0 := congrArg (fun w : Variables E => w.2.2) hz
  have hLe : L z.2.1 = -z.1 • e := by
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hf
  have hHL : H z.2.1 = L z.2.2 := (sub_eq_zero.mp hg).symm
  have hq : inner ℝ z.2.1 (H z.2.1) = 0 := by
    have hs : inner ℝ (L z.2.1) z.2.2 = inner ℝ z.2.1 (L z.2.2) := hL _ _
    rw [hHL, ← hs]
    rw [hLe, real_inner_smul_left, hr, mul_zero]
  have hu : z.2.1 = 0 := by
    by_contra hn
    exact (ne_of_gt (hH _ hn)) hq
  have hh : z.1 = 0 := by
    rw [hu, map_zero, zero_add] at hf
    exact (smul_eq_zero.mp hf).resolve_right he
  have hp : z.2.2 = 0 := by
    apply L.injective
    simpa only [hu, map_zero, sub_zero] using hg
  exact Prod.ext hh (Prod.ext hu hp)

theorem exists_jacobian_equiv (e : E) (he : e ≠ 0) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (hH : ∀ u, u ≠ 0 → 0 < inner ℝ u (H u)) :
    ∃ J : Variables E ≃L[ℝ] Variables E, ∀ z, J z = jacobian e L.toContinuousLinearMap H z := by
  have hi := jacobian_injective e he L hL H hH
  let J := LinearEquiv.ofBijective (jacobian e L.toContinuousLinearMap H).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨J.toContinuousLinearEquiv, fun _ => rfl⟩

end
end CurrentKS.KKT

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairCone
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

lemma isClosed_pairCone : IsClosed (pairCone d : Set (H d × H d)) :=
  (isClosed_psdCone (d := d)).prod (isClosed_psdCone (d := d))

lemma feasible_iff_cone (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z ∈ domain d ∧ -residual S η z ∈ pairCone d := by
  simp only [feasible, mem_ofPred_eq, mem_pairCone, Prod.fst_neg, Prod.snd_neg]
  simp only [mem_psd_iff_nonneg, neg_nonneg]

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SymmetricMap
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

lemma lagrangian_separate (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (P Q : H d) (z : Point d) :
    lagrangian ε S η P Q z =
      z.1 * (1-_root_.OAI.CurrentKS.Hermitian.realTrace P-_root_.OAI.CurrentKS.Hermitian.realTrace Q) + (inner ℝ P S - inner ℝ Q S) +
        (inner ℝ P (invH z.2.1) + inner ℝ (η Q + ε • Hermitian.one) z.2.1) +
        (inner ℝ Q (invH z.2.2) + inner ℝ (η P + ε • Hermitian.one) z.2.2) := by
  simp only [lagrangian, objective, residual, inner_add_right, inner_sub_right,
    inner_add_left, inner_smul_rightH, inner_smul_leftH, inner_right_one,
    inner_one, realTrace_add, hη P z.2.2, hη Q z.2.1]
  ring

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_LagrangianObjective
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma lagrangian_le_objective (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (P Q : H d) (hP : P ∈ psdCone d) (hQ : Q ∈ psdCone d)
    (z : Point d) (hz : z ∈ feasible S η) :
    lagrangian ε S η P Q z ≤ objective ε z := by
  have hf := (feasible_iff_cone S η z).mp hz
  have h₁ := inner_nonneg_of_psd P (-residual S η z).1 hP hf.2.1
  have h₂ := inner_nonneg_of_psd Q (-residual S η z).2 hQ hf.2.2
  simp only [Prod.fst_neg, Prod.snd_neg, inner_neg_right] at h₁ h₂
  change objective ε z + inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 ≤ _
  linarith

lemma lagrangian_eq_objective_of_tight (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (P Q : H d) (z : Point d) (hz : residual S η z = 0) :
    lagrangian ε S η P Q z = objective ε z := by
  simp only [lagrangian, hz, Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]

end CurrentKS.Variational

namespace CurrentKS.PositiveMap
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cone_smul_nonneg (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C)
    {a : ℝ} (ha : 0 ≤ a) {x : E} (hx : x ∈ C) : a • x ∈ C := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simpa using h0
  · exact C.smul_mem ha hx

lemma interior_absorbs (C : ConvexCone ℝ E) {p : E}
    (hp : p ∈ interior (C : Set E)) (x : E) :
    ∃ b : ℝ, 0 ≤ b ∧ x + b • p ∈ C := by
  have hc : Continuous (fun t : ℝ => p + t • x) := by fun_prop
  have hn : ∀ᶠ t : ℝ in nhds 0, p + t • x ∈ C := by
    have h : (fun t : ℝ => p + t • x) 0 ∈ interior (C : Set E) := by simpa using hp
    exact hc.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp h)
  obtain ⟨δ, hδ, hs⟩ := Metric.mem_nhds_iff.mp hn
  have ht : 0 < δ/2 := by positivity
  have htd : δ/2 ∈ Metric.ball (0 : ℝ) δ := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  have hh := C.smul_mem (inv_pos.mpr ht) (hs htd)
  refine ⟨(δ/2)⁻¹, (inv_pos.mpr ht).le, ?_⟩
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_comm] using hh

theorem mem_of_supersolution (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C)
    (hC : IsClosed (C : Set E)) (T : E →L[ℝ] E)
    (hT : ∀ x ∈ C, T x ∈ C) {p : E} (hp : p ∈ interior (C : Set E))
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hcrit : q • p - T p ∈ C)
    {x : E} (hx : x - T x ∈ C) : x ∈ C := by
  obtain ⟨b,hb,hbp⟩ := interior_absorbs C hp x
  have hn (n : ℕ) : x + (b*q^n) • p ∈ C := by
    induction n with
    | zero => simpa using hbp
    | succ n ih =>
      have h₁ := hT _ ih
      have h₂ := cone_smul_nonneg C h0 (mul_nonneg hb (pow_nonneg hq₀ n)) hcrit
      have hh := C.add_mem hx (C.add_mem h₁ h₂)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      simp only [map_add, map_smul, pow_succ]
      module
  have ht : Tendsto (fun n : ℕ => x + (b*q^n) • p) atTop (nhds x) := by
    have hh := ((tendsto_const_nhds (x := b)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁)).smul
      (tendsto_const_nhds (x := p))
    simpa using (tendsto_const_nhds (x := x)).add hh
  exact hC.mem_of_tendsto ht (Eventually.of_forall hn)

theorem positive_inverse [FiniteDimensional ℝ E]
    (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C) (hC : IsClosed (C : Set E))
    (hpoint : ∀ x ∈ C, -x ∈ C → x = 0)
    (T : E →L[ℝ] E) (hT : ∀ x ∈ C, T x ∈ C)
    {p : E} (hp : p ∈ interior (C : Set E))
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hcrit : q • p - T p ∈ C) :
    ∃ V : E ≃L[ℝ] E, (∀ x, V x = x-T x) ∧ ∀ x ∈ C, V.symm x ∈ C := by
  let N : E →ₗ[ℝ] E := LinearMap.id - T.toLinearMap
  have hker (x : E) (hx : N x = 0) : x = 0 := by
    have hx' : x-T x ∈ C := by
      change N x ∈ C
      rw [hx]
      exact h0
    have hn' : -x-T (-x) ∈ C := by
      have he : -x-T (-x) = -(x-T x) := by rw [map_neg]; abel
      rw [he, show x-T x = 0 from hx, neg_zero]
      exact h0
    exact hpoint x (mem_of_supersolution C h0 hC T hT hp hq₀ hq₁ hcrit hx')
      (mem_of_supersolution C h0 hC T hT hp hq₀ hq₁ hcrit hn')
  have hinj : Function.Injective N := by
    intro x y he
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, he, sub_self]
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective N
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let V : E ≃L[ℝ] E := e.toContinuousLinearEquiv
  refine ⟨V, fun _ => rfl, fun x hx => ?_⟩
  apply mem_of_supersolution C h0 hC T hT hp hq₀ hq₁ hcrit
  change V (V.symm x) ∈ C
  rwa [V.apply_symm_apply]

theorem positive_inverse_of_gap [FiniteDimensional ℝ E]
    (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C) (hC : IsClosed (C : Set E))
    (hpoint : ∀ x ∈ C, -x ∈ C → x = 0)
    (T : E →L[ℝ] E) (hT : ∀ x ∈ C, T x ∈ C)
    {p : E} (hp : p ∈ interior (C : Set E))
    (hgap : p-T p ∈ interior (C : Set E)) :
    ∃ V : E ≃L[ℝ] E, (∀ x, V x = x-T x) ∧ ∀ x ∈ C, V.symm x ∈ C := by
  have hc : Continuous (fun t : ℝ => p-T p-t • p) := by fun_prop
  have hn : ∀ᶠ t : ℝ in nhds 0, p-T p-t • p ∈ C := by
    have h : (fun t : ℝ => p-T p-t • p) 0 ∈ interior (C : Set E) := by simpa using hgap
    exact hc.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp h)
  obtain ⟨δ,hδ,hs⟩ := Metric.mem_nhds_iff.mp hn
  let s := min (δ/2) (1/2 : ℝ)
  have hs₀ : 0 < s := lt_min (by positivity) (by norm_num)
  have hs₁ : s ≤ 1/2 := min_le_right _ _
  have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsball : s ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs₀] using hsδ
  apply positive_inverse C h0 hC hpoint T hT hp (q := 1-s) (by linarith) (by linarith)
  have he : (1-s) • p-T p = p-T p-s • p := by module
  rw [he]
  exact hs hsball

end CurrentKS.PositiveMap

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Pair
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

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p3
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p3
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p3
lemma linPositive_preserves (X Y : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d) (z : Pair d) (hz : z ∈ pairCone d) :
    linPositive X Y η z ∈ pairCone d :=
  ⟨sandwich_psd _ _ (hη z.2 hz.2), sandwich_psd _ _ (hη z.1 hz.1)⟩

lemma linCongruence_preserves (X Y : H d) (z : Pair d) (hz : z ∈ pairCone d) :
    linCongruence X Y z ∈ pairCone d :=
  ⟨sandwich_psd _ _ hz.1, sandwich_psd _ _ hz.2⟩

lemma linConstraint_conjugate (X Y : H d) (η : H d →L[ℝ] H d)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) (z : Pair d) :
    linCongruence X Y (linConstraint X Y η z) = z - linPositive X Y η z := by
  apply Prod.ext
  · change sandwich X (sandwich (invH X) z.1 - η z.2) = _
    rw [sandwich_sub, sandwich_inverse_cancel X z.1 hX]
    rfl
  · change sandwich Y (sandwich (invH Y) z.2 - η z.1) = _
    rw [sandwich_sub, sandwich_inverse_cancel Y z.2 hY]
    rfl

lemma pair_pd_interior [NeZero d] {P Q : H d} (hP : P ∈ pd d) (hQ : Q ∈ pd d) :
    (P,Q) ∈ interior (pairCone d : Set (Pair d)) := by
  change (P,Q) ∈ interior ((psdCone d : Set (H d)) ×ˢ (psdCone d : Set (H d)))
  rw [interior_prod_eq]
  exact ⟨posDef_mem_interior _ hP, posDef_mem_interior _ hQ⟩

theorem linConstraint_positive_inverse [NeZero d]
    (X Y P Q : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) (hP : P ∈ pd d) (hQ : Q ∈ pd d)
    {ε : ℝ} (hε : 0 < ε)
    (hPX : P = sandwich X (η Q) + ε • sandwich X (Hermitian.one : H d))
    (hQY : Q = sandwich Y (η P) + ε • sandwich Y (Hermitian.one : H d)) :
    ∃ V : Pair d ≃L[ℝ] Pair d, (∀ z, V z = linConstraint X Y η z) ∧
      ∀ z ∈ pairCone d, V.symm z ∈ pairCone d := by
  have hgap : (P,Q) - linPositive X Y η (P,Q) ∈ interior (pairCone d : Set (Pair d)) := by
    have he : (P,Q) - linPositive X Y η (P,Q) =
        (ε • sandwich X (Hermitian.one : H d), ε • sandwich Y (Hermitian.one : H d)) := by
      apply Prod.ext <;> simp only [linPositive_apply, Prod.fst_sub, Prod.snd_sub]
      · rw [hPX]; abel
      · rw [hQY]; abel
    rw [he]
    apply pair_pd_interior
    · rw [← sandwich_smul]
      exact sandwich_pd X _ hX (scalar_posDef hε)
    · rw [← sandwich_smul]
      exact sandwich_pd Y _ hY (scalar_posDef hε)
  obtain ⟨N, hN, hNpos⟩ := CurrentKS.PositiveMap.positive_inverse_of_gap
    (pairCone d) ⟨zero_mem_psdCone,zero_mem_psdCone⟩ isClosed_pairCone
    (fun z hz hnz => Prod.ext (psd_pointed _ hz.1 hnz.1) (psd_pointed _ hz.2 hnz.2))
    (linPositive X Y η) (linPositive_preserves X Y η hη)
    (pair_pd_interior hP hQ) hgap
  have he (z : Pair d) : linCongruence X Y (linConstraint X Y η z) = N z := by
    rw [hN]
    exact linConstraint_conjugate X Y η hX hY z
  have hinj : Function.Injective (linConstraint X Y η).toLinearMap := by
    intro u v huv
    apply N.injective
    rw [← he, ← he]
    exact congrArg (linCongruence X Y) huv
  let V : Pair d ≃L[ℝ] Pair d :=
    (LinearEquiv.ofBijective (linConstraint X Y η).toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  refine ⟨V, fun _ => rfl, fun z hz => ?_⟩
  have hh : V.symm z = N.symm (linCongruence X Y z) := by
    apply N.injective
    rw [N.apply_symm_apply, ← he]
    change linCongruence X Y (V (V.symm z)) = _
    rw [V.apply_symm_apply]
  rw [hh]
  exact hNpos _ (linCongruence_preserves X Y z hz)

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairHilbert
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

attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpacePairHilbert_p4
lemma linConstraint_symmetric (X Y : H d) (η : H d →L[ℝ] H d) (hη : SymmetricMap η) :
    LinearMap.IsSymmetric (𝕜 := ℝ) (E := PairHilbert d) (onPairHilbert (linConstraint X Y η)).toLinearMap := by
  intro u v
  change inner ℝ (sandwich (invH X) (WithLp.ofLp u).1 - η (WithLp.ofLp u).2) (WithLp.ofLp v).1 +
    inner ℝ (sandwich (invH Y) (WithLp.ofLp u).2 - η (WithLp.ofLp u).1) (WithLp.ofLp v).2 =
    inner ℝ (WithLp.ofLp u).1 (sandwich (invH X) (WithLp.ofLp v).1 - η (WithLp.ofLp v).2) +
    inner ℝ (WithLp.ofLp u).2 (sandwich (invH Y) (WithLp.ofLp v).2 - η (WithLp.ofLp v).1)
  simp only [inner_sub_left, inner_sub_right, inner_sandwich]
  rw [hη (WithLp.ofLp u).1 (WithLp.ofLp v).2, hη (WithLp.ofLp u).2 (WithLp.ofLp v).1]
  ring

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Pack
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
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d : ℕ}

lemma identityPair_ne_zero [NeZero d] : identityPair d ≠ 0 := by
  intro h
  have he : (Hermitian.one : H d) = 0 := congrArg (fun u : PairHilbert d => (WithLp.ofLp u).1) h
  have hh := congrArg (fun A : H d => (A : Mat d) 0 0) he
  simp at hh

lemma hessian_strict_pos [NeZero d] (X Y P Q : H d)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) (hP : P ∈ pd d) (hQ : Q ∈ pd d)
    (u : PairHilbert d) (hu : u ≠ 0) : 0 < inner ℝ u (hessian X Y P Q u) := by
  have hp := sandwich_pd (invH X) P hX.inv hP
  have hq := sandwich_pd (invH Y) Q hY.inv hQ
  have h₁ : 0 ≤ inner ℝ (WithLp.ofLp u).1
      (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp u).1) := by
    rw [jordanCLM_quadratic]
    exact mul_nonneg (by norm_num) (inner_nonneg_of_psd _ _ hp.posSemidef
      (sandwich_psd _ _ hX.inv.posSemidef))
  have h₂ : 0 ≤ inner ℝ (WithLp.ofLp u).2
      (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp u).2) := by
    rw [jordanCLM_quadratic]
    exact mul_nonneg (by norm_num) (inner_nonneg_of_psd _ _ hq.posSemidef
      (sandwich_psd _ _ hY.inv.posSemidef))
  change 0 < inner ℝ (WithLp.ofLp u).1
      (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp u).1) +
    inner ℝ (WithLp.ofLp u).2
      (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp u).2)
  by_cases hx : (WithLp.ofLp u).1 = 0
  · have hy : (WithLp.ofLp u).2 ≠ 0 := by
      intro hy
      apply hu
      apply (pairEquiv d).injective
      exact Prod.ext hx hy
    exact add_pos_of_nonneg_of_pos h₁ (jordanCLM_strict_pos _ _ hY.inv hq _ hy)
  · exact add_pos_of_pos_of_nonneg (jordanCLM_strict_pos _ _ hX.inv hp _ hx) h₂

theorem kkt_regular [NeZero d] (X Y P Q : H d) (η : H d →L[ℝ] H d)
    (hηpos : ∀ A ∈ psdCone d, η A ∈ psdCone d) (hηsym : SymmetricMap η)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) (hP : P ∈ pd d) (hQ : Q ∈ pd d)
    {ε : ℝ} (hε : 0 < ε)
    (hPX : P = sandwich X (η Q) + ε • sandwich X (Hermitian.one : H d))
    (hQY : Q = sandwich Y (η P) + ε • sandwich Y (Hermitian.one : H d)) :
    ∃ J : Vars d ≃L[ℝ] Vars d, ∀ v, J v = CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint X Y η)) (hessian X Y P Q) v := by
  obtain ⟨V,hV,_⟩ := linConstraint_positive_inverse X Y P Q η hηpos hX hY hP hQ hε hPX hQY
  let L : PairHilbert d ≃L[ℝ] PairHilbert d := ((pairEquiv d).trans V).trans (pairEquiv d).symm
  have he : L.toContinuousLinearMap = onPairHilbert (linConstraint X Y η) := by
    apply ContinuousLinearMap.ext
    intro u
    change (pairEquiv d).symm (V (pairEquiv d u)) =
      (pairEquiv d).symm (linConstraint X Y η (pairEquiv d u))
    rw [hV]
  have hs := CurrentKS.KKT.equiv_symmetric_of_map_eq L _ he
    (linConstraint_symmetric X Y η hηsym)
  obtain ⟨J,hJ⟩ := CurrentKS.KKT.exists_jacobian_equiv (identityPair d)
    identityPair_ne_zero L hs (hessian X Y P Q) (hessian_strict_pos X Y P Q hX hY hP hQ)
  refine ⟨J, fun v => ?_⟩
  exact (hJ v).trans (congrArg (fun T =>
    CurrentKS.KKT.jacobian (identityPair d) T (hessian X Y P Q) v) he)

lemma pack_kkt (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Point d) (P Q : H d)
    (htr : _root_.OAI.CurrentKS.Hermitian.realTrace P + _root_.OAI.CurrentKS.Hermitian.realTrace Q = 1)
    (ht : residual S η z = 0)
    (hX : sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d))
    (hY : sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d)) :
    kktSystem ε S η (pack z P Q) = 0 := by
  apply Prod.ext
  · change inner ℝ (Hermitian.one : H d) P + inner ℝ (Hermitian.one : H d) Q - 1 = 0
    rw [inner_one,inner_one,htr]
    ring
  · apply Prod.ext
    · apply (pairEquiv d).injective
      have ht₁ := congrArg Prod.fst ht
      have ht₂ := congrArg Prod.snd ht
      change invH z.2.1 + S + η z.2.2 - z.1 • (Hermitian.one : H d) = 0 at ht₁
      change invH z.2.2 - S + η z.2.1 - z.1 • (Hermitian.one : H d) = 0 at ht₂
      apply Prod.ext
      · change z.1 • (Hermitian.one : H d) - invH z.2.1 - S - η z.2.2 = 0
        calc
          _ = -(invH z.2.1 + S + η z.2.2 - z.1 • (Hermitian.one : H d)) := by module
          _ = 0 := by rw [ht₁, neg_zero]
      · change z.1 • (Hermitian.one : H d) - invH z.2.2 + S - η z.2.1 = 0
        calc
          _ = -(invH z.2.2 - S + η z.2.1 - z.1 • (Hermitian.one : H d)) := by module
          _ = 0 := by rw [ht₂, neg_zero]
    · apply (pairEquiv d).injective
      apply Prod.ext
      · change sandwich (invH z.2.1) P - η Q - ε • (Hermitian.one : H d) = 0
        rw [hX]
        module
      · change sandwich (invH z.2.2) Q - η P - ε • (Hermitian.one : H d) = 0
        rw [hY]
        module

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

theorem optimal_of_kkt (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hηsym : SymmetricMap η) (z : Point d) (hz : z ∈ domain d)
    (P Q : H d) (hP : P ∈ psdCone d) (hQ : Q ∈ psdCone d)
    (htr : _root_.OAI.CurrentKS.Hermitian.realTrace P + _root_.OAI.CurrentKS.Hermitian.realTrace Q = 1)
    (hX : sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d))
    (hY : sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d))
    (htight : residual S η z = 0) :
    z ∈ feasible S η ∧ ∀ w ∈ feasible S η, objective ε z ≤ objective ε w := by
  have hf : z ∈ feasible S η := by
    refine ⟨hz,?_,?_⟩ <;> simp [htight]
  refine ⟨hf,fun w hw => ?_⟩
  have h₁ := inverse_trace_gap_nonneg P z.2.1 w.2.1 hP hz.1 hw.1.1
  have h₂ := inverse_trace_gap_nonneg Q z.2.2 w.2.2 hQ hz.2 hw.1.2
  rw [hX] at h₁
  rw [hY] at h₂
  have hL : lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w := by
    rw [lagrangian_separate ε S η hηsym, lagrangian_separate ε S η hηsym]
    have hc : 1-_root_.OAI.CurrentKS.Hermitian.realTrace P-_root_.OAI.CurrentKS.Hermitian.realTrace Q = 0 := by linarith
    rw [hc, mul_zero, mul_zero]
    linarith
  rw [lagrangian_eq_objective_of_tight ε S η P Q z htight] at hL
  exact hL.trans (lagrangian_le_objective ε S η P Q hP hQ w hw)

end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Value
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

lemma value_eq_of_min (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    value ε S η = objective ε z := by
  apply IsLeast.csInf_eq
  refine ⟨⟨z,hz,rfl⟩,?_⟩
  rintro b ⟨w,hw,rfl⟩
  exact hmin w hw

lemma value_eq_of_kkt (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hηsym : SymmetricMap η) (z : Point d) (hz : z ∈ domain d)
    (P Q : H d) (hP : P ∈ psdCone d) (hQ : Q ∈ psdCone d)
    (htr : _root_.OAI.CurrentKS.Hermitian.realTrace P + _root_.OAI.CurrentKS.Hermitian.realTrace Q = 1)
    (hX : sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d))
    (hY : sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d))
    (htight : residual S η z = 0) : value ε S η = objective ε z := by
  obtain ⟨hf,hm⟩ := optimal_of_kkt ε S η hηsym z hz P Q hP hQ htr hX hY htight
  exact value_eq_of_min ε S η z hf hm

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_UnpackKkt
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
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

lemma unpack_kkt (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Vars d)
    (hz : kktSystem ε S η z = 0) :
    _root_.OAI.CurrentKS.Hermitian.realTrace (mCoord d z) + _root_.OAI.CurrentKS.Hermitian.realTrace (nCoord d z) = 1 ∧
    residual S η (unpack z) = 0 ∧
    sandwich (invH (xCoord d z)) (mCoord d z) = η (nCoord d z) + ε • (Hermitian.one : H d) ∧
    sandwich (invH (yCoord d z)) (nCoord d z) = η (mCoord d z) + ε • (Hermitian.one : H d) := by
  have htr := congrArg Prod.fst hz
  have ht := congrArg (fun v : Vars d => pairEquiv d v.2.1) hz
  have hs := congrArg (fun v : Vars d => pairEquiv d v.2.2) hz
  have ht₁ := congrArg Prod.fst ht
  have ht₂ := congrArg Prod.snd ht
  have hs₁ := congrArg Prod.fst hs
  have hs₂ := congrArg Prod.snd hs
  change inner ℝ (Hermitian.one : H d) (mCoord d z) +
    inner ℝ (Hermitian.one : H d) (nCoord d z) - 1 = 0 at htr
  rw [inner_one,inner_one] at htr
  refine ⟨sub_eq_zero.mp htr,?_,?_,?_⟩
  · change tCoord d z • (Hermitian.one : H d) - invH (xCoord d z) - S - η (yCoord d z) = 0 at ht₁
    change tCoord d z • (Hermitian.one : H d) - invH (yCoord d z) + S - η (xCoord d z) = 0 at ht₂
    apply Prod.ext
    · change invH (xCoord d z) + S + η (yCoord d z) - tCoord d z • (Hermitian.one : H d) = 0
      calc
        _ = -(tCoord d z • (Hermitian.one : H d) - invH (xCoord d z) - S - η (yCoord d z)) := by module
        _ = 0 := by rw [ht₁,neg_zero]
    · change invH (yCoord d z) - S + η (xCoord d z) - tCoord d z • (Hermitian.one : H d) = 0
      calc
        _ = -(tCoord d z • (Hermitian.one : H d) - invH (yCoord d z) + S - η (xCoord d z)) := by module
        _ = 0 := by rw [ht₂,neg_zero]
  · change sandwich (invH (xCoord d z)) (mCoord d z) - η (nCoord d z) - ε • (Hermitian.one : H d) = 0 at hs₁
    exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hs₁)
  · change sandwich (invH (yCoord d z)) (nCoord d z) - η (mCoord d z) - ε • (Hermitian.one : H d) = 0 at hs₂
    exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hs₂)

lemma value_eq_of_system (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hP : mCoord d z ∈ psdCone d) (hQ : nCoord d z ∈ psdCone d)
    (hz : kktSystem ε S η z = 0) : value ε S η = objective ε (unpack z) := by
  obtain ⟨htr,ht,hx,hy⟩ := unpack_kkt ε S η z hz
  exact value_eq_of_kkt ε S η hη (unpack z) ⟨hX,hY⟩ (mCoord d z) (nCoord d z)
    hP hQ htr hx hy ht

lemma contDiff_objective (ε : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (objective (d := d) ε) := by
  have ht : ContDiff ℝ n (fun z : Point d => inner ℝ (Hermitian.one : H d) (z.2.1+z.2.2)) :=
    (innerSL ℝ (Hermitian.one : H d)).contDiff.comp (contDiff_snd.fst.add contDiff_snd.snd)
  have hh := contDiff_fst.add ((contDiff_const (c := ε)).mul ht)
  simp only [inner_one] at hh
  exact hh

lemma contDiff_unpack {n : WithTop ℕ∞} : ContDiff ℝ n (unpack (d := d)) :=
  (tCoord d).contDiff.prodMk ((xCoord d).contDiff.prodMk (yCoord d).contDiff)

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p6
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6
theorem contDiffAt_value_oai [NeZero d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) (hε : 0 < ε) (S : E → H d) (η : E → (H d →L[ℝ] H d)) (b : E)
    (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
    (hηpos : ∀ A ∈ psdCone d, η b A ∈ psdCone d)
    (hηsym : ∀ᶠ a in 𝓝 b, SymmetricMap (η a))
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S b) (hS₂ : S b ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S b) (η b))
    (hmin : ∀ w ∈ feasible (S b) (η b), objective ε z ≤ objective ε w) :
    ContDiffAt ℝ ∞ (fun a => value ε (S a) (η a)) b := by
  have hsym := hηsym.self_of_nhds
  obtain ⟨P,Q,hP,hQ,_,_,htr,hPX,hQY,ht,hx,hy⟩ :=
    kkt (S b) (η b) hηpos hsym hε hS₁ hS₂ z hz hmin
  obtain ⟨J,hJ⟩ := kkt_regular z.2.1 z.2.2 P Q (η b) hηpos hsym hz.1.1 hz.1.2 hP hQ hε hPX hQY
  have he := pack_kkt ε (S b) (η b) z P Q htr ht hx hy
  obtain ⟨f,hf,hfc,hfe⟩ := exists_smooth_kkt_branch ε (S b,η b) (pack z P Q) hz.1.1 hz.1.2 J hJ
  let g : E → Vars d := fun a => f (S a,η a)
  have hg : g b = pack z P Q := hf
  have hgc : ContDiffAt ℝ ∞ g b := hfc.comp b (hS.prodMk hη)
  have hge : ∀ᶠ a in 𝓝 b, kktSystem ε (S a) (η a) (g a) = 0 := by
    filter_upwards [(hS.continuousAt.prodMk hη.continuousAt).eventually hfe] with a ha
    exact ha.trans he
  have hXg : ∀ᶠ a in 𝓝 b, xCoord d (g a) ∈ pd d := by
    apply ((xCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change xCoord d (g b) ∈ pd d
    rw [hg]
    exact hz.1.1
  have hYg : ∀ᶠ a in 𝓝 b, yCoord d (g a) ∈ pd d := by
    apply ((yCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change yCoord d (g b) ∈ pd d
    rw [hg]
    exact hz.1.2
  have hPg : ∀ᶠ a in 𝓝 b, mCoord d (g a) ∈ pd d := by
    apply ((mCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change mCoord d (g b) ∈ pd d
    rw [hg]
    exact hP
  have hQg : ∀ᶠ a in 𝓝 b, nCoord d (g a) ∈ pd d := by
    apply ((nCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change nCoord d (g b) ∈ pd d
    rw [hg]
    exact hQ
  have hval : (fun a => value ε (S a) (η a)) =ᶠ[𝓝 b] (fun a => objective ε (unpack (g a))) := by
    filter_upwards [hηsym,hge,hXg,hYg,hPg,hQg] with a ha he hx hy hp hq
    exact value_eq_of_system ε (S a) (η a) ha (g a) hx hy hp.posSemidef hq.posSemidef he
  exact ((contDiff_objective ε).contDiffAt.comp b
    ((contDiff_unpack (d := d)).contDiffAt.comp b hgc)).congr_of_eventuallyEq hval

end
end CurrentKS.Variational

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CurrentKS.Variational.contDiffAt_value_oai.{u_1} := @OAI.CurrentKS.Variational.contDiffAt_value_oai.{u_1}
