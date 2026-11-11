-- Prove2me | solution 1 for OAI.CurrentKS.Variational.full_jacobian_inverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:04.126332+00:00
-- url     : https://prove2.me/submissions/226c96ea-c81b-4b9a-985d-3323ba0b5d56

import Mathlib
import Definitions.Def_OAIQ241TT006

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

lemma inverse_bound_below {a : ℝ} (ha : 0 < a) {A : H d}
    (hA : A ∈ pd d) (he : invH A ≤ a • one) : a⁻¹ • one ≤ A := by
  let : Invertible (A : Mat d) := hA.isUnit.invertible
  have hi := inverse_antitone hA.inv (scalar_posDef ha) he
  rw [scalar_inv, Matrix.inv_inv_of_invertible] at hi
  change ((a⁻¹ : ℝ) : ℂ) • (1 : Mat d) ≤ (A : Mat d)
  simpa only [Complex.ofReal_inv] using hi

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_ra6e136_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p7
lemma sandwich_sub (A U V : H d) : sandwich A (U-V) = sandwich A U - sandwich A V := by
  apply Subtype.ext
  change (A : Mat d) * ((U : Mat d)-(V : Mat d)) * (A : Mat d) = _
  simp only [mul_sub, sub_mul]
  rfl

lemma invH_involutive (X : H d) (hX : X ∈ pd d) : invH (invH X) = X := by
  apply Subtype.ext
  exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hX.isUnit)

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_ra6e136_2 : NormedSpace ℝ (H d) := inferInstance
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

lemma sandwich_mono (U : H d) {A B : H d} (h : A ≤ B) : sandwich U A ≤ sandwich U B := by
  have hp := sandwich_psd U (B-A) ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h))
  rw [sandwich_sub, mem_psd_iff_nonneg] at hp
  exact sub_nonneg.mp hp

lemma inner_mono_right {P A B : H d} (hP : P ∈ psdCone d) (h : A ≤ B) :
    inner ℝ P A ≤ inner ℝ P B := by
  have hh := inner_nonneg_of_psd P (B-A) hP ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h))
  rw [inner_sub_right] at hh
  linarith

lemma inner_mono_left {P A B : H d} (hP : P ∈ psdCone d) (h : A ≤ B) :
    inner ℝ A P ≤ inner ℝ B P := by
  simpa only [real_inner_comm] using inner_mono_right hP h

lemma trace_square_norm (U : H d) : inner ℝ (Hermitian.one : H d) (sandwich U Hermitian.one) = ‖U‖^2 := by
  rw [inner_eq_trace, sandwich_val, one_val, one_mul, mul_one, ← inner_eq_trace U U]
  exact real_inner_self_eq_norm_sq U

lemma jordanCLM_lower (A B : H d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : a • (Hermitian.one : H d) ≤ A) (hB : b • (Hermitian.one : H d) ≤ B) (U : H d) :
    (2*a*b) * ‖U‖^2 ≤ inner ℝ U (jordanCLM A B U) := by
  have hApos : A ∈ psdCone d := (mem_psd_iff_nonneg _).mpr
    ((psd_nonneg (psd_smul (A := (Hermitian.one : H d)) one_mem_psdCone ha)).trans hA)
  have h₁ := inner_mono_left (sandwich_psd U A hApos) hB
  have h₂ := inner_mono_right (P := (Hermitian.one : H d)) one_mem_psdCone (sandwich_mono U hA)
  rw [inner_smul_leftH] at h₁
  rw [sandwich_smul, inner_smul_rightH, trace_square_norm] at h₂
  rw [jordanCLM_quadratic]
  nlinarith [mul_le_mul_of_nonneg_left h₂ hb]

lemma jordanCLM_upper (A B : H d) {a b : ℝ} (hb : 0 ≤ b)
    (hApos : A ∈ psdCone d) (hA : A ≤ a • (Hermitian.one : H d))
    (hB : B ≤ b • (Hermitian.one : H d)) (U : H d) :
    inner ℝ U (jordanCLM A B U) ≤ (2*a*b) * ‖U‖^2 := by
  have h₁ := inner_mono_left (sandwich_psd U A hApos) hB
  have h₂ := inner_mono_right (P := (Hermitian.one : H d)) one_mem_psdCone (sandwich_mono U hA)
  rw [inner_smul_leftH] at h₁
  rw [sandwich_smul, inner_smul_rightH, trace_square_norm] at h₂
  rw [jordanCLM_quadratic]
  nlinarith [mul_le_mul_of_nonneg_left h₂ hb]

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SquareScalarBound
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
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}
section Operator
open scoped Matrix.Norms.L2Operator

lemma square_scalar_bound (A : H d) {a : ℝ} (ha : 0 ≤ a)
    (hApos : A ∈ psdCone d) (hA : A ≤ a • (Hermitian.one : H d)) :
    sandwich A Hermitian.one ≤ a^2 • (Hermitian.one : H d) := by
  let : CStarAlgebra (Mat d) := {}
  have hnorm : ‖(A : Mat d)‖ ≤ a := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap (A : Mat d) ha hApos.nonneg).mpr
    simp only [Algebra.algebraMap_eq_smul_one]
    exact hA
  have hsqpos : ((A : Mat d)*(A : Mat d)).PosSemidef := by
    have hh : ((sandwich A Hermitian.one : H d) : Mat d).PosSemidef :=
      sandwich_psd A Hermitian.one one_mem_psdCone
    simpa only [sandwich_val, one_val, mul_one] using hh
  have hsqnorm : ‖(A : Mat d)*(A : Mat d)‖ ≤ a^2 :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (A : Mat d)])
  have hb := (CStarAlgebra.norm_le_iff_le_algebraMap ((A : Mat d)*(A : Mat d))
    (sq_nonneg a) hsqpos.nonneg).mp hsqnorm
  change (A : Mat d)*1*(A : Mat d) ≤ (a^2 : ℝ) • (1 : Mat d)
  simpa only [Algebra.algebraMap_eq_smul_one, mul_one] using hb

end Operator

lemma inverse_lower_of_upper (X : H d) (hX : X ∈ pd d) {a : ℝ} (ha : 0 < a)
    (h : X ≤ a • (Hermitian.one : H d)) : a⁻¹ • (Hermitian.one : H d) ≤ invH X := by
  exact inverse_bound_below ha hX.inv (by rwa [invH_involutive X hX])

lemma inverse_upper_of_lower (X : H d) (hX : X ∈ pd d) {a : ℝ} (ha : 0 < a)
    (h : a • (Hermitian.one : H d) ≤ X) : invH X ≤ a⁻¹ • (Hermitian.one : H d) := by
  have hi := inverse_antitone (scalar_posDef ha) hX h
  rw [scalar_inv] at hi
  change (X : Mat d)⁻¹ ≤ ((a⁻¹ : ℝ) : ℂ) • (1 : Mat d)
  simpa only [Complex.ofReal_inv] using hi

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

lemma inverse_elimination (e : E) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (z rhs : Variables E) (hz : jacobian e L.toContinuousLinearMap H z = rhs) :
    z.2.1 = L.symm rhs.2.1 - z.1 • L.symm e ∧
    z.2.2 = L.symm rhs.2.2 + L.symm (H (L.symm rhs.2.1)) - z.1 • L.symm (H (L.symm e)) ∧
    z.1 * inner ℝ (L.symm e) (H (L.symm e)) =
      inner ℝ (L.symm e) rhs.2.2 + inner ℝ (L.symm e) (H (L.symm rhs.2.1)) - rhs.1 := by
  have hr : inner ℝ e z.2.2 = rhs.1 := congrArg Prod.fst hz
  have hf : L z.2.1 + z.1 • e = rhs.2.1 := congrArg (fun w : Variables E => w.2.1) hz
  have hg : L z.2.2 - H z.2.1 = rhs.2.2 := congrArg (fun w : Variables E => w.2.2) hz
  have hu : z.2.1 = L.symm rhs.2.1 - z.1 • L.symm e := by
    apply L.injective
    simp only [map_sub, map_smul, L.apply_symm_apply]
    exact eq_sub_iff_add_eq.mpr hf
  have hp : z.2.2 = L.symm rhs.2.2 + L.symm (H (L.symm rhs.2.1)) - z.1 • L.symm (H (L.symm e)) := by
    apply L.injective
    simp only [map_sub, map_add, map_smul, L.apply_symm_apply]
    rw [hu, map_sub, map_smul] at hg
    rw [sub_eq_iff_eq_add] at hg
    rw [hg]
    module
  refine ⟨hu,hp,?_⟩
  rw [hp, inner_sub_right, inner_add_right, real_inner_smul_right] at hr
  have hs := hL.toLinearMap_symm
  have heq (v : E) : inner ℝ e (L.symm v) = inner ℝ (L.symm e) v := (hs e v).symm
  rw [heq, heq, heq] at hr
  linarith

end
end CurrentKS.KKT

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_InverseEliminationBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.KKT
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma inverse_elimination_bounds (e : E) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (z rhs : Variables E) (hz : jacobian e L.toContinuousLinearMap H z = rhs)
    {b H0 δ : ℝ} (hb : 0 ≤ b) (hH0 : 0 ≤ H0) (hδ : 0 < δ)
    (hB : ‖L.symm.toContinuousLinearMap‖ ≤ b) (hBe : ‖L.symm e‖ ≤ b)
    (hH : ‖H‖ ≤ H0) (hden : δ ≤ inner ℝ (L.symm e) (H (L.symm e))) (hrhs : ‖rhs‖ ≤ 1) :
    |z.1| ≤ (1+b+H0*b^2)/δ ∧
    ‖z.2.1‖ ≤ b*(1+|z.1|) ∧
    ‖z.2.2‖ ≤ b*(1+H0*‖z.2.1‖) := by
  have hr : |rhs.1| ≤ 1 := by
    exact (norm_fst_le rhs).trans hrhs
  have hf : ‖rhs.2.1‖ ≤ 1 := (norm_fst_le rhs.2).trans ((norm_snd_le rhs).trans hrhs)
  have hg : ‖rhs.2.2‖ ≤ 1 := (norm_snd_le rhs.2).trans ((norm_snd_le rhs).trans hrhs)
  have hbn (x : E) : ‖L.symm x‖ ≤ b*‖x‖ :=
    (L.symm.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hhn (x : E) : ‖H x‖ ≤ H0*‖x‖ :=
    (H.le_opNorm x).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  obtain ⟨hu,_hp,hh⟩ := inverse_elimination e L hL H z rhs hz
  have hscalar : |z.1| ≤ (1+b+H0*b^2)/δ := by
    have hnum : |inner ℝ (L.symm e) rhs.2.2 + inner ℝ (L.symm e) (H (L.symm rhs.2.1)) - rhs.1| ≤
        b+H0*b^2+1 := by
      calc
        _ ≤ |inner ℝ (L.symm e) rhs.2.2|+|inner ℝ (L.symm e) (H (L.symm rhs.2.1))|+|rhs.1| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
        _ ≤ ‖L.symm e‖*‖rhs.2.2‖+‖L.symm e‖*‖H (L.symm rhs.2.1)‖+1 := by
          gcongr <;> exact abs_real_inner_le_norm _ _
        _ ≤ b*1+b*(H0*(b*1))+1 := by
          have hnorm : ‖H (L.symm rhs.2.1)‖ ≤ H0*(b*1) :=
            (hhn _).trans (mul_le_mul_of_nonneg_left
              ((hbn _).trans (mul_le_mul_of_nonneg_left hf hb)) hH0)
          exact add_le_add (add_le_add
            (mul_le_mul hBe hg (norm_nonneg _) hb)
            (mul_le_mul hBe hnorm (norm_nonneg _) hb)) (le_refl 1)
        _ = _ := by ring
    rw [← hh,abs_mul,abs_of_pos (hδ.trans_le hden)] at hnum
    have hm := mul_le_mul_of_nonneg_left hden (abs_nonneg z.1)
    exact (le_div_iff₀ hδ).mpr (by linarith)
  refine ⟨hscalar,?_,?_⟩
  · rw [hu]
    calc
      _ ≤ ‖L.symm rhs.2.1‖+‖z.1 • L.symm e‖ := norm_sub_le _ _
      _ ≤ b*1+|z.1| * b := by
        rw [norm_smul,Real.norm_eq_abs]
        exact add_le_add ((hbn _).trans (mul_le_mul_of_nonneg_left hf hb))
          (mul_le_mul_of_nonneg_left hBe (abs_nonneg _))
      _ = _ := by ring
  · have hg' : z.2.2 = L.symm (rhs.2.2+H z.2.1) := by
      apply L.injective
      rw [L.apply_symm_apply]
      have he := congrArg (fun w : Variables E => w.2.2) hz
      change L z.2.2-H z.2.1 = rhs.2.2 at he
      exact sub_eq_iff_eq_add.mp he
    rw [hg']
    calc
      _ ≤ b*‖rhs.2.2+H z.2.1‖ := hbn _
      _ ≤ b*(‖rhs.2.2‖+‖H z.2.1‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hb
      _ ≤ b*(1+H0*‖z.2.1‖) := mul_le_mul_of_nonneg_left (add_le_add hg (hhn _)) hb

lemma inverse_elimination_numeric {d b h u p : ℝ} (hd : 0 < d) (hb : 0 ≤ b)
    (hh : |h| ≤ (1+b+16000000*b^2)/(1/(100*d)))
    (hu : u ≤ b*(1+|h|)) (hp : p ≤ b*(1+16000000*u)) :
    |h| ≤ 10^18*(d+1)*(1+b)^4 ∧ u ≤ 10^18*(d+1)*(1+b)^4 ∧
      p ≤ 10^18*(d+1)*(1+b)^4 := by
  let s := 1+b
  have hs : 1 ≤ s := by dsimp [s] <;> linarith
  have hs0 : 0 ≤ s := le_trans zero_le_one hs
  have hbs : b ≤ s := by dsimp [s] <;> linarith
  have hD : 1 ≤ d+1 := by linarith
  have hD0 : 0 ≤ d+1 := by linarith
  have hs2 : 1 ≤ s^2 := one_le_pow₀ hs
  have hs3 : 1 ≤ s^3 := one_le_pow₀ hs
  have hs4 : 1 ≤ s^4 := one_le_pow₀ hs
  have hs12 : s ≤ s^2 := by nlinarith
  have hb2 : b^2 ≤ s^2 := pow_le_pow_left₀ hb hbs _
  have hD2 : 1 ≤ (d+1)*s^2 := one_le_mul_of_one_le_of_one_le hD hs2
  have hD3 : 1 ≤ (d+1)*s^3 := one_le_mul_of_one_le_of_one_le hD hs3
  have hsmall : |h| ≤ 2000000000*(d+1)*s^2 := by
    have hfrac : (1+b+16000000*b^2)/(1/(100*d)) = 100*d*(1+b+16000000*b^2) := by field_simp
    rw [hfrac] at hh
    calc
      _ ≤ 100*d*(1+b+16000000*b^2) := hh
      _ ≤ 100*d*(16000001*s^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [s] at hs12
        nlinarith
      _ ≤ 2000000000*(d+1)*s^2 := by nlinarith [mul_nonneg hd.le (sq_nonneg s)]
  have hu' : u ≤ 3000000000*(d+1)*s^3 := by
    calc
      _ ≤ b*(1+|h|) := hu
      _ ≤ s*(1+2000000000*(d+1)*s^2) := by gcongr
      _ ≤ s*(3000000000*(d+1)*s^2) := by
        apply mul_le_mul_of_nonneg_left _ hs0
        nlinarith
      _ = _ := by ring
  have hp' : p ≤ 50000000000000000*(d+1)*s^4 := by
    calc
      _ ≤ b*(1+16000000*u) := hp
      _ ≤ b*(1+16000000*(3000000000*(d+1)*s^3)) := by gcongr
      _ ≤ s*(1+16000000*(3000000000*(d+1)*s^3)) := by gcongr
      _ ≤ s*(50000000000000000*(d+1)*s^3) := by
        apply mul_le_mul_of_nonneg_left _ hs0
        nlinarith
      _ = _ := by ring
  have hs24 : s^2 ≤ s^4 := pow_le_pow_right₀ hs (by omega)
  have hs34 : s^3 ≤ s^4 := pow_le_pow_right₀ hs (by omega)
  change |h| ≤ (10:ℝ)^18*(d+1)*s^4 ∧ u ≤ (10:ℝ)^18*(d+1)*s^4 ∧
    p ≤ (10:ℝ)^18*(d+1)*s^4
  refine ⟨hsmall.trans ?_,hu'.trans ?_,hp'.trans ?_⟩
  · gcongr; norm_num
  · gcongr; norm_num
  · gcongr; norm_num

lemma jacobian_inverse_norm_100 (e : E) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (J : Variables E ≃L[ℝ] Variables E)
    (hJ : ∀ z,J z = jacobian e L.toContinuousLinearMap H z)
    {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hB : ‖L.symm.toContinuousLinearMap‖ ≤ ε⁻¹) (hBe : ‖L.symm e‖ ≤ ε⁻¹)
    (hH : ‖H‖ ≤ 16000000)
    (hden : 1/(100*d) ≤ inner ℝ (L.symm e) (H (L.symm e))) :
    ‖J.symm.toContinuousLinearMap‖ ≤ 10^18*(d+1)*(1+ε⁻¹)^4 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro rhs hrhs
  have heq : jacobian e L.toContinuousLinearMap H (J.symm rhs) = rhs := by
    rw [← hJ,J.apply_symm_apply]
  obtain ⟨hh,hu,hp⟩ := inverse_elimination_bounds e L hL H _ rhs heq (inv_nonneg.mpr hε.le)
    (show (0:ℝ)≤16000000 by norm_num) (show 0<1/(100*d) by positivity) hB hBe hH hden hrhs.le
  obtain ⟨hh',hu',hp'⟩ := inverse_elimination_numeric hd (inv_nonneg.mpr hε.le) hh hu hp
  change max |(J.symm rhs).1| (max ‖(J.symm rhs).2.1‖ ‖(J.symm rhs).2.2‖) ≤ _
  exact max_le hh' (max_le hu' hp')

end CurrentKS.KKT

end

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormalizedMinimizer
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.PositiveMap
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eigenvalue_abs_le (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C)
    (hC : IsClosed (C : Set E)) (hpoint : ∀ x ∈ C, -x ∈ C → x = 0)
    (T : E →L[ℝ] E) (hT : ∀ x ∈ C, T x ∈ C)
    {p : E} (hp : p ∈ interior (C : Set E)) {c : ℝ} (hc : 0 ≤ c)
    (hbound : c • p - T p ∈ C) {r : ℝ} {x : E} (hx : x ≠ 0)
    (heig : T x = r • x) : |r| ≤ c := by
  by_contra! hbad
  have hrpos : 0 < |r| := hc.trans_lt hbad
  have hrsq : 0 < r^2 := sq_pos_of_ne_zero (abs_pos.mp hrpos)
  have hcsq : c^2 < r^2 := by nlinarith [sq_abs r]
  let U : E →L[ℝ] E := (r^2)⁻¹ • (T.comp T)
  have hU : ∀ y ∈ C, U y ∈ C := by
    intro y hy
    exact cone_smul_nonneg C h0 (inv_pos.mpr hrsq).le (hT _ (hT y hy))
  have hcrit : (c^2/r^2) • p - U p ∈ C := by
    have hh := C.add_mem (hT _ hbound) (cone_smul_nonneg C h0 hc hbound)
    have he : T (c • p-T p) + c • (c • p-T p) = c^2 • p - T (T p) := by
      simp only [map_sub, map_smul]
      module
    rw [he] at hh
    have hs := cone_smul_nonneg C h0 (inv_pos.mpr hrsq).le hh
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    simp only [U, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      smul_sub, smul_smul, div_eq_mul_inv]
    rw [mul_comm (c^2) ((r^2)⁻¹)]
  have heU : U x = x := by
    change (r^2)⁻¹ • T (T x) = x
    simp only [heig, map_smul, smul_smul]
    rw [← pow_two, inv_mul_cancel₀ hrsq.ne', one_smul]
  have hxC : x ∈ C := mem_of_supersolution C h0 hC U hU hp
    (div_nonneg (sq_nonneg c) hrsq.le) ((div_lt_one hrsq).mpr hcsq) hcrit
    (by rw [heU, sub_self]; exact h0)
  have hnC : -x ∈ C := mem_of_supersolution C h0 hC U hU hp
    (div_nonneg (sq_nonneg c) hrsq.le) ((div_lt_one hrsq).mpr hcsq) hcrit
    (by rw [map_neg, heU, sub_self]; exact h0)
  exact hx (hpoint x hxC hnC)

theorem symmetric_norm_bound {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (C : ConvexCone ℝ F) (h0 : (0 : F) ∈ C) (hC : IsClosed (C : Set F))
    (hpoint : ∀ x ∈ C, -x ∈ C → x = 0)
    (T : F →L[ℝ] F) (hT : ∀ x ∈ C, T x ∈ C) (hsym : T.toLinearMap.IsSymmetric)
    {p : F} (hp : p ∈ interior (C : Set F)) {c : ℝ} (hc : 0 ≤ c)
    (hbound : c • p - T p ∈ C) : ‖T‖ ≤ c := by
  let b := hsym.eigenvectorBasis rfl
  have heig (i : Fin (Module.finrank ℝ F)) : |hsym.eigenvalues rfl i| ≤ c := by
    exact eigenvalue_abs_le C h0 hC hpoint T hT hp hc hbound
      (hsym.hasEigenvector_eigenvectorBasis rfl i).2 (hsym.apply_eigenvectorBasis rfl i)
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have hsq : ‖T x‖^2 ≤ c^2 * ‖x‖^2 := by
    rw [← b.sum_sq_inner_right (T x), ← b.sum_sq_inner_right x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hh : inner ℝ (b i) (T x) = hsym.eigenvalues rfl i * inner ℝ (b i) x := by
      calc
        inner ℝ (b i) (T x) = inner ℝ (T (b i)) x := (hsym (b i) x).symm
        _ = _ := by
          change inner ℝ (T.toLinearMap (hsym.eigenvectorBasis rfl i)) x = _
          rw [hsym.apply_eigenvectorBasis]
          simp [real_inner_smul_left, b]
    rw [hh, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (hsym.eigenvalues rfl i)) hc).mpr (heig i)
  nlinarith [norm_nonneg (T x), norm_nonneg x, mul_nonneg hc (norm_nonneg x)]

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
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe
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
lemma pairHilbertCone_pointed (z : PairHilbert d)
    (hz : z ∈ pairHilbertCone d) (hnz : -z ∈ pairHilbertCone d) : z = 0 := by
  apply (pairEquiv d).injective
  rw [map_zero]
  have hn : -(pairEquiv d z) ∈ pairCone d := by
    change pairEquiv d (-z) ∈ pairCone d at hnz
    rwa [map_neg] at hnz
  exact Prod.ext (psd_pointed _ hz.1 hn.1) (psd_pointed _ hz.2 hn.2)

lemma isClosed_pairHilbertCone : IsClosed (pairHilbertCone d : Set (PairHilbert d)) :=
  isClosed_pairCone.preimage (pairEquiv d).continuous

lemma pairHilbert_interior [NeZero d] {P Q : H d} (hP : P ∈ pd d) (hQ : Q ∈ pd d) :
    (pairEquiv d).symm (P,Q) ∈ interior (pairHilbertCone d : Set (PairHilbert d)) := by
  change (pairEquiv d).symm (P,Q) ∈ interior ((pairEquiv d).toHomeomorph ⁻¹' (pairCone d : Set (Pair d)))
  rw [← (pairEquiv d).toHomeomorph.preimage_interior]
  change pairEquiv d ((pairEquiv d).symm (P,Q)) ∈ interior (pairCone d : Set (Pair d))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact pair_pd_interior hP hQ

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

lemma linConstraint_stationary (X Y P Q : H d) (η : H d →L[ℝ] H d) (ε : ℝ)
    (hPX : sandwich (invH X) P = η Q + ε • (Hermitian.one : H d))
    (hQY : sandwich (invH Y) Q = η P + ε • (Hermitian.one : H d)) :
    linConstraint X Y η (P,Q) = ε • ((Hermitian.one : H d),Hermitian.one) := by
  calc
    _ = (sandwich (invH X) P - η Q, sandwich (invH Y) Q - η P) :=
      linConstraint_apply X Y η (P, Q)
    _ = _ := by
      rw [hPX, hQY]
      apply Prod.ext <;> simp

theorem linConstraint_inverse_norm [NeZero d]
    (X Y P Q : H d) (η : H d →L[ℝ] H d) (hη : SymmetricMap η)
    {ε : ℝ} (hε : 0 < ε)
    (hPle : P ≤ (Hermitian.one : H d)) (hQle : Q ≤ (Hermitian.one : H d))
    (hPX : sandwich (invH X) P = η Q + ε • (Hermitian.one : H d))
    (hQY : sandwich (invH Y) Q = η P + ε • (Hermitian.one : H d))
    (V : Pair d ≃L[ℝ] Pair d) (hV : ∀ z, V z = linConstraint X Y η z)
    (hVpos : ∀ z ∈ pairCone d, V.symm z ∈ pairCone d) :
    ‖onPairHilbert V.symm.toContinuousLinearMap‖ ≤ ε⁻¹ := by
  let e := pairEquiv d
  let W := (e.trans V).trans e.symm
  have hW : LinearMap.IsSymmetric (𝕜 := ℝ) (E := PairHilbert d) W.toLinearEquiv.toLinearMap := by
    convert linConstraint_symmetric X Y η hη using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    change e.symm (V (e z)) = e.symm (linConstraint X Y η (e z))
    rw [hV]
  have hWsym : LinearMap.IsSymmetric (𝕜 := ℝ) (E := PairHilbert d) (onPairHilbert V.symm.toContinuousLinearMap).toLinearMap :=
    hW.toLinearMap_symm
  let E : Pair d := ((Hermitian.one : H d),Hermitian.one)
  have hVE : V (P,Q) = ε • E := by
    rw [hV]
    exact linConstraint_stationary X Y P Q η ε hPX hQY
  have hiE : V.symm E = ε⁻¹ • (P,Q) := by
    apply V.injective
    rw [V.apply_symm_apply, map_smul, hVE, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have hp : e.symm E ∈ interior (pairHilbertCone d : Set (PairHilbert d)) :=
    pairHilbert_interior Matrix.PosDef.one Matrix.PosDef.one
  apply CurrentKS.PositiveMap.symmetric_norm_bound (pairHilbertCone d)
    (show (0 : PairHilbert d) ∈ pairHilbertCone d from ⟨zero_mem_psdCone, zero_mem_psdCone⟩)
    isClosed_pairHilbertCone pairHilbertCone_pointed
    (onPairHilbert V.symm.toContinuousLinearMap)
    (fun z hz => by
      change e (e.symm (V.symm (e z))) ∈ pairCone d
      rw [e.apply_symm_apply]
      exact hVpos _ hz)
    hWsym hp (inv_pos.mpr hε).le
  change e (ε⁻¹ • e.symm E - e.symm (V.symm (e (e.symm E)))) ∈ pairCone d
  simp only [map_sub, map_smul, e.apply_symm_apply, hiE]
  rw [← smul_sub ε⁻¹ E (P,Q)]
  apply CurrentKS.PositiveMap.cone_smul_nonneg (pairCone d)
    ⟨zero_mem_psdCone,zero_mem_psdCone⟩ (inv_pos.mpr hε).le
  exact ⟨(mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hPle),
    (mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hQle)⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SymmetricNormQuadratic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hilbert
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma symmetric_norm_le_of_quadratic (T : E →L[ℝ] E) (hsym : T.IsSymmetric)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, |inner ℝ (T x) x| ≤ c * ‖x‖^2) : ‖T‖ ≤ c := by
  rw [T.norm_eq_iSup_rayleighQuotient hsym]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa [hx] using hc
  · have hn : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
    simp only [RCLike.re_to_real, abs_div, abs_of_pos hn]
    exact (div_le_iff₀ hn).mpr (h x)

end
end CurrentKS.Hilbert

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Hessian
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

attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpacePairHilbert_p0
lemma hessian_symmetric (X Y P Q : H d) :
    LinearMap.IsSymmetric (𝕜 := ℝ) (E := PairHilbert d) (hessian X Y P Q).toLinearMap := by
  intro u v
  change inner ℝ (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp u).1) (WithLp.ofLp v).1 +
    inner ℝ (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp u).2) (WithLp.ofLp v).2 =
    inner ℝ (WithLp.ofLp u).1 (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp v).1) +
    inner ℝ (WithLp.ofLp u).2 (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp v).2)
  congr 1
  · exact jordanCLM_symmetric _ _ _ _
  · exact jordanCLM_symmetric _ _ _ _

lemma hessian_block_bounds (X P : H d) (hX : X ∈ pd d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hXlo : (2*K)⁻¹ • (Hermitian.one : H d) ≤ X)
    (hXhi : X ≤ (K/ε) • (Hermitian.one : H d))
    (hPhi : P ≤ (Hermitian.one : H d))
    (hStat : ε • (Hermitian.one : H d) ≤ sandwich (invH X) P) (U : H d) :
    (2*ε^2/K) * ‖U‖^2 ≤ inner ℝ U (jordanCLM (invH X) (sandwich (invH X) P) U) ∧
    inner ℝ U (jordanCLM (invH X) (sandwich (invH X) P) U) ≤ (16*K^3) * ‖U‖^2 := by
  have hiXlo : (ε/K) • (Hermitian.one : H d) ≤ invH X := by
    simpa only [inv_div] using inverse_lower_of_upper X hX (div_pos hK hε) hXhi
  have hiXhi : invH X ≤ (2*K) • (Hermitian.one : H d) := by
    simpa only [inv_inv] using inverse_upper_of_lower X hX (inv_pos.mpr (by positivity)) hXlo
  have hiPhi : sandwich (invH X) P ≤ (2*K)^2 • (Hermitian.one : H d) :=
    (sandwich_mono (invH X) hPhi).trans
      (square_scalar_bound (invH X) (by positivity) hX.inv.posSemidef hiXhi)
  constructor
  · have hl := jordanCLM_lower (invH X) (sandwich (invH X) P)
      (div_pos hε hK).le hε.le hiXlo hStat U
    convert hl using 1 <;> first | rfl | ring
  · have hu := jordanCLM_upper (invH X) (sandwich (invH X) P)
      (sq_nonneg (2*K)) hX.inv.posSemidef hiXhi hiPhi U
    convert hu using 1 <;> first | rfl | ring

lemma hessian_bounds (X Y P Q : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hXlo : (2*K)⁻¹ • (Hermitian.one : H d) ≤ X)
    (hYlo : (2*K)⁻¹ • (Hermitian.one : H d) ≤ Y)
    (hXhi : X ≤ (K/ε) • (Hermitian.one : H d))
    (hYhi : Y ≤ (K/ε) • (Hermitian.one : H d))
    (hPhi : P ≤ (Hermitian.one : H d)) (hQhi : Q ≤ (Hermitian.one : H d))
    (hStatX : ε • (Hermitian.one : H d) ≤ sandwich (invH X) P)
    (hStatY : ε • (Hermitian.one : H d) ≤ sandwich (invH Y) Q) :
    (∀ u : PairHilbert d, (2*ε^2/K) * ‖u‖^2 ≤ inner ℝ u (hessian X Y P Q u)) ∧
    ‖hessian X Y P Q‖ ≤ 16*K^3 := by
  have hbounds (u : PairHilbert d) :
      (2*ε^2/K) * ‖u‖^2 ≤ inner ℝ u (hessian X Y P Q u) ∧
      inner ℝ u (hessian X Y P Q u) ≤ (16*K^3) * ‖u‖^2 := by
    obtain ⟨h₁,h₂⟩ := hessian_block_bounds X P hX hε hK hXlo hXhi hPhi hStatX (WithLp.ofLp u).1
    obtain ⟨h₃,h₄⟩ := hessian_block_bounds Y Q hY hε hK hYlo hYhi hQhi hStatY (WithLp.ofLp u).2
    have he : inner ℝ u (hessian X Y P Q u) =
        inner ℝ (WithLp.ofLp u).1 (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp u).1) +
        inner ℝ (WithLp.ofLp u).2 (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp u).2) := rfl
    rw [he, WithLp.prod_norm_sq_eq_of_L2]
    dsimp only [WithLp.fst, WithLp.snd]
    constructor <;> nlinarith
  refine ⟨fun u => (hbounds u).1, ?_⟩
  apply CurrentKS.Hilbert.symmetric_norm_le_of_quadratic (hessian X Y P Q)
    (hessian_symmetric X Y P Q) (by positivity)
  intro u
  rw [real_inner_comm]
  have hn : 0 ≤ inner ℝ u (hessian X Y P Q u) :=
    (by positivity : 0 ≤ (2*ε^2/K) * ‖u‖^2).trans (hbounds u).1
  rw [abs_of_nonneg hn]
  exact (hbounds u).2

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

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormSq
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

attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert_p1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_1_p1
lemma norm_one_sq : ‖(Hermitian.one : H d)‖^2 = (d : ℝ) := by
  rw [← real_inner_self_eq_norm_sq,inner_one,realTrace_one]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert_p1
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpacePairHilbert_p1
lemma identityPair_norm_sq : ‖identityPair d‖^2 = 2*(d : ℝ) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(Hermitian.one : H d)‖^2+‖(Hermitian.one : H d)‖^2 = _
  rw [norm_one_sq]
  ring

lemma norm_sq_le_trace_of_psd_le_one (P : H d) (hP : P ∈ psdCone d) (hPle : P ≤ Hermitian.one) :
    ‖P‖^2 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace P := by
  have hh := inner_nonneg_of_psd P (Hermitian.one-P) hP
    ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hPle))
  rw [inner_sub_right,inner_one',real_inner_self_eq_norm_sq] at hh
  linarith

lemma trace_pair_norm (P Q : H d) (hP : P ∈ psdCone d) (hQ : Q ∈ psdCone d)
    (htr : _root_.OAI.CurrentKS.Hermitian.realTrace P+_root_.OAI.CurrentKS.Hermitian.realTrace Q=1) :
    P ≤ Hermitian.one ∧ Q ≤ Hermitian.one ∧
    ‖(pairEquiv d).symm (P,Q)‖ ≤ 1 ∧
    1 ≤ 2*(d : ℝ)*‖(pairEquiv d).symm (P,Q)‖^2 := by
  have hPn := realTrace_nonneg hP
  have hQn := realTrace_nonneg hQ
  have hPle : P ≤ Hermitian.one := (trace_bound_above hP).trans (by
    simpa only [one_smul] using scalar_one_mono (d := d) (show _root_.OAI.CurrentKS.Hermitian.realTrace P ≤ 1 by linarith))
  have hQle : Q ≤ Hermitian.one := (trace_bound_above hQ).trans (by
    simpa only [one_smul] using scalar_one_mono (d := d) (show _root_.OAI.CurrentKS.Hermitian.realTrace Q ≤ 1 by linarith))
  have hn2 : ‖(pairEquiv d).symm (P,Q)‖^2 ≤ 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖P‖^2+‖Q‖^2 ≤ 1
    have h₁ := norm_sq_le_trace_of_psd_le_one P hP hPle
    have h₂ := norm_sq_le_trace_of_psd_le_one Q hQ hQle
    linarith
  have hi : inner ℝ (identityPair d) ((pairEquiv d).symm (P,Q)) = 1 := by
    change inner ℝ (Hermitian.one : H d) P+inner ℝ (Hermitian.one : H d) Q = 1
    rwa [inner_one,inner_one]
  have hc := abs_real_inner_le_norm (identityPair d) ((pairEquiv d).symm (P,Q))
  rw [hi,abs_one] at hc
  have hc2 := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) hc 2
  rw [mul_pow,identityPair_norm_sq,one_pow] at hc2
  refine ⟨hPle,hQle,?_,hc2⟩
  nlinarith [norm_nonneg ((pairEquiv d).symm (P,Q))]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_1_p1
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p2
theorem full_jacobian_inverse_bound_oai [NeZero d] (X Y P Q : H d)
    (η : H d →L[ℝ] H d) (hηpos : ∀ A ∈ psdCone d,η A ∈ psdCone d)
    (hηsym : SymmetricMap η) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hP : P ∈ pd d) (hQ : Q ∈ pd d) {ε : ℝ} (hε : 0 < ε)
    (htr : _root_.OAI.CurrentKS.Hermitian.realTrace P+_root_.OAI.CurrentKS.Hermitian.realTrace Q=1)
    (hStatX : sandwich (invH X) P = η Q+ε • (Hermitian.one : H d))
    (hStatY : sandwich (invH Y) Q = η P+ε • (Hermitian.one : H d))
    (hXlo : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ X)
    (hYlo : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ Y)
    (hXhi : X ≤ (100/ε) • (Hermitian.one : H d))
    (hYhi : Y ≤ (100/ε) • (Hermitian.one : H d)) :
    ∃ J : Vars d ≃L[ℝ] Vars d,
      (∀ v,J v = CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint X Y η)) (hessian X Y P Q) v) ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ 10^18*((d : ℝ)+1)*(1+ε⁻¹)^4 := by
  have hPX : P = sandwich X (η Q)+ε • sandwich X (Hermitian.one : H d) := by
    rw [← sandwich_smul,← sandwich_add,← hStatX,sandwich_inverse_cancel _ _ hX]
  have hQY : Q = sandwich Y (η P)+ε • sandwich Y (Hermitian.one : H d) := by
    rw [← sandwich_smul,← sandwich_add,← hStatY,sandwich_inverse_cancel _ _ hY]
  obtain ⟨V,hV,hVpos⟩ := linConstraint_positive_inverse X Y P Q η hηpos hX hY hP hQ hε hPX hQY
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
  refine ⟨J, fun v => ?_, ?_⟩
  · exact (hJ v).trans (congrArg (fun T =>
      CurrentKS.KKT.jacobian (identityPair d) T (hessian X Y P Q) v) he)
  obtain ⟨hPle,hQle,hnorm,hbelow⟩ := trace_pair_norm P Q hP.posSemidef hQ.posSemidef htr
  have hB : ‖L.symm.toContinuousLinearMap‖ ≤ ε⁻¹ :=
    linConstraint_inverse_norm X Y P Q η hηsym hε hPle hQle hStatX hStatY V hV hVpos
  have hLe : L ((pairEquiv d).symm (P,Q)) = ε • identityPair d := by
    change (pairEquiv d).symm (V ((pairEquiv d) ((pairEquiv d).symm (P,Q)))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply,hV,linConstraint_stationary X Y P Q η ε hStatX hStatY]
    exact (map_smul (pairEquiv d).symm ε _)
  have hiE : L.symm (identityPair d) = ε⁻¹ • (pairEquiv d).symm (P,Q) := by
    apply L.injective
    rw [L.apply_symm_apply,map_smul,hLe,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
  have hnE : ‖L.symm (identityPair d)‖ = ε⁻¹*‖(pairEquiv d).symm (P,Q)‖ := by
    rw [hiE,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  have hBe : ‖L.symm (identityPair d)‖ ≤ ε⁻¹ := by
    rw [hnE]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hε.le)
  have hεX : ε • (Hermitian.one : H d) ≤ sandwich (invH X) P := by
    rw [hStatX]
    exact le_add_of_nonneg_left (psd_nonneg (hηpos _ hQ.posSemidef))
  have hεY : ε • (Hermitian.one : H d) ≤ sandwich (invH Y) Q := by
    rw [hStatY]
    exact le_add_of_nonneg_left (psd_nonneg (hηpos _ hP.posSemidef))
  have hess := hessian_bounds X Y P Q hX hY hε (show (0:ℝ)<100 by norm_num)
    (by convert hXlo using 1; norm_num) (by convert hYlo using 1; norm_num)
    hXhi hYhi hPle hQle hεX hεY
  have hd : (0:ℝ)<d := by exact_mod_cast NeZero.pos d
  have hden : 1/(100*(d : ℝ)) ≤ inner ℝ (L.symm (identityPair d))
      (hessian X Y P Q (L.symm (identityPair d))) := by
    apply le_trans _ (hess.1 _)
    rw [hnE]
    have heq : (2*ε^2/100)*(ε⁻¹*‖(pairEquiv d).symm (P,Q)‖)^2 =
        (2/100 : ℝ)*‖(pairEquiv d).symm (P,Q)‖^2 := by field_simp [hε.ne']
    rw [heq]
    apply (div_le_iff₀ (show (0:ℝ)<100*d by positivity)).mpr
    nlinarith only [hbelow]
  apply CurrentKS.KKT.jacobian_inverse_norm_100 (identityPair d) L hs (hessian X Y P Q) J hJ
    hε hd hB hBe _ hden
  convert hess.2 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

end
end CurrentKS.Variational

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.Variational.full_jacobian_inverse_bound_oai := @OAI.CurrentKS.Variational.full_jacobian_inverse_bound_oai
