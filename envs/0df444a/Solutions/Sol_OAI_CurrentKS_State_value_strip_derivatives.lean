-- Prove2me | solution 1 for OAI.CurrentKS.State.value_strip_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:58:32.801121+00:00
-- url     : https://prove2.me/submissions/8e521527-e415-4140-a56a-3bf07480e57a

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_State_kkt_strip_jet
import Theorems.Thm_OAI_CurrentKS_Variational_exists_smooth_kkt_branch
import Theorems.Thm_OAI_CurrentKS_Variational_full_jacobian_inverse_bound
import Theorems.Thm_OAI_CurrentKS_Variational_kkt
import Theorems.Thm_OAI_CurrentKS_Variational_kkt_curve_derivatives

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ScalarPsi
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

lemma base_pos {x : ℝ} (hx : |x| < 1) : 0 < 1-x^2 := by
  have h := (abs_lt.mp hx)
  nlinarith [sq_nonneg x]

lemma contDiffAt_psi {x : ℝ} (hx : |x| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n psi x := by
  exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (base_pos hx))).comp x
    (contDiffAt_const.sub (contDiffAt_id.pow 2))

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_Kappa₁
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

lemma strip_interior {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2) : |x| < 1 := by linarith

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_NormMultilinearTwo
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Implicit
noncomputable section
open Filter
open scoped Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma iteratedDeriv_clm {c : ℝ → E} {a : ℝ} {n : ℕ} (hc : ContDiffAt ℝ n c a)
    (L : E →L[ℝ] G) : iteratedDeriv n (L ∘ c) a = L (iteratedDeriv n c a) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_left hc le_rfl]
  rfl

end
end CurrentKS.Implicit

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

lemma realTrace_mono {A B : H d} (hab : A ≤ B) : realTrace A ≤ realTrace B := by
  have hh := realTrace_nonneg (show B-A ∈ psdCone d from hab)
  simpa using hh

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

lemma inner_right_one (A : H d) : inner ℝ A (one : H d) = realTrace A := by
  rw [real_inner_comm, inner_one]

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

lemma psd_sum {ι : Type*} (s : Finset ι) (A : ι → H d) (hA : ∀ i ∈ s, A i ∈ psdCone d) :
    (∑ i ∈ s, A i) ∈ psdCone d := by
  exact (mem_psd_iff_nonneg _).mpr (Finset.sum_nonneg fun i hi => (mem_psd_iff_nonneg _).mp (hA i hi))

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich2
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

lemma trace_bounds_of_feasible [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {z : Point d} (hz : z ∈ feasible S η) :
    0 ≤ z.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have htr₁ := realTrace_mono h₁
  have htr₂ := realTrace_mono h₂
  have hiX := realTrace_nonneg (A := invH z.2.1) hX.inv.posSemidef
  have hiY := realTrace_nonneg (A := invH z.2.2) hY.inv.posSemidef
  have heX := realTrace_nonneg (hη _ hX.posSemidef)
  have heY := realTrace_nonneg (hη _ hY.posSemidef)
  simp only [realTrace_add, realTrace_sub, realTrace_smul, realTrace_one] at htr₁ htr₂
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  refine ⟨?_, realTrace_nonneg hX.posSemidef, realTrace_nonneg hY.posSemidef⟩
  nlinarith

lemma objective_bounds [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) {z : Point d} (hz : z ∈ feasible S η)
    (hf : objective ε z ≤ K) :
    0 ≤ z.1 ∧ z.1 ≤ K ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ≤ K / ε ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 ≤ K / ε := by
  obtain ⟨ht, hX, hY⟩ := trace_bounds_of_feasible S η hη hz
  simp only [objective, realTrace_add] at hf
  refine ⟨ht, ?_, (le_div_iff₀ hε).mpr ?_, (le_div_iff₀ hε).mpr ?_⟩ <;>
    nlinarith [mul_nonneg hε.le hX, mul_nonneg hε.le hY]

lemma inverse_bounds (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (ht : z.1 ≤ K) :
    invH z.2.1 ≤ (2*K) • (Hermitian.one : H d) ∧ invH z.2.2 ≤ (2*K) • (Hermitian.one : H d) := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have heX : 0 ≤ η z.2.1 := psd_nonneg (hη _ hX.posSemidef)
  have heY : 0 ≤ η z.2.2 := psd_nonneg (hη _ hY.posSemidef)
  have htk : z.1 • (Hermitian.one : H d) ≤ K • (Hermitian.one : H d) := scalar_one_mono ht
  constructor
  · have hh : invH z.2.1 + S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heY).trans (h₁.trans htk)
    have hx := add_le_add hh (neg_le_neg hS₁)
    convert hx using 1 <;> first | rfl | module
  · have hh : invH z.2.2 - S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heX).trans (h₂.trans htk)
    have hx := add_le_add hh hS₂
    convert hx using 1 <;> first | rfl | module

lemma sublevel_box [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (hf : objective ε z ≤ K) :
    z.1 ∈ Icc 0 K ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.1 ∧ z.2.1 ≤ (K/ε) • (Hermitian.one : H d)) ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.2 ∧ z.2.2 ≤ (K/ε) • (Hermitian.one : H d)) := by
  obtain ⟨ht, htK, htrX, htrY⟩ := objective_bounds S η hη hε hz hf
  obtain ⟨hXi, hYi⟩ := inverse_bounds S η hη hS₁ hS₂ hz htK
  obtain ⟨hX,hY,-,-⟩ := (feasible_iff S η z).mp hz
  have hmul : ∀ r s : ℝ, r ≤ s → r • (Hermitian.one : H d) ≤ s • (Hermitian.one : H d) :=
    fun _ _ h => scalar_one_mono h
  exact ⟨⟨ht,htK⟩,
    ⟨inverse_bound_below (by positivity) hX hXi,
      (trace_bound_above hX.posSemidef).trans (hmul _ _ htrX)⟩,
    ⟨inverse_bound_below (by positivity) hY hYi,
      (trace_bound_above hY.posSemidef).trans (hmul _ _ htrY)⟩⟩

end
end CurrentKS.Variational

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r52faa3_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma eta_apply (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z : H d) :
    eta c A x Z = ∑ i, (c * psi (x i)) • sandwich (A i) Z := by
  simp [eta]

lemma psi_bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ psi x ∧ psi x ≤ 1 := by
  have hr : 0 ≤ 1-x^2 := by have hh := abs_le.mp hx; nlinarith
  exact ⟨Real.rpow_nonneg hr _, Real.rpow_le_one hr (by nlinarith [sq_nonneg x]) (by norm_num)⟩

lemma eta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {x : Coordinates N} (hx : Cube x) :
    ∀ Z ∈ psdCone d, eta c A x Z ∈ psdCone d := by
  intro Z hZ
  rw [eta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (psi_bounds (hx i)).1)

lemma eta_symmetric (c : ℝ) (A : Fin N → H d) (x : Coordinates N) : SymmetricMap (eta c A x) := by
  intro U V
  change inner ℝ U (eta c A x V) = inner ℝ (eta c A x U) V
  simp only [eta_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (c*psi (x i)) * inner ℝ U (sandwich (A i) V) :=
      real_inner_smul_right U (sandwich (A i) V) (c*psi (x i))
    _ = (c*psi (x i)) * inner ℝ (sandwich (A i) U) V := by rw [inner_sandwich]
    _ = _ := (real_inner_smul_left (sandwich (A i) U) V (c*psi (x i))).symm

end CurrentKS.State

end

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

end

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

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormTCoord
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p1
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPair
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPair
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpacePair
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert_p2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpacePairHilbert_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_1_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_1_p2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p3
lemma norm_tCoord_le : norm (E := Vars d →L[ℝ] ℝ) (tCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact norm_fst_le z
lemma norm_uCoord_le : norm (E := Vars d →L[ℝ] PairHilbert d) (uCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (norm_fst_le z.2).trans (norm_snd_le z)

lemma norm_pairEquiv_symm_le : norm (E := Pair d →L[ℝ] PairHilbert d) (pairEquiv d).symm.toContinuousLinearMap ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  have he : ‖(pairEquiv d).symm z‖^2 = ‖z.1‖^2+‖z.2‖^2 := WithLp.prod_norm_sq_eq_of_L2 _
  have h₁ := pow_le_pow_left₀ (norm_nonneg z.1) (norm_fst_le z) 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg z.2) (norm_snd_le z) 2
  change ‖(pairEquiv d).symm z‖ ≤ 2*‖z‖
  nlinarith [norm_nonneg ((pairEquiv d).symm z),norm_nonneg z]

lemma norm_identityPair_le_dimension : ‖identityPair d‖ ≤ 2*((d:ℝ)+1) := by
  have hn := identityPair_norm_sq (d := d)
  have hd := Nat.cast_nonneg (α := ℝ) d
  nlinarith [norm_nonneg (identityPair d)]

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormPsdScalar
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

attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_1_p0
lemma norm_psd_le_scalar (U : H d) (hU : U ∈ psdCone d) {r : ℝ} (hr : 0 ≤ r)
    (hUr : U ≤ r • Hermitian.one) : ‖U‖ ≤ r*((d:ℝ)+1) := by
  have ht := realTrace_mono hUr
  rw [Hermitian.realTrace_smul,Hermitian.realTrace_one] at ht
  have hh := inner_nonneg_of_psd U (r • Hermitian.one-U) hU
    ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hUr))
  rw [inner_sub_right,real_inner_smul_right U (Hermitian.one : H d) r,inner_one',real_inner_self_eq_norm_sq] at hh
  have hnt : ‖U‖^2 ≤ r^2*d := by nlinarith [mul_le_mul_of_nonneg_left ht hr]
  have hd : (0:ℝ)≤d := Nat.cast_nonneg d
  have hd' : (d:ℝ)≤(d+1)^2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hd' (sq_nonneg r)
  have hn : 0 ≤ r*((d:ℝ)+1) := by positivity
  nlinarith [norm_nonneg U]

lemma norm_pair_le_two (X Y : H d) {r : ℝ} (hX : ‖X‖ ≤ r) (hY : ‖Y‖ ≤ r) :
    ‖(pairEquiv d).symm (X,Y)‖ ≤ 2*r := by
  exact ((pairEquiv d).symm.toContinuousLinearMap.le_opNorm (X,Y)).trans
    (mul_le_mul norm_pairEquiv_symm_le (by simpa only [Prod.norm_def,max_le_iff] using And.intro hX hY)
      (norm_nonneg _) (by norm_num))

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_1_p0
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p1
lemma norm_pack_bounds (z : Point d) (P Q : H d) {ε : ℝ} (hε : 0 < ε)
    (ht : z.1 ∈ Icc 0 100)
    (hX : z.2.1 ∈ pd d) (hY : z.2.2 ∈ pd d)
    (hXhi : z.2.1 ≤ (100/ε) • (Hermitian.one : H d))
    (hYhi : z.2.2 ≤ (100/ε) • (Hermitian.one : H d))
    (hP : P ∈ pd d) (hQ : Q ∈ pd d) (htr : _root_.OAI.CurrentKS.Hermitian.realTrace P+_root_.OAI.CurrentKS.Hermitian.realTrace Q=1) :
    ‖pack z P Q‖ ≤ 200+(200/ε)*((d:ℝ)+1) := by
  have hx := norm_psd_le_scalar z.2.1 hX.posSemidef (by positivity) hXhi
  have hy := norm_psd_le_scalar z.2.2 hY.posSemidef (by positivity) hYhi
  have hu := norm_pair_le_two z.2.1 z.2.2 hx hy
  have hp := (trace_pair_norm P Q hP.posSemidef hQ.posSemidef htr).2.2.1
  have hr : 0 ≤ (200/ε)*((d:ℝ)+1) := by positivity
  change max |z.1| (max ‖(pairEquiv d).symm z.2‖ ‖(pairEquiv d).symm (P,Q)‖) ≤ _
  rw [max_le_iff,max_le_iff,abs_of_nonneg ht.1]
  constructor
  · linarith [ht.2]
  constructor
  · have he : 2*((100/ε)*((d:ℝ)+1)) = (200/ε)*((d:ℝ)+1) := by ring
    rw [he] at hu
    linarith
  · linarith

theorem bounded_optimizer_data [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hηpos : ∀ X ∈ psdCone d,η X ∈ psdCone d) (hηsym : SymmetricMap η)
    {ε : ℝ} (hε : 0 < ε) (hSlo : -(100:ℝ) • (Hermitian.one : H d) ≤ S)
    (hShi : S ≤ (100:ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible S η) (hz100 : objective ε z ≤ 100)
    (hmin : ∀ w ∈ feasible S η,objective ε z ≤ objective ε w) :
    ∃ P Q : H d, ∃ J : Vars d ≃L[ℝ] Vars d,
      P ∈ pd d ∧ Q ∈ pd d ∧ ‖P‖ ≤ 1 ∧ ‖Q‖ ≤ 1 ∧
      kktSystem ε S η (pack z P Q)=0 ∧
      (∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint z.2.1 z.2.2 η)) (hessian z.2.1 z.2.2 P Q) u) ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4 ∧
      ‖pack z P Q‖ ≤ 200+(200/ε)*((d:ℝ)+1) ∧
      ‖invH z.2.1‖ ≤ 200*((d:ℝ)+1) ∧ ‖invH z.2.2‖ ≤ 200*((d:ℝ)+1) := by
  obtain ⟨P,Q,hP,hQ,hPle,hQle,htr,hPX,hQY,ht,hx,hy⟩ :=
    kkt S η hηpos hηsym hε hSlo hShi z hz hmin
  have hb := sublevel_box S η hηpos hε (by norm_num : (0:ℝ)<100) hSlo hShi hz hz100
  have hhX : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ z.2.1 := by convert hb.2.1.1 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  have hhY : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ z.2.2 := by convert hb.2.2.1 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  obtain ⟨J,hJ,hJi⟩ := full_jacobian_inverse_bound z.2.1 z.2.2 P Q η hηpos hηsym
    hz.1.1 hz.1.2 hP hQ hε htr hx hy hhX hhY hb.2.1.2 hb.2.2.2
  have hPn := norm_sq_le_trace_of_psd_le_one P hP.posSemidef hPle
  have hQn := norm_sq_le_trace_of_psd_le_one Q hQ.posSemidef hQle
  have hnP : ‖P‖ ≤ 1 := by nlinarith [realTrace_nonneg hQ.posSemidef,norm_nonneg P]
  have hnQ : ‖Q‖ ≤ 1 := by nlinarith [realTrace_nonneg hP.posSemidef,norm_nonneg Q]
  refine ⟨P,Q,J,hP,hQ,hnP,hnQ,pack_kkt ε S η z P Q htr ht hx hy,hJ,hJi,
    norm_pack_bounds z P Q hε hb.1 hz.1.1 hz.1.2 hb.2.1.2 hb.2.2.2 hP hQ htr,?_,?_⟩
  · apply norm_psd_le_scalar _ hz.1.1.inv.posSemidef (by norm_num)
    simpa only [inv_inv] using inverse_upper_of_lower z.2.1 hz.1.1
      (by norm_num : (0:ℝ)<(200:ℝ)⁻¹) hhX
  · apply norm_psd_le_scalar _ hz.1.2.inv.posSemidef (by norm_num)
    simpa only [inv_inv] using inverse_upper_of_lower z.2.2 hz.1.2
      (by norm_num : (0:ℝ)<(200:ℝ)⁻¹) hhY
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_JetBoundProjection
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdSubtypeMatMemSubmoduleRealH
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealProdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealProdPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p0
local instance instNormedAddCommGroupContinuousLinearMapRealIdVars_r52faa3_1 : NormedAddCommGroup (E →L[ℝ] Vars d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdVars_r52faa3_1 : NormedSpace ℝ (E →L[ℝ] Vars d) := inferInstance
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_2_r52faa3_1 : NormedAddCommGroup (E →L[ℝ] H d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH_2_r52faa3_1 : NormedSpace ℝ (E →L[ℝ] H d) := inferInstance
lemma norm_tracePair_le {B : ℝ} (hd : (d:ℝ)+1 ≤ B) :
    ‖innerSL ℝ (identityPair d)‖ ≤ 2*B := by
  have hB : 0 ≤ B := le_trans (by positivity) hd
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  exact (norm_inner_le_norm (𝕜 := ℝ) (identityPair d) v).trans
    (mul_le_mul_of_nonneg_right ((norm_identityPair_le_dimension (d := d)).trans (show 2*((d:ℝ)+1) ≤ 2*B by linarith)) (norm_nonneg v))

end
end CurrentKS.Variational

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

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ValueBranch
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p7
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p7
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p7
theorem exists_value_branch [NeZero d] (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d) (b : E)
    (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
    (hηsym : ∀ᶠ a in 𝓝 b, SymmetricMap (η a)) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hP : mCoord d z ∈ pd d) (hQ : nCoord d z ∈ pd d)
    (hzero : kktSystem ε (S b) (η b) z=0)
    (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ u, J u=CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u) :
    ∃ g : E → Vars d, g b=z ∧ ContDiffAt ℝ ∞ g b ∧
      (∀ᶠ a in 𝓝 b,kktSystem ε (S a) (η a) (g a)=0) ∧
      (fun a => value ε (S a) (η a)) =ᶠ[𝓝 b] fun a => objective ε (unpack (g a)) := by
  obtain ⟨f,hf,hfc,hfe⟩ := exists_smooth_kkt_branch ε (S b,η b) z hX hY J hJ
  let g : E → Vars d := fun a => f (S a,η a)
  have hg : g b=z := hf
  have hgc : ContDiffAt ℝ ∞ g b := hfc.comp b (hS.prodMk hη)
  have hge : ∀ᶠ a in 𝓝 b,kktSystem ε (S a) (η a) (g a)=0 := by
    filter_upwards [(hS.continuousAt.prodMk hη.continuousAt).eventually hfe] with a ha
    exact ha.trans hzero
  have hXg : ∀ᶠ a in 𝓝 b,xCoord d (g a) ∈ pd d := by
    apply ((xCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change xCoord d (g b) ∈ pd d
    rw [hg]
    exact hX
  have hYg : ∀ᶠ a in 𝓝 b,yCoord d (g a) ∈ pd d := by
    apply ((yCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change yCoord d (g b) ∈ pd d
    rw [hg]
    exact hY
  have hPg : ∀ᶠ a in 𝓝 b,mCoord d (g a) ∈ pd d := by
    apply ((mCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change mCoord d (g b) ∈ pd d
    rw [hg]
    exact hP
  have hQg : ∀ᶠ a in 𝓝 b,nCoord d (g a) ∈ pd d := by
    apply ((nCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change nCoord d (g b) ∈ pd d
    rw [hg]
    exact hQ
  refine ⟨g,hg,hgc,hge,?_⟩
  filter_upwards [hηsym,hge,hXg,hYg,hPg,hQg] with a ha he hx hy hp hq
  exact value_eq_of_system ε (S a) (η a) ha (g a) hx hy hp.posSemidef hq.posSemidef he

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ObjectiveVarsCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert_1
private local instance instTopologicalSpacePairHilbert_r52faa3_1 : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_3
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_3
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p4
lemma objectiveVarsCLM_apply (ε : ℝ) (z : Vars d) :
    objectiveVarsCLM ε z = objective ε (unpack z) := by
  change tCoord d z + ε * inner ℝ (identityPair d) (uCoord d z) =
    tCoord d z + ε * _root_.OAI.CurrentKS.Hermitian.realTrace (xCoord d z + yCoord d z)
  congr 1
  congr 1
  change inner ℝ (Hermitian.one : H d) (xCoord d z)+
    inner ℝ (Hermitian.one : H d) (yCoord d z) = _
  rw [Hermitian.inner_one,Hermitian.inner_one,Hermitian.realTrace_add]

lemma norm_objectiveVarsCLM (ε : ℝ) :
    ‖objectiveVarsCLM (d := d) ε‖ ≤ 1+|ε| *(2*((d:ℝ)+1)) := by
  have ht := norm_tracePair_le (d := d) (le_refl ((d:ℝ)+1))
  let t : Vars d →L[ℝ] ℝ := tCoord d
  let L : Vars d →L[ℝ] ℝ := (innerSL ℝ (identityPair d)).comp (uCoord d)
  change ‖t+ε • L‖ ≤ _
  calc
    _ ≤ ‖t‖+‖ε • L‖ := norm_add_le _ _
    _ = ‖t‖+|ε| *‖L‖ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ 1+|ε| *(2*((d:ℝ)+1)*1) := by
      exact add_le_add norm_tCoord_le (mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul ht norm_uCoord_le (norm_nonneg _) (by positivity))) (abs_nonneg ε))
    _ = _ := by ring

theorem exists_value_curve [NeZero d] (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
    (b h : E) (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
    (hηsym : ∀ᶠ a in 𝓝 b,SymmetricMap (η a)) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hP : mCoord d z ∈ pd d) (hQ : nCoord d z ∈ pd d)
    (hzero : kktSystem ε (S b) (η b) z=0) (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u) :
    ∃ c : ℝ → Vars d, ContDiffAt ℝ 3 c 0 ∧ c 0=z ∧
      (fun t => kktSystem ε (S (b+t • h)) (η (b+t • h)) (c t)) =ᶠ[𝓝 0] (fun _ => 0) ∧
      (fun t => value ε (S (b+t • h)) (η (b+t • h))) =ᶠ[𝓝 0] (objectiveVarsCLM ε ∘ c) := by
  obtain ⟨g,hg,hgc,hge,hgv⟩ := exists_value_branch ε S η b hS hη hηsym z hX hY hP hQ hzero J hJ
  let line := fun t : ℝ => b+t • h
  have hl : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hl0 : line 0=b := by simp [line]
  let c := g ∘ line
  have hl3 : ContDiff ℝ 3 line := contDiff_infty.mp hl 3
  have hc : ContDiffAt ℝ 3 c 0 := by
    have hgg : ContDiffAt ℝ 3 g (line 0) := by rw [hl0]; exact contDiffAt_infty.mp hgc 3
    exact hgg.comp 0 hl3.contDiffAt
  have hc0 : c 0=z := by change g (line 0)=z; rw [hl0,hg]
  have hlt : Tendsto line (𝓝 0) (𝓝 b) := by
    have hx : Tendsto line (𝓝 0) (𝓝 (line 0)) := hl.continuous.continuousAt
    rw [hl0] at hx
    exact hx
  refine ⟨c,hc,hc0,hlt.eventually hge,?_⟩
  have hh := hlt.eventually hgv
  filter_upwards [hh] with t ht
  exact ht.trans (objectiveVarsCLM_apply ε (g (line t))).symm

lemma norm_iteratedDeriv_germ_linear {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : ℝ → G) (hc : ContDiffAt ℝ 3 c 0) (L : G →L[ℝ] ℝ) (f : ℝ → ℝ)
    (he : f =ᶠ[𝓝 0] (L ∘ c)) (k : ℕ) (hk : k ≤ 3) :
    |iteratedDeriv k f 0| ≤ ‖L‖ * ‖iteratedDeriv k c 0‖ := by
  rw [he.iteratedDeriv_eq k]
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  rw [CurrentKS.Implicit.iteratedDeriv_clm (hc.of_le hk') L]
  exact L.le_opNorm _

theorem value_curve_derivatives [NeZero d] (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
    (b h : E) (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
    (hηsym : ∀ᶠ a in 𝓝 b,SymmetricMap (η a)) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hP : mCoord d z ∈ pd d) (hQ : nCoord d z ∈ pd d)
    (hzero : kktSystem ε (S b) (η b) z=0) (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hh : ‖h‖ ≤ 1)
    (hFB : JetBound (fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2) (b,z) D) :
    let f := fun t : ℝ => value ε (S (b+t • h)) (η (b+t • h))
    |iteratedDeriv 2 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*(A*D*(1+A*D)^2) ∧
    |iteratedDeriv 3 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*
      (A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2))) := by
  obtain ⟨c,hc,hc0,heq,hv⟩ := exists_value_curve ε S η b h hS hη hηsym z hX hY hP hQ hzero J hJ
  have hb := kkt_curve_derivatives ε S η b h (contDiffAt_infty.mp hS 3)
    (contDiffAt_infty.mp hη 3) z hX hY J hJ hA hD hJinv hh hFB c hc hc0 heq
  constructor
  · exact (norm_iteratedDeriv_germ_linear c hc (objectiveVarsCLM ε) _ hv 2 (by norm_num)).trans
      (mul_le_mul (norm_objectiveVarsCLM ε) hb.1 (norm_nonneg _) (by positivity))
  · exact (norm_iteratedDeriv_germ_linear c hc (objectiveVarsCLM ε) _ hv 3 (by norm_num)).trans
      (mul_le_mul (norm_objectiveVarsCLM ε) hb.2 (norm_nonneg _) (by positivity))

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
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

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupVars
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealVars
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH
lemma contDiff_S (A : Fin N → H d) {n : WithTop ℕ∞} : ContDiff ℝ n (S A) := by
  apply ContDiff.sum
  intro i _
  exact (contDiff_apply ℝ ℝ i).smul contDiff_const

lemma contDiffAt_eta (c : ℝ) (A : Fin N → H d) {x : Coordinates N}
    (hx : ∀ i, |x i| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n (eta c A) x := by
  apply ContDiffAt.sum
  intro i _
  have hp : ContDiffAt ℝ n (fun y : Coordinates N => psi (y i)) x :=
    (contDiffAt_psi (hx i)).comp x (contDiffAt_apply ℝ ℝ i x)
  have hc : ContDiffAt ℝ n (fun _ : Coordinates N => c) x := contDiffAt_const
  exact (hc.mul hp).smul (show ContDiffAt ℝ n (fun _ : Coordinates N => sandwichCLM (A i)) x from contDiffAt_const)

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

attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceVars
theorem value_strip_derivatives_oai [NeZero d] (A : Fin N → H d)
    (_hA : ∀ i,A i ∈ psdCone d) (hAn : ∀ i,‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x h : Coordinates N)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (hh : ‖h‖ ≤ 1)
    (hlo : -(100:ℝ) • (Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ (100:ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S₀+S A x) (eta 384 A x)) (hz100 : objective ε z ≤ 100)
    (hmin : ∀ w ∈ feasible (S₀+S A x) (eta 384 A x),objective ε z ≤ objective ε w) :
    let B := coarseBudget d N ε σ
    let Jb := 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4
    let D := 300*B^5
    let f := fun t : ℝ => value ε (S₀+S A (x+t • h)) (eta 384 A (x+t • h))
    |iteratedDeriv 2 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*(Jb*D*(1+Jb*D)^2) ∧
    |iteratedDeriv 3 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*
      (Jb*D*((1+Jb*D)^3+3*(1+Jb*D)*(Jb*D*(1+Jb*D)^2))) := by
  have hB : 0 < coarseBudget d N ε σ :=
    lt_of_lt_of_le zero_lt_one (coarseBudget_bounds (d:=d) (N:=N) hε hσ).1
  have hxi (i : Fin N) : |x i| < 1 := strip_interior hσ (hx i)
  have hpos := eta_positive (by norm_num : (0:ℝ)≤384) A (fun i => (hxi i).le)
  obtain ⟨P,Q,J,hP,hQ,hPn,hQn,hzero,hJ,hJi,hzB,hiX,hiY⟩ :=
    bounded_optimizer_data (S₀+S A x) (eta 384 A x) hpos (eta_symmetric 384 A x) hε hlo hhi z hz hz100 hmin
  apply value_curve_derivatives ε (fun y => S₀+S A y) (eta 384 A) x h
    (contDiffAt_const.add (contDiff_S A).contDiffAt) (contDiffAt_eta 384 A hxi)
    (Filter.Eventually.of_forall (fun y => eta_symmetric 384 A y)) (pack z P Q)
    hz.1.1 hz.1.2
    hP hQ hzero J
    hJ
    (by positivity) (by positivity) hJi hh
  exact kkt_strip_jet A hAn S₀ hS₀ x hε hσ hx (pack z P Q)
    hz.1.1 hz.1.2 hzB
    hiX hiY
    hPn hQn
end
end CurrentKS.State

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.State.value_strip_derivatives_oai := @OAI.CurrentKS.State.value_strip_derivatives_oai
