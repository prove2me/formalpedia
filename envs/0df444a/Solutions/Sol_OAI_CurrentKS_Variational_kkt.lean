-- Prove2me | solution 1 for OAI.CurrentKS.Variational.kkt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:50:20.545081+00:00
-- url     : https://prove2.me/submissions/b1cdf5d1-06b3-4eb4-9196-b12772d64a9e

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

theorem positive_dual_matrix (p : StrongDual ℝ (H d))
    (hp : ∀ A ∈ psdCone d, 0 ≤ p A) :
    ∃ P : H d, P ∈ psdCone d ∧ ∀ A, p A = inner ℝ P A := by
  let b := stdOrthonormalBasis ℝ (H d)
  let P : H d := ∑ i, p (b i) • b i
  have he (A : H d) : inner ℝ P A = p A := by
    change inner ℝ (∑ i, p (b i) • b i : H d) A = p A
    rw [sum_inner]
    simp only [inner_smul_leftH]
    nth_rw 2 [← b.sum_repr' A]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul, smul_eq_mul, mul_comm]
  exact ⟨P, psd_of_inner_nonneg P (fun A hA => (he A).symm ▸ hp A hA),
    fun A => (he A).symm⟩

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

lemma pd_smul {A : H d} (hA : A ∈ pd d) {a : ℝ} (ha : 0 < a) :
    a • A ∈ pd d := by
  change ((a : ℂ) • (A : Mat d)).PosDef
  exact hA.smul (by exact_mod_cast ha)

lemma convex_pd : Convex ℝ (pd d) := by
  intro A hA B hB a b ha hb hab
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simpa [show b = 1 by linarith] using hB
  · exact (pd_smul hA ha').add_posSemidef (psd_smul hB.posSemidef hb)

theorem inverse_convex {A B : H d} (hA : A ∈ pd d) (hB : B ∈ pd d)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a • invH A + b • invH B - invH (a • A + b • B) ∈ psdCone d := by
  let : Invertible (A : Mat d) := hA.isUnit.invertible
  let : Invertible (B : Mat d) := hB.isUnit.invertible
  have hc : a • A + b • B ∈ pd d := convex_pd hA hB ha hb hab
  let : Invertible ((a • A + b • B : H d) : Mat d) := hc.isUnit.invertible
  have hAb : (fromBlocks (A : Mat d) 1 1 (A : Mat d)⁻¹).PosSemidef := by
    simpa using (Matrix.PosDef.fromBlocks₁₁ 1 (A : Mat d)⁻¹ hA).mpr
      (by simpa using (Matrix.PosSemidef.zero (n := Fin d) (R := ℂ)) : ((A : Mat d)⁻¹ - (1 : Mat d)ᴴ * (A : Mat d)⁻¹ * 1).PosSemidef)
  have hBb : (fromBlocks (B : Mat d) 1 1 (B : Mat d)⁻¹).PosSemidef := by
    simpa using (Matrix.PosDef.fromBlocks₁₁ 1 (B : Mat d)⁻¹ hB).mpr
      (by simpa using (Matrix.PosSemidef.zero (n := Fin d) (R := ℂ)) : ((B : Mat d)⁻¹ - (1 : Mat d)ᴴ * (B : Mat d)⁻¹ * 1).PosSemidef)
  have hs := (hAb.smul (a := (a : ℂ)) (by exact_mod_cast ha)).add
    (hBb.smul (a := (b : ℂ)) (by exact_mod_cast hb))
  have hoff : (a : ℂ) • (1 : Mat d) + (b : ℂ) • (1 : Mat d) = 1 := by
    rw [← add_smul, ← Complex.ofReal_add, hab, Complex.ofReal_one, one_smul]
  rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add, hoff] at hs
  have he := (Matrix.PosDef.fromBlocks₁₁ 1
    ((a : ℂ) • (A : Mat d)⁻¹ + (b : ℂ) • (B : Mat d)⁻¹) hc).mp (by simpa using hs)
  simpa using he

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
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
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

lemma hasDerivAt_matrix_inverse (A U : H d) (hA : A ∈ pd d) :
    HasDerivAt (fun r : ℝ => ((A : Mat d) + r • (U : Mat d))⁻¹)
      (-((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹)) 0 := by
  obtain ⟨a, ha⟩ := hA.isUnit
  have hcurve : HasDerivAt (fun r : ℝ => (A : Mat d) + r • (U : Mat d)) (U : Mat d) 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) (A : Mat d)).add
      ((hasDerivAt_id' (0 : ℝ)).smul_const (U : Mat d))
    simp only [zero_add, one_smul] at hh
    exact hh
  have hInv := (hasFDerivAt_ringInverse (𝕜 := ℝ) a)
  rw [ha] at hInv
  have hz : (A : Mat d) = (fun r : ℝ => (A : Mat d) + r • (U : Mat d)) 0 := by
    ext i j
    simp [Matrix.add_apply]
  have hd := hInv.comp_hasDerivAt_of_eq (0 : ℝ) hcurve hz
  have hi : (↑a⁻¹ : Mat d) = (A : Mat d)⁻¹ := by rw [Matrix.coe_units_inv, ha]
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  · funext r
    exact Matrix.nonsing_inv_eq_ringInverse _
  · simp only [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hi]

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

lemma hasDerivAt_trace_inverse (A U P : H d) (hA : A ∈ pd d) :
    HasDerivAt (fun r : ℝ => inner ℝ P (invH (A + r • U)))
      (-inner ℝ (sandwich (invH A) P) U) 0 := by
  have hi := hasDerivAt_matrix_inverse A U hA
  have hm := (hasDerivAt_const (0 : ℝ) (P : Mat d)).mul hi
  have ht := (matrixTraceCLM (d := d)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hm
  have hfun : (fun r : ℝ => (matrixTraceCLM (d := d)) ((P : Mat d) *
      ((A : Mat d) + r • (U : Mat d))⁻¹)) =
      (fun r : ℝ => inner ℝ P (invH (A + r • U))) := by
    funext r
    rw [inner_eq_trace]
    rfl
  change HasDerivAt (fun r : ℝ => (matrixTraceCLM (d := d)) ((P : Mat d) *
    ((A : Mat d) + r • (U : Mat d))⁻¹)) _ (0 : ℝ) at ht
  rw [hfun] at ht
  simp only [zero_mul, zero_add, mul_neg] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  rw [← inner_sandwich, inner_eq_trace]
  change -((P : Mat d) * ((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹)).trace.re =
    (-((P : Mat d) * ((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹))).trace.re
  simp only [Matrix.trace_neg, Complex.neg_re]

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InnerRight
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

lemma inner_right_one (A : H d) : inner ℝ A (one : H d) = realTrace A := by
  rw [real_inner_comm, inner_one]

lemma hasDerivAt_inner_curve (B X U : H d) :
    HasDerivAt (fun r : ℝ => inner ℝ B (X + r • U)) (inner ℝ B U) 0 := by
  simp only [inner_add_right, inner_smul_rightH]
  have hh := (hasDerivAt_const (0 : ℝ) (inner ℝ B X)).add
      ((hasDerivAt_id' (0 : ℝ)).mul_const (inner ℝ B U))
  simp only [zero_add, one_mul] at hh
  exact hh

lemma inverse_trace_stationarity [NeZero d] (P B X : H d) (hX : X ∈ pd d)
    (hmin : ∀ Z ∈ pd d, inner ℝ P (invH X) + inner ℝ B X ≤
      inner ℝ P (invH Z) + inner ℝ B Z) : sandwich (invH X) P = B := by
  apply ext_inner_right ℝ
  intro U
  have hd := (hasDerivAt_trace_inverse X U P hX).add (hasDerivAt_inner_curve B X U)
  have hc : Continuous (fun r : ℝ => X + r • U) := by fun_prop
  have hn : ∀ᶠ r : ℝ in nhds 0, X + r • U ∈ pd d := by
    have h0 : X + (0 : ℝ) • U ∈ pd d := by simpa using hX
    exact (hc.continuousAt.preimage_mem_nhds (isOpen_pd.mem_nhds h0))
  have hm : IsLocalMin (fun r : ℝ => inner ℝ P (invH (X + r • U)) +
      inner ℝ B (X + r • U)) 0 := by
    filter_upwards [hn] with r hr
    simpa only [zero_smul, add_zero] using hmin (X + r • U) hr
  have he := hm.hasDerivAt_eq_zero hd
  linarith

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

lemma pd_sum_scalar {A : H d} (hA : A ∈ psdCone d) {ε : ℝ} (hε : 0 < ε) :
    A + ε • (one : H d) ∈ pd d := by
  have hh := (scalar_posDef hε).add_posSemidef hA
  rw [add_comm] at hh
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StrictEpigraph
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Conic
noncomputable section
open Set
open scoped Topology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

omit [ContinuousSMul ℝ F] in
lemma add_mem_interior_cone (K : ConvexCone ℝ F) {a b : F}
    (ha : a ∈ K) (hb : b ∈ interior (K : Set F)) :
    a + b ∈ interior (K : Set F) := by
  have ho : IsOpen {z : F | z - a ∈ interior (K : Set F)} :=
    isOpen_interior.preimage (continuous_id.sub continuous_const)
  have hs : {z : F | z - a ∈ interior (K : Set F)} ⊆ (K : Set F) := by
    intro z hz
    have := K.add_mem ha (interior_subset hz)
    simp only [add_sub_cancel] at this
    exact this
  apply interior_maximal hs ho
  simpa using hb

omit [IsTopologicalAddGroup F] in
lemma smul_mem_interior_cone (K : ConvexCone ℝ F) {a : ℝ} {b : F}
    (ha : 0 < a) (hb : b ∈ interior (K : Set F)) :
    a • b ∈ interior (K : Set F) := by
  have ho : IsOpen {z : F | a⁻¹ • z ∈ interior (K : Set F)} :=
    isOpen_interior.preimage (continuous_const.smul continuous_id)
  have hs : {z : F | a⁻¹ • z ∈ interior (K : Set F)} ⊆ (K : Set F) := by
    intro z hz
    have := K.smul_mem ha (interior_subset hz)
    simp only [smul_smul, mul_inv_cancel₀ ha.ne', one_smul] at this
    exact this
  apply interior_maximal hs ho
  change a⁻¹ • (a • b) ∈ interior (K : Set F)
  simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using hb

omit [AddCommGroup E] [Module ℝ E] [ContinuousSMul ℝ F] in
lemma strictEpigraph_open (K : ConvexCone ℝ F) (D : Set E) (g : E → F) (f : E → ℝ) :
    IsOpen (strictEpigraph K D g f) := by
  have he : strictEpigraph K D g f =
      ⋃ x ∈ D, {z : F × ℝ | z.1 - g x ∈ interior (K : Set F)} ∩
        {z : F × ℝ | f x < z.2} := by
    ext z
    simp only [strictEpigraph, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    aesop
  rw [he]
  exact isOpen_iUnion fun x => isOpen_iUnion fun _ =>
    (isOpen_interior.preimage (continuous_fst.sub continuous_const)).inter
      (isOpen_lt continuous_const continuous_snd)

lemma strictEpigraph_convex (K : ConvexCone ℝ F) (D : Set E) (g : E → F) (f : E → ℝ)
    (hD : Convex ℝ D) (hf : ConvexOn ℝ D f)
    (hg : ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      a • g x + b • g y - g (a • x + b • y) ∈ K) :
    Convex ℝ (strictEpigraph K D g f) := by
  rintro z ⟨x, hx, hzx, hfx⟩ w ⟨y, hy, hwy, hfy⟩ a b ha hb hab
  refine ⟨a • x + b • y, hD hx hy ha hb hab, ?_, ?_⟩
  · have hi := K.convex.interior hzx hwy ha hb hab
    have h := add_mem_interior_cone K (hg x hx y hy a b ha hb hab) hi
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    module
  · have h := hf.2 hx hy ha hb hab
    have hh : a * f x + b * f y < a * z.2 + b * w.2 := by
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb' : b = 1 := by linarith
        simpa [hb'] using hfy
      · have h1 := mul_lt_mul_of_pos_left hfx ha'
        have h2 := mul_le_mul_of_nonneg_left hfy.le hb
        linarith
    exact h.trans_lt hh

lemma nonpos_of_bounded_ray {a b c : ℝ} (h : ∀ r : ℝ, 0 ≤ r → a + r*b < c) : b ≤ 0 := by
  by_contra hn
  have hb : 0 < b := lt_of_not_ge hn
  have hr : 0 ≤ max 0 ((c-a)/b) + 1 := by positivity
  have hh := h _ hr
  have hmax : (c-a)/b ≤ max 0 ((c-a)/b) := le_max_right _ _
  have hm := (div_le_iff₀ hb).mp hmax
  nlinarith

theorem multiplier_rule (K : ConvexCone ℝ F) (h0 : (0 : F) ∈ K)
    (D : Set E) (g : E → F) (f : E → ℝ)
    (hD : Convex ℝ D) (hf : ConvexOn ℝ D f)
    (hg : ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      a • g x + b • g y - g (a • x + b • y) ∈ K)
    (x₀ : E) (hx₀ : x₀ ∈ D) (hfeas : -g x₀ ∈ K)
    (hmin : ∀ x ∈ D, -g x ∈ K → f x₀ ≤ f x)
    (xs : E) (hxs : xs ∈ D) (hstrict : -g xs ∈ interior (K : Set F)) :
    ∃ p : StrongDual ℝ F,
      (∀ k ∈ K, 0 ≤ p k) ∧ p (g x₀) = 0 ∧
      ∀ x ∈ D, f x₀ ≤ f x + p (g x) := by
  have hn : (0, f x₀) ∉ strictEpigraph K D g f := by
    rintro ⟨x, hx, hc, hfx⟩
    have hfe : -g x ∈ K := interior_subset (by simpa using hc)
    exact (not_lt_of_ge (hmin x hx hfe)) hfx
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point
    (strictEpigraph_convex K D g f hD hf hg) (strictEpigraph_open K D g f) hn
  let q : StrongDual ℝ F := l.comp (ContinuousLinearMap.inl ℝ F ℝ)
  let a : ℝ := l (0, 1)
  have hsplit (y : F) (t : ℝ) : l (y,t) = q y + t*a := by
    have he : (y,t) = (y,0) + t • (0,1) := by simp
    rw [he, map_add, map_smul]
    rfl
  have haneg : a < 0 := by
    let t := max (f xs + 1) (f x₀)
    have ht : f xs < t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hv : f x₀ ≤ t := le_max_right _ _
    have hs := hl (0,t) ⟨xs, hxs, by simpa using hstrict, ht⟩
    rw [hsplit, hsplit, map_zero, zero_add, zero_add] at hs
    by_contra hh
    have := mul_le_mul_of_nonneg_right hv (le_of_not_gt hh)
    linarith
  have hq (k : F) (hk : k ∈ K) : q k ≤ 0 := by
    have hr (r : ℝ) (hr : 0 ≤ r) :
        (f xs + 1)*a + r * q k < f x₀*a := by
      have hkr : r • k ∈ K := by
        rcases eq_or_lt_of_le hr with rfl | hr
        · simpa using h0
        · exact K.smul_mem hr hk
      have hs := hl (r • k, f xs + 1)
        ⟨xs, hxs, by simpa [sub_eq_add_neg] using add_mem_interior_cone K hkr hstrict,
          by linarith⟩
      rw [hsplit, hsplit, map_zero, zero_add, map_smul, smul_eq_mul] at hs
      linarith
    exact nonpos_of_bounded_ray hr
  have hlim (x : E) (hx : x ∈ D) : q (g x) + f x*a ≤ f x₀*a := by
    have hε (ε : ℝ) (hε : 0 < ε) :
        q (g x) + f x*a + ε*(q (-g xs) + a) < f x₀*a := by
      have hs := hl (g x + ε • (-g xs), f x + ε)
        ⟨x, hx, by simpa using smul_mem_interior_cone K hε hstrict, by linarith⟩
      rw [hsplit, hsplit, map_zero, zero_add, map_add, map_smul, smul_eq_mul] at hs
      nlinarith
    by_contra hh
    have hd : 0 < q (g x) + f x*a - f x₀*a := by linarith
    let ε := (q (g x) + f x*a - f x₀*a) / (|q (-g xs)+a|+1) / 2
    have hεpos : 0 < ε := by dsimp [ε] <;> positivity
    have hhε := hε ε hεpos
    have heq : ε * (|q (-g xs)+a|+1) * 2 = q (g x) + f x*a - f x₀*a := by
      dsimp [ε]
      field_simp
    have hab := neg_abs_le (q (-g xs)+a)
    have hmul := mul_le_mul_of_nonneg_left hab hεpos.le
    nlinarith
  let p : StrongDual ℝ F := a⁻¹ • q
  have hp (k : F) (hk : k ∈ K) : 0 ≤ p k := by
    change 0 ≤ a⁻¹ * q k
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr haneg.le) (hq k hk)
  have hlag (x : E) (hx : x ∈ D) : f x₀ ≤ f x + p (g x) := by
    have hh := hlim x hx
    change f x₀ ≤ f x + a⁻¹ * q (g x)
    have hm := mul_le_mul_of_nonpos_right hh (inv_nonpos.mpr haneg.le)
    calc
      f x₀ = (f x₀ * a) * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ haneg.ne, mul_one]
      _ ≤ (q (g x) + f x*a) * a⁻¹ := hm
      _ = f x + a⁻¹ * q (g x) := by
        rw [add_mul, mul_assoc, mul_inv_cancel₀ haneg.ne, mul_one]
        ring
  refine ⟨p, hp, ?_, hlag⟩
  have h1 := hp (-g x₀) hfeas
  have h2 := hlag x₀ hx₀
  rw [map_neg] at h1
  linarith
end
end CurrentKS.Conic

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Lagrangian
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

lemma convex_domain : Convex ℝ (domain d) := by
  intro z hz w hw a b ha hb hab
  exact ⟨convex_pd hz.1 hw.1 ha hb hab, convex_pd hz.2 hw.2 ha hb hab⟩

lemma convex_objective (ε : ℝ) : ConvexOn ℝ (domain d) (objective ε) := by
  refine ⟨convex_domain, ?_⟩
  intro z hz w hw a b ha hb hab
  apply le_of_eq
  simp only [objective, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    realTrace_add, realTrace_smul, smul_eq_mul]
  ring

lemma residual_coneConvex (S : H d) (η : H d →L[ℝ] H d)
    (z : Point d) (hz : z ∈ domain d) (w : Point d) (hw : w ∈ domain d)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a • residual S η z + b • residual S η w - residual S η (a • z + b • w) ∈ pairCone d := by
  have hX := inverse_convex hz.1 hw.1 ha hb hab
  have hY := inverse_convex hz.2 hw.2 ha hb hab
  have he : a • residual S η z + b • residual S η w - residual S η (a • z + b • w) =
      (a • invH z.2.1 + b • invH w.2.1 - invH (a • z.2.1 + b • w.2.1),
        a • invH z.2.2 + b • invH w.2.2 - invH (a • z.2.2 + b • w.2.2)) +
      ((a+b-1) • S, -(a+b-1) • S) := by
    apply Prod.ext <;> simp only [residual, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, map_add, map_smul, smul_eq_mul] <;> module
  rw [he, hab]
  simpa using And.intro hX hY

lemma unit_le_slack {R : H d} {r : ℝ} (hR : R ≤ r • (Hermitian.one : H d)) :
    (Hermitian.one : H d) ≤ (r+1) • (Hermitian.one : H d) - R := by
  have hh := sub_le_sub_left hR ((r+1) • (Hermitian.one : H d))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  module

lemma invH_one : invH (Hermitian.one : H d) = Hermitian.one := by
  apply Subtype.ext
  simp [invH]

lemma exists_strict_feasible [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d)) :
    ∃ z ∈ domain d, -residual S η z ∈ interior (pairCone d : Set (H d × H d)) := by
  let I : H d := Hermitian.one
  let t : ℝ := K + _root_.OAI.CurrentKS.Hermitian.realTrace (η I) + 2
  let z : Point d := (t,I,I)
  have heη : η I ≤ _root_.OAI.CurrentKS.Hermitian.realTrace (η I) • I := trace_bound_above (hη I one_mem_psdCone)
  have hmS : -S ≤ K • I := by
    have hh := neg_le_neg hS₁
    have he : -((-K) • (Hermitian.one : H d)) = K • I := by module
    rw [he] at hh
    exact hh
  have hR₁ : I + S + η I ≤ (1+K+_root_.OAI.CurrentKS.Hermitian.realTrace (η I)) • I := by
    have hh := add_le_add_left (add_le_add hS₂ heη) I
    convert hh using 1 <;> first | rfl | module
  have hR₂ : I - S + η I ≤ (1+K+_root_.OAI.CurrentKS.Hermitian.realTrace (η I)) • I := by
    have hh := add_le_add_left (add_le_add hmS heη) I
    convert hh using 1 <;> first | rfl | module
  have hs₁ : (-residual S η z).1 ∈ pd d := by
    apply pd_of_lower (a := 1) zero_lt_one
    have hh := unit_le_slack hR₁
    dsimp [residual, z, t]
    rw [show invH I = I from invH_one]
    convert hh using 1 <;> first | rfl | module
  have hs₂ : (-residual S η z).2 ∈ pd d := by
    apply pd_of_lower (a := 1) zero_lt_one
    have hh := unit_le_slack hR₂
    dsimp [residual, z, t]
    rw [show invH I = I from invH_one]
    convert hh using 1 <;> first | rfl | module
  refine ⟨z, ⟨Matrix.PosDef.one, Matrix.PosDef.one⟩, ?_⟩
  change -residual S η z ∈ interior ((psdCone d : Set (H d)) ×ˢ (psdCone d : Set (H d)))
  rw [interior_prod_eq]
  exact ⟨posDef_mem_interior _ hs₁, posDef_mem_interior _ hs₂⟩

theorem exists_matrix_multipliers [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    ∃ P Q : H d, P ∈ psdCone d ∧ Q ∈ psdCone d ∧
      inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 = 0 ∧
      ∀ w ∈ domain d, lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w := by
  obtain ⟨zs, hzs, hs⟩ := exists_strict_feasible S η hη hS₁ hS₂
  have hzc := (feasible_iff_cone S η z).mp hz
  obtain ⟨p, hp, hc, hl⟩ := Conic.multiplier_rule (pairCone d)
    ⟨zero_mem_psdCone, zero_mem_psdCone⟩ (domain d) (residual S η) (objective ε)
    convex_domain (convex_objective ε) (residual_coneConvex S η)
    z hzc.1 hzc.2 (fun w hw hf => hmin w ((feasible_iff_cone S η w).mpr ⟨hw,hf⟩))
    zs hzs hs
  let p₁ : StrongDual ℝ (H d) := p.comp (ContinuousLinearMap.inl ℝ (H d) (H d))
  let p₂ : StrongDual ℝ (H d) := p.comp (ContinuousLinearMap.inr ℝ (H d) (H d))
  obtain ⟨P, hP, heP⟩ := positive_dual_matrix p₁ (fun A hA => hp (A,0) ⟨hA, zero_mem_psdCone⟩)
  obtain ⟨Q, hQ, heQ⟩ := positive_dual_matrix p₂ (fun A hA => hp (0,A) ⟨zero_mem_psdCone, hA⟩)
  have he (A B : H d) : p (A,B) = inner ℝ P A + inner ℝ Q B := by
    rw [← heP, ← heQ]
    change p (A,B) = p (A,0) + p (0,B)
    rw [← map_add]
    congr 1
    simp
  have hcomp : inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 = 0 := by
    rw [← he]
    exact hc
  refine ⟨P,Q,hP,hQ,hcomp, fun w hw => ?_⟩
  have h := hl w hw
  rw [show residual S η w = ((residual S η w).1,(residual S η w).2) from rfl, he] at h
  change objective ε z + inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 ≤
    objective ε w + inner ℝ P (residual S η w).1 + inner ℝ Q (residual S η w).2
  linarith

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

lemma stationary_trace (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (P Q : H d) (z : Point d) (hz : z ∈ domain d)
    (hmin : ∀ w ∈ domain d, lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w) :
    _root_.OAI.CurrentKS.Hermitian.realTrace P + _root_.OAI.CurrentKS.Hermitian.realTrace Q = 1 := by
  have hp := hmin (z.1+1,z.2) hz
  have hm := hmin (z.1-1,z.2) hz
  rw [lagrangian_separate ε S η hη, lagrangian_separate ε S η hη] at hp hm
  dsimp only at hp hm
  nlinarith

lemma stationary_X [NeZero d] (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (P Q : H d) (z : Point d) (hz : z ∈ domain d)
    (hmin : ∀ w ∈ domain d, lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w) :
    sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d) := by
  apply inverse_trace_stationarity P _ _ hz.1
  intro X hX
  have h := hmin (z.1,X,z.2.2) ⟨hX,hz.2⟩
  rw [lagrangian_separate ε S η hη, lagrangian_separate ε S η hη] at h
  dsimp only at h
  linarith

lemma stationary_Y [NeZero d] (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (P Q : H d) (z : Point d) (hz : z ∈ domain d)
    (hmin : ∀ w ∈ domain d, lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w) :
    sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d) := by
  apply inverse_trace_stationarity Q _ _ hz.2
  intro Y hY
  have h := hmin (z.1,z.2.1,Y) ⟨hz.1,hY⟩
  rw [lagrangian_separate ε S η hη, lagrangian_separate ε S η hη] at h
  dsimp only at h
  linarith

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_TightComplementarity
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

lemma tight_of_complementarity [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (P Q : H d) (hP : P ∈ pd d) (hQ : Q ∈ pd d) (z : Point d)
    (hz : z ∈ feasible S η)
    (hc : inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 = 0) :
    residual S η z = 0 := by
  have hf := (feasible_iff_cone S η z).mp hz
  have hPz := inner_nonneg_of_psd P (-residual S η z).1 hP.posSemidef hf.2.1
  have hQz := inner_nonneg_of_psd Q (-residual S η z).2 hQ.posSemidef hf.2.2
  simp only [Prod.fst_neg, Prod.snd_neg, inner_neg_right] at hPz hQz
  have h₁ : inner ℝ P (-(residual S η z).1) = 0 := by rw [inner_neg_right]; linarith
  have h₂ : inner ℝ Q (-(residual S η z).2) = 0 := by rw [inner_neg_right]; linarith
  have he₁ := eq_zero_of_inner_pd hP hf.2.1 h₁
  have he₂ := eq_zero_of_inner_pd hQ hf.2.2 h₂
  apply Prod.ext
  · exact neg_eq_zero.mp he₁
  · exact neg_eq_zero.mp he₂

theorem kkt_oai [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hηpos : ∀ A ∈ psdCone d, η A ∈ psdCone d) (hηsym : SymmetricMap η)
    {ε K : ℝ} (hε : 0 < ε)
    (hS₁ : -K • ((Hermitian.one : H d) : H d) ≤ S) (hS₂ : S ≤ K • ((Hermitian.one : H d) : H d))
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    ∃ P Q : H d, P ∈ pd d ∧ Q ∈ pd d ∧ P ≤ (Hermitian.one : H d) ∧ Q ≤ (Hermitian.one : H d) ∧
      _root_.OAI.CurrentKS.Hermitian.realTrace P + _root_.OAI.CurrentKS.Hermitian.realTrace Q = 1 ∧
      P = sandwich z.2.1 (η Q) + ε • sandwich z.2.1 (Hermitian.one : H d) ∧
      Q = sandwich z.2.2 (η P) + ε • sandwich z.2.2 (Hermitian.one : H d) ∧
      residual S η z = 0 ∧
      sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d) ∧
      sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d) := by
  obtain ⟨P,Q,hP,hQ,hc,hl⟩ := exists_matrix_multipliers S η hηpos hS₁ hS₂ z hz hmin
  have hzD := hz.1
  have htr := stationary_trace ε S η hηsym P Q z hzD hl
  have hX := stationary_X ε S η hηsym P Q z hzD hl
  have hY := stationary_Y ε S η hηsym P Q z hzD hl
  have hPX : P = sandwich z.2.1 (η Q + ε • (Hermitian.one : H d)) := by
    rw [← hX, sandwich_inverse_cancel _ _ hzD.1]
  have hQY : Q = sandwich z.2.2 (η P + ε • (Hermitian.one : H d)) := by
    rw [← hY, sandwich_inverse_cancel _ _ hzD.2]
  have hPpd : P ∈ pd d := hPX.symm ▸ (sandwich_pd _ _ hzD.1 (pd_sum_scalar (hηpos Q hQ) hε))
  have hQpd : Q ∈ pd d := hQY.symm ▸ (sandwich_pd _ _ hzD.2 (pd_sum_scalar (hηpos P hP) hε))
  have hPle : P ≤ (Hermitian.one : H d) := by
    have ht : _root_.OAI.CurrentKS.Hermitian.realTrace P ≤ 1 := by linarith [realTrace_nonneg hQ]
    exact (trace_bound_above hP).trans (by simpa only [one_smul] using scalar_one_mono (d := d) ht)
  have hQle : Q ≤ (Hermitian.one : H d) := by
    have ht : _root_.OAI.CurrentKS.Hermitian.realTrace Q ≤ 1 := by linarith [realTrace_nonneg hP]
    exact (trace_bound_above hQ).trans (by simpa only [one_smul] using scalar_one_mono (d := d) ht)
  refine ⟨P,Q,hPpd,hQpd,hPle,hQle,htr,?_,?_,tight_of_complementarity S η P Q hPpd hQpd z hz hc,hX,hY⟩
  · rw [hPX, sandwich_add, sandwich_smul]
  · rw [hQY, sandwich_add, sandwich_smul]

end
end CurrentKS.Variational

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.Variational.kkt_oai := @OAI.CurrentKS.Variational.kkt_oai
