-- Prove2me | solution 1 for OAI.CurrentKS.Variational.value_derivatives_majorant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:42.821747+00:00
-- url     : https://prove2.me/submissions/f194b796-b876-4353-8c64-41b6213602df

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_Variational_contDiffAt_value
import Theorems.Thm_OAI_CurrentKS_Variational_kkt

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_LocalMinSecondNonnegative
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Analysis
open Filter Set
open scoped Topology

lemma localMin_second_nonnegative {f : ℝ → ℝ} {a : ℝ}
    (h : IsLocalMin f a) (hc : ContinuousAt f a) : 0 ≤ deriv (deriv f) a := by
  by_contra hn
  have hn' : deriv (deriv f) a < 0 := lt_of_not_ge hn
  have hm := isLocalMax_of_deriv_deriv_neg hn' h.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [h,hm] with x hx hx'
    exact le_antisymm hx' hx
  have he' := he.deriv.deriv_eq
  simp only [deriv_const'] at he'
  linarith

lemma majorant_derivatives {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 2 f a) (hg : ContDiffAt ℝ 2 g a)
    (heq : f a = g a) (hle : ∀ᶠ s in 𝓝 a, f s ≤ g s) :
    deriv f a = deriv g a ∧ deriv (deriv f) a ≤ deriv (deriv g) a := by
  have hm : IsLocalMin (fun s => g s - f s) a := by
    filter_upwards [hle] with s hs
    change g a - f a ≤ g s - f s
    rw [← heq,sub_self]
    exact sub_nonneg.mpr hs
  have hd := hm.deriv_eq_zero
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have he : deriv (fun s => g s - f s) =ᶠ[𝓝 a] fun s => deriv g s - deriv f s := by
    filter_upwards [hf.eventually (by norm_num),
      hg.eventually (by norm_num)] with s hs ht
    exact deriv_sub (ht.differentiableAt (by norm_num)) (hs.differentiableAt (by norm_num))
  have hf' := hf.derivWithin (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)
  have hg' := hg.derivWithin (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)
  have hdd := localMin_second_nonnegative hm (hg.continuousAt.sub hf.continuousAt)
  rw [he.deriv_eq] at hdd
  have hde := ((hg'.differentiableAt (by norm_num)).hasDerivAt.sub
    (hf'.differentiableAt (by norm_num)).hasDerivAt).deriv
  change deriv (fun s => deriv g s - deriv f s) a = _ at hde
  rw [hde] at hdd
  have hd0 := (hgd.hasDerivAt.sub hfd.hasDerivAt).deriv
  change deriv (fun s => g s - f s) a = _ at hd0
  rw [hd0] at hd
  exact ⟨(sub_eq_zero.mp hd).symm,sub_nonneg.mp hdd⟩

end CurrentKS.Analysis

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_ra8140e_1 : NormedSpace ℝ (H d) := inferInstance
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RetractH
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

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p6
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6
lemma invH_retract (A : H d) : invH A = retractH (Ring.inverse (A : Mat d)) := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact (retractH_coe (invH A)).symm

lemma contDiffAt_invH {A : H d} (hA : A ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n invH A := by
  obtain ⟨a,ha⟩ := hA.isUnit
  have hi : ContDiffAt ℝ n Ring.inverse (A : Mat d) := by
    rw [← ha]
    exact contDiffAt_ringInverse ℝ a
  have hc := (retractH (d := d)).contDiff.contDiffAt.comp A
    (hi.comp A (hermitianSubmodule d).subtypeL.contDiff.contDiffAt)
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun B => invH_retract B

lemma hasFDerivAt_invH {A : H d} (hA : A ∈ pd d) :
    HasFDerivAt invH (-sandwichCLM (invH A)) A := by
  obtain ⟨a,ha⟩ := hA.isUnit
  have hi : HasFDerivAt (fun B : Mat d => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Mat d) (A : Mat d)⁻¹ (A : Mat d)⁻¹) (A : Mat d) := by
    rw [← ha]
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Matrix.coe_units_inv] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) a)
  have hc := (retractH (d := d)).hasFDerivAt.comp A
    (hi.comp A (hermitianSubmodule d).subtypeL.hasFDerivAt)
  have he : (fun B : H d => retractH ((B : Mat d)⁻¹)) = invH := by
    funext B
    exact retractH_coe (invH B)
  change HasFDerivAt (fun B : H d => retractH ((B : Mat d)⁻¹)) _ A at hc
  rw [he] at hc
  refine hc.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro U
  change -sandwich (invH A) U = retractH (-((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹))
  rw [map_neg]
  exact congrArg Neg.neg (retractH_coe (sandwich (invH A) U)).symm

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FDerivTightPart
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
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma contDiffAt_tightPart {n : WithTop ℕ∞} {t : E → ℝ} {X Y S : E → H d}
    {η : E → (H d →L[ℝ] H d)} {z : E}
    (ht : ContDiffAt ℝ n t z) (hX : ContDiffAt ℝ n X z) (hY : ContDiffAt ℝ n Y z)
    (hS : ContDiffAt ℝ n S z) (hη : ContDiffAt ℝ n η z) (hpos : X z ∈ pd d) :
    ContDiffAt ℝ n (fun v => t v • (one : H d) - invH (X v) - S v - η v (Y v)) z :=
  (((ht.smul contDiffAt_const).sub ((contDiffAt_invH hpos).comp z hX)).sub hS).sub
    (hη.clm_apply hY)

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PartialFderiv
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.KKT
noncomputable section
open scoped Topology ContDiff

variable {A Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma partial_fderiv {F : A × Z → Z} {a : A} {z : Z} {L : Z →L[ℝ] Z}
    (hF : DifferentiableAt ℝ F (a,z))
    (hL : HasFDerivAt (fun v => F (a,v)) L z) :
    (fderiv ℝ F (a,z)).comp (ContinuousLinearMap.inr ℝ A Z) = L := by
  have hi : HasFDerivAt (fun v : Z => (a,v)) (ContinuousLinearMap.inr ℝ A Z) z := by
    convert (hasFDerivAt_const a z).prodMk (hasFDerivAt_id z) using 1 <;> rfl
  exact (hF.hasFDerivAt.comp z hi).unique hL

lemma smooth_branch [CompleteSpace A] [CompleteSpace Z] {F : A × Z → Z} {a : A} {z : Z}
    (hF : ContDiffAt ℝ ∞ F (a,z)) (J : Z ≃L[ℝ] Z)
    (hJ : HasFDerivAt (fun v => F (a,v)) J.toContinuousLinearMap z) :
    ∃ f : A → Z, f a = z ∧ ContDiffAt ℝ ∞ f a ∧
      ∀ᶠ b in 𝓝 a, F (b,f b) = F (a,z) := by
  have hi : ((fderiv ℝ F (a,z)).comp (ContinuousLinearMap.inr ℝ A Z)).IsInvertible := by
    rw [partial_fderiv (hF.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hJ]
    exact ContinuousLinearMap.isInvertible_equiv
  refine ⟨hF.implicitFunction (by simp) hi, hF.implicitFunction_apply_self (by simp) hi,
    hF.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi, ?_⟩
  exact hF.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi

end
end CurrentKS.KKT

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_TightSystem
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

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p5
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p5
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p5
lemma hasFDerivAt_tightSystem (t : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (z : Pair d) (hX : z.1 ∈ pd d) (hY : z.2 ∈ pd d) :
    HasFDerivAt (tightSystem t S η) (linConstraint z.1 z.2 η) z := by
  have h₁ := (((hasFDerivAt_const (t • (Hermitian.one : H d)) z).sub
    ((hasFDerivAt_invH hX).comp z (hasFDerivAt_fst (p := z)))).sub_const S).sub
      (η.hasFDerivAt.comp z (hasFDerivAt_snd (p := z)))
  have h₂ := (((hasFDerivAt_const (t • (Hermitian.one : H d)) z).sub
    ((hasFDerivAt_invH hY).comp z (hasFDerivAt_snd (p := z)))).add_const S).sub
      (η.hasFDerivAt.comp z (hasFDerivAt_fst (p := z)))
  convert h₁.prodMk h₂ using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · change sandwich (invH z.1) v.1 - η v.2 = 0 - (-sandwich (invH z.1) v.1) - η v.2
    module
  · change sandwich (invH z.2) v.2 - η v.1 = 0 - (-sandwich (invH z.2) v.2) - η v.1
    module

attribute [local instance] OAI.CurrentKS.Variational.tightSystemOperatorNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.tightSystemOperatorNormedSpace
attribute [local instance] OAI.CurrentKS.Variational.tightSystemPairNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.tightSystemPairNormedSpace
attribute [local instance] OAI.CurrentKS.Variational.tightSystemParametersNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.tightSystemParametersNormedSpace
attribute [local instance] OAI.CurrentKS.Variational.tightSystemProductNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.tightSystemProductNormedSpace
lemma contDiffAt_tightGiven {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} (t : ℝ) {S : E → H d} {η : E → (H d →L[ℝ] H d)}
    {X Y : E → H d} {b : E}
    (hS : ContDiffAt ℝ n S b) (hη : ContDiffAt ℝ n η b)
    (hx : ContDiffAt ℝ n X b) (hy : ContDiffAt ℝ n Y b)
    (hX : X b ∈ pd d) (hY : Y b ∈ pd d) :
    ContDiffAt ℝ n (fun v => tightSystem t (S v) (η v) (X v,Y v)) b := by
  have h₁ := contDiffAt_tightPart (t := fun _ => t) contDiffAt_const hx hy hS hη hX
  have h₂ := contDiffAt_tightPart (t := fun _ => t) contDiffAt_const hy hx hS.neg hη hY
  simpa only [tightSystem,sub_neg_eq_add] using h₁.prodMk h₂

lemma contDiffAt_tightJoint {n : WithTop ℕ∞} (t : ℝ) (a : Parameters d) (z : Pair d)
    (hX : z.1 ∈ pd d) (hY : z.2 ∈ pd d) :
    ContDiffAt ℝ n (tightJoint t) (a,z) := by
  exact contDiffAt_tightGiven (E := Parameters d × Pair d) t
    (S := fun v => v.1.1) (η := fun v => v.1.2)
    (X := fun v => v.2.1) (Y := fun v => v.2.2)
    contDiffAt_fst.fst contDiffAt_fst.snd contDiffAt_snd.fst contDiffAt_snd.snd hX hY

theorem exists_smooth_tight_branch (t : ℝ) (a : Parameters d) (z : Pair d)
    (hX : z.1 ∈ pd d) (hY : z.2 ∈ pd d)
    (J : Pair d ≃L[ℝ] Pair d) (hJ : J.toContinuousLinearMap = linConstraint z.1 z.2 a.2) :
    ∃ f : Parameters d → Pair d, f a = z ∧ ContDiffAt ℝ ∞ f a ∧
      ∀ᶠ b in 𝓝 a, tightSystem t b.1 b.2 (f b) = tightSystem t a.1 a.2 z := by
  apply CurrentKS.KKT.smooth_branch (contDiffAt_tightJoint t a z hX hY) J
  erw [hJ]
  exact hasFDerivAt_tightSystem t a.1 a.2 z hX hY

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

lemma contDiff_objective (ε : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (objective (d := d) ε) := by
  have ht : ContDiff ℝ n (fun z : Point d => inner ℝ (Hermitian.one : H d) (z.2.1+z.2.2)) :=
    (innerSL ℝ (Hermitian.one : H d)).contDiff.comp (contDiff_snd.fst.add contDiff_snd.snd)
  have hh := contDiff_fst.add ((contDiff_const (c := ε)).mul ht)
  simp only [inner_one] at hh
  exact hh

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ValueFeasible
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

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p8
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedSpace
attribute [local instance] OAI.CurrentKS.Variational.valueFeasiblePairNormedSpace
lemma value_le_feasible [NeZero d] (ε : ℝ) (hε : 0 ≤ ε) (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d) (z : Point d) (hz : z ∈ feasible S η) :
    value ε S η ≤ objective ε z := by
  have hb : BddBelow (objective ε '' feasible S η) := by
    refine ⟨0,?_⟩
    rintro r ⟨w,hw,rfl⟩
    obtain ⟨ht,hX,hY⟩ := trace_bounds_of_feasible S η hη hw
    simp only [objective,realTrace_add]
    exact add_nonneg ht (mul_nonneg hε (add_nonneg hX hY))
  exact csInf_le hb ⟨z,hz,rfl⟩

attribute [local instance] OAI.CurrentKS.Variational.valueFeasiblePairNormedAddCommGroup
lemma tightSystem_eq_neg_residual (t : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Pair d) :
    tightSystem t S η z = -residual S η (t,z) := by
  apply Prod.ext <;> change _ = -_ <;> dsimp only [tightSystem,residual] <;> abel

theorem exists_smooth_feasible_majorant [NeZero d]
    (ε : ℝ) (hε : 0 < ε) (S : ℝ → H d) (η : ℝ → (H d →L[ℝ] H d)) (a : ℝ)
    (hS : ContDiffAt ℝ ∞ S a) (hη : ContDiffAt ℝ ∞ η a)
    (hηpos : ∀ A ∈ psdCone d, η a A ∈ psdCone d) (hηsym : SymmetricMap (η a))
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S a) (hS₂ : S a ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S a) (η a))
    (hmin : ∀ w ∈ feasible (S a) (η a), objective ε z ≤ objective ε w) :
    ∃ g : ℝ → Pair d, g a = z.2 ∧ ContDiffAt ℝ ∞ g a ∧
      ∀ᶠ s in 𝓝 a, (z.1,g s) ∈ feasible (S s) (η s) ∧
        residual (S s) (η s) (z.1,g s) = 0 := by
  obtain ⟨P,Q,hP,hQ,_,_,_,hPX,hQY,ht,_,_⟩ :=
    kkt (S a) (η a) hηpos hηsym hε hS₁ hS₂ z hz hmin
  obtain ⟨J,hJ,_⟩ := linConstraint_positive_inverse z.2.1 z.2.2 P Q (η a)
    hηpos hz.1.1 hz.1.2 hP hQ hε hPX hQY
  have hJ' : J.toContinuousLinearMap = linConstraint z.2.1 z.2.2 (η a) := by
    apply ContinuousLinearMap.ext
    intro v
    exact hJ v
  obtain ⟨f,hf,hfc,hfe⟩ := exists_smooth_tight_branch z.1 (S a,η a) z.2 hz.1.1 hz.1.2 J hJ'
  let g : ℝ → Pair d := fun s => f (S s,η s)
  have hg : g a = z.2 := hf
  have hgc : ContDiffAt ℝ ∞ g a := hfc.comp a (hS.prodMk hη)
  have hge : ∀ᶠ s in 𝓝 a, residual (S s) (η s) (z.1,g s) = 0 := by
    filter_upwards [(hS.continuousAt.prodMk hη.continuousAt).eventually hfe] with s hs
    have ht' : residual (S a) (η a) (z.1,z.2) = 0 := ht
    simpa only [tightSystem_eq_neg_residual,ht',neg_zero,neg_eq_zero] using hs
  have hXg : ∀ᶠ s in 𝓝 a, (g s).1 ∈ pd d := by
    apply hgc.fst.continuousAt.eventually
    apply isOpen_pd.mem_nhds
    change (g a).1 ∈ pd d
    rw [hg]
    exact hz.1.1
  have hYg : ∀ᶠ s in 𝓝 a, (g s).2 ∈ pd d := by
    apply hgc.snd.continuousAt.eventually
    apply isOpen_pd.mem_nhds
    change (g a).2 ∈ pd d
    rw [hg]
    exact hz.1.2
  refine ⟨g,hg,hgc,?_⟩
  filter_upwards [hge,hXg,hYg] with s hs hx hy
  refine ⟨⟨⟨hx,hy⟩,?_,?_⟩,hs⟩ <;> rw [hs] <;> exact le_rfl

theorem value_derivatives_majorant_oai [NeZero d]
    (ε : ℝ) (hε : 0 < ε) (S : ℝ → H d) (η : ℝ → (H d →L[ℝ] H d)) (a : ℝ)
    (hS : ContDiffAt ℝ ∞ S a) (hη : ContDiffAt ℝ ∞ η a)
    (hηpos : ∀ᶠ s in 𝓝 a, ∀ A ∈ psdCone d, η s A ∈ psdCone d)
    (hηsym : ∀ᶠ s in 𝓝 a, SymmetricMap (η s))
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S a) (hS₂ : S a ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S a) (η a))
    (hmin : ∀ w ∈ feasible (S a) (η a), objective ε z ≤ objective ε w) :
    ∃ g : ℝ → Pair d, g a = z.2 ∧ ContDiffAt ℝ ∞ g a ∧
      (∀ᶠ s in 𝓝 a, residual (S s) (η s) (z.1,g s) = 0) ∧
      deriv (fun s => value ε (S s) (η s)) a = deriv (fun s => objective ε (z.1,g s)) a ∧
      deriv (deriv (fun s => value ε (S s) (η s))) a ≤
        deriv (deriv (fun s => objective ε (z.1,g s))) a := by
  obtain ⟨g,hg,hgc,hge⟩ := exists_smooth_feasible_majorant ε hε S η a hS hη
    hηpos.self_of_nhds hηsym.self_of_nhds hS₁ hS₂ z hz hmin
  have hv := contDiffAt_value ε hε S η a hS hη hηpos.self_of_nhds hηsym hS₁ hS₂ z hz hmin
  have ho : ContDiffAt ℝ ∞ (fun s => objective ε (z.1,g s)) a :=
    (contDiff_objective ε).contDiffAt.comp a (contDiffAt_const.prodMk hgc)
  have heq : value ε (S a) (η a) = objective ε (z.1,g a) := by
    rw [hg]
    exact value_eq_of_min ε (S a) (η a) z hz hmin
  have hle : ∀ᶠ s in 𝓝 a, value ε (S s) (η s) ≤ objective ε (z.1,g s) := by
    filter_upwards [hge,hηpos] with s hs hp
    exact value_le_feasible ε hε.le (S s) (η s) hp (z.1,g s) hs.1
  obtain ⟨hd,hdd⟩ := CurrentKS.Analysis.majorant_derivatives
    (contDiffAt_infty.mp hv 2) (contDiffAt_infty.mp ho 2) heq hle
  exact ⟨g,hg,hgc,hge.mono fun _ hs => hs.2,hd,hdd⟩

end
end CurrentKS.Variational

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.Variational.value_derivatives_majorant_oai := @OAI.CurrentKS.Variational.value_derivatives_majorant_oai
