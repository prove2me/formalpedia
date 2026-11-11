-- Prove2me | solution 1 for OAI.CurrentKS.State.face_value_direction_variations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:52:09.075011+00:00
-- url     : https://prove2.me/submissions/04c6b35f-03fe-4876-9e9c-544c94fa471c

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_Variational_value_derivatives_majorant

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

lemma psi_pos {x : ℝ} (hx : |x| < 1) : 0 < psi x :=
  Real.rpow_pos_of_pos (base_pos hx) _

lemma psi_cube {x : ℝ} (hx : |x| < 1) : psi x ^ 3 = 1-x^2 := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma psi_sq {x : ℝ} (hx : |x| < 1) : psi x ^ 2 = (1-x^2) ^ (2/3 : ℝ) := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma hasDerivAt_psi {x : ℝ} (hx : |x| < 1) : HasDerivAt psi (psi₁ x) x := by
  have hr := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).rpow_const
    (p := (1/3 : ℝ)) (Or.inl (ne_of_gt (base_pos hx)))
  convert hr using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  norm_num only [mul_one, zero_sub, Nat.cast_ofNat]
  simp only [id_eq, pow_one, Pi.sub_apply, Pi.pow_apply]
  rw [Real.rpow_neg (base_pos hx).le, ← psi_sq hx]
  unfold psi₁
  ring

lemma contDiffAt_psi {x : ℝ} (hx : |x| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n psi x := by
  exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (base_pos hx))).comp x
    (contDiffAt_const.sub (contDiffAt_id.pow 2))

lemma hasDerivAt_psi₁ {x : ℝ} (hx : |x| < 1) : HasDerivAt psi₁ (-kappa x) x := by
  have hw : psi x ≠ 0 := ne_of_gt (psi_pos hx)
  have hp := hasDerivAt_psi hx
  have hd := ((hasDerivAt_id x).const_mul (-2)).div ((hp.pow 2).const_mul 3)
    (by positivity : (3 : ℝ) * psi x^2 ≠ 0)
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  unfold kappa psi₁
  have hc := psi_cube hx
  field_simp
  nlinarith [hc]

lemma kappa_pos {x : ℝ} (hx : |x| < 1) : 0 < kappa x := by
  unfold kappa
  have h := psi_pos hx
  positivity

lemma derivative_ratio {x : ℝ} (hx : |x| < 1) :
    psi₁ x ^ 2 / (psi x * kappa x) = 2*x^2/(3+x^2) := by
  have hw := ne_of_gt (psi_pos hx)
  have hx3 : 3+x^2 ≠ 0 := by positivity
  unfold psi₁ kappa
  field_simp
  ring

lemma derivative_ratio_le {x : ℝ} (hx : |x| < 1) :
    psi₁ x ^ 2 / (psi x * kappa x) ≤ (1/2 : ℝ) := by
  rw [derivative_ratio hx]
  have hp : 0 < 3+x^2 := by positivity
  apply (div_le_iff₀ hp).mpr
  have hb := base_pos hx
  nlinarith

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MixedYoungBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar

lemma mixed_young_bound {c s k f h p q a b u v r w : ℝ}
    (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : f^2/s ≤ k/2)
    (hu : 2*(f*h)*u ≤ s*r + (f*h)^2/s*a)
    (hv : 2*(f*h)*v ≤ s*w + (f*h)^2/s*b) :
    2*c*f*h*(p*v+q*u) ≤ c*s*(q*r+p*w) + (c/2)*k*h^2*(b*p+a*q) := by
  have hh : (f*h)^2/s ≤ (k/2)*h^2 := by
    calc
      _ = (f^2/s)*h^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hf (sq_nonneg h)
  have ha' := mul_le_mul_of_nonneg_right hh ha
  have hb' := mul_le_mul_of_nonneg_right hh hb
  have hu' : 2*(f*h)*u ≤ s*r + (k/2)*h^2*a := hu.trans (add_le_add (le_refl (s*r)) ha')
  have hv' : 2*(f*h)*v ≤ s*w + (k/2)*h^2*b := hv.trans (add_le_add (le_refl (s*w)) hb')
  have hu'' := mul_le_mul_of_nonneg_left hu' (mul_nonneg hc hq)
  have hv'' := mul_le_mul_of_nonneg_left hv' (mul_nonneg hc hp)
  nlinarith

lemma derivative_square_le {x : ℝ} (hx : |x| < 1) : psi₁ x^2 / psi x ≤ kappa x/2 := by
  have hh := derivative_ratio_le hx
  rw [← div_div,div_le_iff₀ (kappa_pos hx)] at hh
  linarith
end CurrentKS.Scalar

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r757011_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
lemma jordanCLM_val (A B U : H d) :
    ((jordanCLM A B U : H d) : Mat d) =
      (A : Mat d) * (U : Mat d) * (B : Mat d) + (B : Mat d) * (U : Mat d) * (A : Mat d) := by
  change ((A : Mat d)+(B : Mat d)) * (U : Mat d) * ((A : Mat d)+(B : Mat d)) -
    (A : Mat d)*(U : Mat d)*(A : Mat d) - (B : Mat d)*(U : Mat d)*(B : Mat d) = _
  noncomm_ring

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

lemma hasFDerivAt_invSandwich (A P : H d) (hA : A ∈ pd d) :
    HasFDerivAt (fun z : H d × H d => sandwich (invH z.1) z.2)
      ((-jordanCLM (invH A) (sandwich (invH A) P)).comp (ContinuousLinearMap.fst ℝ (H d) (H d)) +
       (sandwichCLM (invH A)).comp (ContinuousLinearMap.snd ℝ (H d) (H d))) (A,P) := by
  let val := (hermitianSubmodule d).subtypeL
  have hInv := val.hasFDerivAt.comp (A,P)
    ((hasFDerivAt_invH hA).comp (A,P) (hasFDerivAt_fst (p := (A,P))))
  have hMid := val.hasFDerivAt.comp (A,P) (hasFDerivAt_snd (p := (A,P)))
  have hm := (hInv.mul' hMid).mul' hInv
  have hh := (retractH (d := d)).hasFDerivAt.comp (A,P) hm
  have he : (fun z : H d × H d => retractH
      (((invH z.1 : H d) : Mat d) * (z.2 : Mat d) * ((invH z.1 : H d) : Mat d))) =
      (fun z : H d × H d => sandwich (invH z.1) z.2) := by
    funext z
    exact retractH_coe (sandwich (invH z.1) z.2)
  change HasFDerivAt (fun z : H d × H d => retractH
    (((invH z.1 : H d) : Mat d) * (z.2 : Mat d) * ((invH z.1 : H d) : Mat d))) _ (A,P) at hh
  rw [he] at hh
  refine hh.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro z
  change -jordanCLM (invH A) (sandwich (invH A) P) z.1 + sandwich (invH A) z.2 =
    retractH
      (((invH A : H d) : Mat d) * (P : Mat d) *
          (-(((invH A : H d) : Mat d) * (z.1 : Mat d) * ((invH A : H d) : Mat d))) +
       (((invH A : H d) : Mat d) * (z.2 : Mat d) +
          (-(((invH A : H d) : Mat d) * (z.1 : Mat d) * ((invH A : H d) : Mat d))) * (P : Mat d)) *
        ((invH A : H d) : Mat d))
  rw [← retractH_coe (-jordanCLM (invH A) (sandwich (invH A) P) z.1 + sandwich (invH A) z.2)]
  congr 1
  simp only [Submodule.coe_add, Submodule.coe_neg, jordanCLM_val, sandwich_val]
  noncomm_ring

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DerivInvHPath
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
lemma hasDerivAt_invH_path {X : ℝ → H d} {U : H d} {a : ℝ}
    (hX : X a ∈ pd d) (hU : HasDerivAt X U a) :
    HasDerivAt (fun s => invH (X s)) (-sandwich (invH (X a)) U) a := by
  exact (hasFDerivAt_invH hX).comp_hasDerivAt a hU

lemma hasDerivAt_invSandwich_path {X P : ℝ → H d} {U V : H d} {a : ℝ}
    (hX : X a ∈ pd d) (hU : HasDerivAt X U a) (hV : HasDerivAt P V a) :
    HasDerivAt (fun s => sandwich (invH (X s)) (P s))
      (-jordanCLM (invH (X a)) (sandwich (invH (X a)) (P a)) U +
        sandwich (invH (X a)) V) a := by
  exact (hasFDerivAt_invSandwich (X a) (P a) hX).comp_hasDerivAt a (hU.prodMk hV)

lemma jordan_inverse_square (X U : H d) :
    jordanCLM (invH X) (sandwich (invH X) U) U =
      (2 : ℝ) • sandwich (invH X) (sandwich U (invH X)) := by
  apply Subtype.ext
  simp only [jordanCLM_val,sandwich_val,Submodule.coe_smul]
  change (X : Mat d)⁻¹*(U : Mat d)*((X : Mat d)⁻¹*(U : Mat d)*(X : Mat d)⁻¹) +
      ((X : Mat d)⁻¹*(U : Mat d)*(X : Mat d)⁻¹)*(U : Mat d)*(X : Mat d)⁻¹ =
    (2 : ℝ) • ((X : Mat d)⁻¹*((U : Mat d)*(X : Mat d)⁻¹*(U : Mat d))*(X : Mat d)⁻¹)
  rw [two_smul ℝ]
  noncomm_ring

attribute [local instance] OAI.CurrentKS.Hermitian.derivInvHPathNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Hermitian.derivInvHPathNormedSpace
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
lemma constraint_first {X Y S : ℝ → H d} {η : ℝ → (H d →L[ℝ] H d)} {a : ℝ}
    (hX : X a ∈ pd d) (hXd : DifferentiableAt ℝ X a) (hYd : DifferentiableAt ℝ Y a)
    (hSd : DifferentiableAt ℝ S a) (hηd : DifferentiableAt ℝ η a)
    (B : H d) (he : (fun s => invH (X s)+S s+η s (Y s)) =ᶠ[𝓝 a] fun _ => B) :
    sandwich (invH (X a)) (deriv X a) - η a (deriv Y a) =
      deriv S a + deriv η a (Y a) := by
  have hd := (((hasDerivAt_invH_path hX hXd.hasDerivAt).add hSd.hasDerivAt).add
    (hηd.hasDerivAt.clm_apply hYd.hasDerivAt)).deriv
  change deriv (fun s => invH (X s)+S s+η s (Y s)) a = _ at hd
  rw [he.deriv_eq,deriv_const] at hd
  linear_combination (norm := module) hd

lemma constraint_first_eventually [NeZero d] {X Y S : ℝ → H d} {η : ℝ → (H d →L[ℝ] H d)} {a : ℝ}
    (hX : X a ∈ pd d) (hXc : ContDiffAt ℝ 2 X a) (hYc : ContDiffAt ℝ 2 Y a)
    (hSc : ContDiffAt ℝ 2 S a) (hηc : ContDiffAt ℝ 2 η a)
    (B : H d) (he : (fun s => invH (X s)+S s+η s (Y s)) =ᶠ[𝓝 a] fun _ => B) :
    (fun s => sandwich (invH (X s)) (deriv X s) - η s (deriv Y s) - deriv S s - deriv η s (Y s))
      =ᶠ[𝓝 a] fun _ => 0 := by
  let F : ℝ → H d := fun s =>
    sandwich (invH (X s)) (deriv X s) - η s (deriv Y s) - deriv S s - deriv η s (Y s)
  have hpd : ∀ᶠ s in 𝓝 a, X s ∈ pd d :=
    hXc.continuousAt.eventually (isOpen_pd.mem_nhds hX)
  have hf : F =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [hpd,hXc.eventually (by norm_num),hYc.eventually (by norm_num),
      hSc.eventually (by norm_num),hηc.eventually (by norm_num),he.eventuallyEq_nhds] with s hx hxc hyc hsc hηc hec
    have hh := constraint_first hx (hxc.differentiableAt (by norm_num))
      (hyc.differentiableAt (by norm_num)) (hsc.differentiableAt (by norm_num))
      (hηc.differentiableAt (by norm_num)) B hec
    change sandwich (invH (X s)) (deriv X s) - η s (deriv Y s) - deriv S s - deriv η s (Y s) = 0
    rw [hh]
    module
  exact hf

lemma constraint_second [NeZero d] {X Y S : ℝ → H d} {η : ℝ → (H d →L[ℝ] H d)} {a : ℝ}
    (hX : X a ∈ pd d) (hXc : ContDiffAt ℝ 2 X a) (hYc : ContDiffAt ℝ 2 Y a)
    (hSc : ContDiffAt ℝ 2 S a) (hηc : ContDiffAt ℝ 2 η a)
    (B : H d) (he : (fun s => invH (X s)+S s+η s (Y s)) =ᶠ[𝓝 a] fun _ => B) :
    sandwich (invH (X a)) (deriv (deriv X) a) - η a (deriv (deriv Y) a) =
      jordanCLM (invH (X a)) (sandwich (invH (X a)) (deriv X a)) (deriv X a) +
      deriv (deriv S) a + (2 : ℝ) • (deriv η a (deriv Y a)) + deriv (deriv η) a (Y a) := by
  let F : ℝ → H d := fun s =>
    sandwich (invH (X s)) (deriv X s) - η s (deriv Y s) - deriv S s - deriv η s (Y s)
  have hf : F =ᶠ[𝓝 a] fun _ => 0 := constraint_first_eventually hX hXc hYc hSc hηc B he
  have hXd := (hXc.differentiableAt (by norm_num)).hasDerivAt
  have hYd := (hYc.differentiableAt (by norm_num)).hasDerivAt
  have hηd := (hηc.differentiableAt (by norm_num)).hasDerivAt
  have hXc' : ContDiffAt ℝ 1 (deriv X) a := hXc.derivWithin (by norm_num)
  have hXdd := (hXc'.differentiableAt (by norm_num)).hasDerivAt
  have hYc' : ContDiffAt ℝ 1 (deriv Y) a := hYc.derivWithin (by norm_num)
  have hYdd := (hYc'.differentiableAt (by norm_num)).hasDerivAt
  have hSc' : ContDiffAt ℝ 1 (deriv S) a := hSc.derivWithin (by norm_num)
  have hSdd := (hSc'.differentiableAt (by norm_num)).hasDerivAt
  have hηc' : ContDiffAt ℝ 1 (deriv η) a := hηc.derivWithin (by norm_num)
  have hηdd := (hηc'.differentiableAt (by norm_num)).hasDerivAt
  have hd := ((((hasDerivAt_invSandwich_path hX hXd hXdd).sub
    (hηd.clm_apply hYdd)).sub hSdd).sub (hηdd.clm_apply hYd)).deriv
  change deriv F a = _ at hd
  rw [hf.deriv_eq,deriv_const] at hd
  linear_combination (norm := module) -hd

end CurrentKS.Hermitian

end

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SandwichShiftInverse
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.traceCLM_apply _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
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

lemma sandwich_shift_inverse (X U : H d) (hX : X ∈ pd d) (r : ℝ) :
    sandwich (U-r • X) (invH X) = sandwich U (invH X) - (2*r) • U + r^2 • X := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  apply Subtype.ext
  change ((U : Mat d)-r • (X : Mat d)) * (X : Mat d)⁻¹ * ((U : Mat d)-r • (X : Mat d)) =
    (U : Mat d) * (X : Mat d)⁻¹ * (U : Mat d) - (2*r) • (U : Mat d) + r^2 • (X : Mat d)
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm, mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hx, Matrix.nonsing_inv_mul _ hx, mul_one]
  module

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

lemma trace_inverse_young (A X U : H d) (hA : A ∈ psdCone d) (hX : X ∈ pd d)
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    2*t*inner ℝ A U ≤ s*inner ℝ A (sandwich U (invH X)) + t^2/s*inner ℝ A X := by
  have hn := inner_nonneg_of_psd A (sandwich (U-(t/s) • X) (invH X)) hA
    (sandwich_psd _ _ hX.inv.posSemidef)
  rw [sandwich_shift_inverse X U hX,inner_add_right,inner_sub_right,
    real_inner_smul_right A U (2*(t/s)),real_inner_smul_right A X ((t/s)^2)] at hn
  have hh := mul_nonneg hs.le hn
  field_simp at hh ⊢
  nlinarith

end CurrentKS.Hermitian

end

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r757011_2 : NormedSpace ℝ (H d) := inferInstance
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

end
end CurrentKS.State

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

lemma inner_eta_rank_one (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z W : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ (eta c A x Z) W =
      ∑ i, c*psi (x i)*inner ℝ (A i) Z*inner ℝ (A i) W := by
  rw [eta_rank_one c A x Z hA hrank,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_smul_left (A i) W (c*psi (x i)*inner ℝ (A i) Z)

lemma energy_stationary_bound (c ε : ℝ) (hε : 0 ≤ ε) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X Y P Q U V : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    (∑ i, c*psi (x i)*(inner ℝ (A i) Q * inner ℝ (A i) (sandwich U (invH X)) +
      inner ℝ (A i) P * inner ℝ (A i) (sandwich V (invH Y)))) ≤ energy X Y P Q U V := by
  unfold energy
  rw [inner_sandwich (invH X) _ P, inner_sandwich (invH Y) _ Q,hP,hQ,inner_add_left,inner_add_left,
    real_inner_smul_left (Hermitian.one : H d) (sandwich U (invH X)) ε,
    real_inner_smul_left (Hermitian.one : H d) (sandwich V (invH Y)) ε,inner_one,inner_one,
    inner_eta_rank_one c A x Q _ hA hrank,inner_eta_rank_one c A x P _ hA hrank]
  have h₁ := mul_nonneg hε (realTrace_nonneg (sandwich_psd U (invH X) hX.inv.posSemidef))
  have h₂ := mul_nonneg hε (realTrace_nonneg (sandwich_psd V (invH Y) hY.inv.posSemidef))
  have he : (∑ i, c*psi (x i)*(inner ℝ (A i) Q * inner ℝ (A i) (sandwich U (invH X)) +
      inner ℝ (A i) P * inner ℝ (A i) (sandwich V (invH Y)))) =
      (∑ i, c*psi (x i)*inner ℝ (A i) Q * inner ℝ (A i) (sandwich U (invH X))) +
      (∑ i, c*psi (x i)*inner ℝ (A i) P * inner ℝ (A i) (sandwich V (invH Y))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  linarith

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Line
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar Filter
open scoped BigOperators Topology

variable {N : ℕ}

lemma hasDerivAt_line_coord (x h : Coordinates N) (a : ℝ) (i : Fin N) :
    HasDerivAt (fun s => line x h s i) (h i) a := by
  have hh := (hasDerivAt_const a (x i)).add ((hasDerivAt_id a).mul_const (h i))
  simp only [zero_add,one_mul] at hh
  exact hh

lemma contDiff_line (x h : Coordinates N) {n : WithTop ℕ∞} : ContDiff ℝ n (line x h) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.add (contDiff_id.mul contDiff_const)

lemma eventually_line_interior (x h : Coordinates N) {a : ℝ}
    (hx : ∀ i, |line x h a i| < 1) : ∀ᶠ s in 𝓝 a, ∀ i, |line x h s i| < 1 := by
  apply Filter.eventually_all.mpr
  intro i
  exact ((hasDerivAt_line_coord x h a i).continuousAt.abs).eventually (eventually_lt_nhds (hx i))

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NegativeWeight
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p4
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
lemma mixedTerm_bound {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X Y P Q U V : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d)
    (hP : sandwich (invH X) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    mixedTerm c A x h P Q U V ≤ energy X Y P Q U V + (c/2)*negativeWeight A x h X Y P Q := by
  have hi (i : Fin N) := mixed_young_bound hc
    (inner_nonneg_of_psd (A i) P (hA i) hPpos)
    (inner_nonneg_of_psd (A i) Q (hA i) hQpos)
    (inner_nonneg_of_psd (A i) X (hA i) hX.posSemidef)
    (inner_nonneg_of_psd (A i) Y (hA i) hY.posSemidef)
    (derivative_square_le (hx i))
    (trace_inverse_young (A i) X U (hA i) hX (psi_pos (hx i)) (psi₁ (x i)*h i))
    (trace_inverse_young (A i) Y V (hA i) hY (psi_pos (hx i)) (psi₁ (x i)*h i))
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hi i)
  have he := energy_stationary_bound c ε hε A x hA hrank X Y P Q U V hX hY hP hQ
  change mixedTerm c A x h P Q U V ≤ _ at hh
  rw [Finset.sum_add_distrib] at hh
  have hf : (∑ i, (c/2)*kappa (x i)*(h i)^2*
      (inner ℝ (A i) Y*inner ℝ (A i) P + inner ℝ (A i) X*inner ℝ (A i) Q)) =
      (c/2)*negativeWeight A x h X Y P Q := by
    rw [negativeWeight,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hf] at hh
  exact hh.trans (add_le_add he (le_refl _))

lemma secondExpansion_bound {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X Y P Q U V : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d)
    (hP : sandwich (invH X) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    2*energy X Y P Q U V + mixedTerm c A x h P Q U V - c*negativeWeight A x h X Y P Q ≤
      3*energy X Y P Q U V - (c/2)*negativeWeight A x h X Y P Q := by
  have hh := mixedTerm_bound hc hε A x h hx hA hrank X Y P Q U V hX hY hPpos hQpos hP hQ
  linarith

attribute [local instance] OAI.CurrentKS.State.negativeWeightNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.State.negativeWeightNormedSpace
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
lemma hasDerivAt_S_line (A : Fin N → H d) (x h : Coordinates N) (a : ℝ) :
    HasDerivAt (fun s => S A (line x h s)) (S A h) a := by
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_line_coord x h a i).smul_const (A i)

lemma eta₁_apply (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (Y : H d) :
    eta₁ c A x h Y = ∑ i, (c*psi₁ (x i)*h i) • sandwich (A i) Y := by
  simp only [eta₁,_root_.sum_apply,_root_.smul_apply,sandwichCLM_apply]

lemma eta₂_apply (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (Y : H d) :
    eta₂ c A x h Y = ∑ i, (-c*kappa (x i)*(h i)^2) • sandwich (A i) Y := by
  simp only [eta₂,_root_.sum_apply,_root_.smul_apply,sandwichCLM_apply]

lemma hasDerivAt_eta_line (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (a : ℝ)
    (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => eta c A (line x h s)) (eta₁ c A (line x h a) h) a := by
  unfold eta eta₁
  apply HasDerivAt.fun_sum
  intro i _
  convert ((((hasDerivAt_psi (hx i)).comp a (hasDerivAt_line_coord x h a i)).const_mul c).smul_const
    (sandwichCLM (A i))) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring_nf

lemma hasDerivAt_eta₁_line (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (a : ℝ)
    (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => eta₁ c A (line x h s) h) (eta₂ c A (line x h a) h) a := by
  unfold eta₁ eta₂
  apply HasDerivAt.fun_sum
  intro i _
  convert (((((hasDerivAt_psi₁ (hx i)).comp a (hasDerivAt_line_coord x h a i)).const_mul c).mul_const (h i)).smul_const
    (sandwichCLM (A i))) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring_nf

lemma hasDerivAt_deriv_eta_line (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (a : ℝ)
    (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (deriv (fun s => eta c A (line x h s))) (eta₂ c A (line x h a) h) a := by
  apply (hasDerivAt_eta₁_line c A x h a hx).congr_of_eventuallyEq
  filter_upwards [eventually_line_interior x h hx] with s hs
  exact (hasDerivAt_eta_line c A x h s hs).deriv

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_DerivPathObjective
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p2
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.State.derivPathObjectiveNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.State.derivPathObjectiveNormedSpace
lemma hasDerivAt_path_objective {X Y : ℝ → H d} {U V : H d} {a : ℝ}
    (hX : HasDerivAt X U a) (hY : HasDerivAt Y V a) (ε t : ℝ) :
    HasDerivAt (fun s => t+ε*Hermitian.realTrace (X s+Y s)) (ε*Hermitian.realTrace (U+V)) a := by
  have hh := (traceCLM (d := d)).hasFDerivAt.comp_hasDerivAt a (hX.add hY)
  have hh' : HasDerivAt (fun s => Hermitian.realTrace (X s+Y s)) (Hermitian.realTrace (U+V)) a :=
    (hh.congr_deriv (traceCLM_apply (U + V))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => (traceCLM_apply (X s + Y s)).symm)
  have hhh := (hasDerivAt_const a t).add (hh'.const_mul ε)
  simp only [zero_add] at hhh
  exact hhh

lemma deriv_deriv_path_objective {X Y : ℝ → H d} {a : ℝ}
    (hX : ContDiffAt ℝ 2 X a) (hY : ContDiffAt ℝ 2 Y a) (ε t : ℝ) :
    deriv (deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s))) a =
      ε*Hermitian.realTrace (deriv (deriv X) a+deriv (deriv Y) a) := by
  have hX' : ContDiffAt ℝ 1 (deriv X) a := hX.derivWithin (by norm_num)
  have hY' : ContDiffAt ℝ 1 (deriv Y) a := hY.derivWithin (by norm_num)
  have he : deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s)) =ᶠ[𝓝 a]
      fun s => 0+ε*Hermitian.realTrace (deriv X s+deriv Y s) := by
    filter_upwards [hX.eventually (by norm_num),hY.eventually (by norm_num)] with s hx hy
    simpa only [zero_add] using (hasDerivAt_path_objective
      (hx.differentiableAt (by norm_num)).hasDerivAt (hy.differentiableAt (by norm_num)).hasDerivAt ε t).deriv
  rw [he.deriv_eq]
  exact (hasDerivAt_path_objective (hX'.differentiableAt (by norm_num)).hasDerivAt
    (hY'.differentiableAt (by norm_num)).hasDerivAt ε 0).deriv

lemma first_response_path (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hXd : DifferentiableAt ℝ X 0) (hYd : DifferentiableAt ℝ Y 0)
    (B : H d)
    (he : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => B) :
    sandwich (invH (X 0)) (deriv X 0) - eta c A x (deriv Y 0) =
      S A h+eta₁ c A x h (Y 0) := by
  have hS := hasDerivAt_S_line A x h 0
  have hη := hasDerivAt_eta_line c A x h 0 (by simpa using hx)
  have hh := constraint_first hX hXd hYd hS.differentiableAt hη.differentiableAt B he
  rw [hS.deriv,hη.deriv] at hh
  simpa only [line_zero] using hh

lemma first_response_path_neg (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) {X Y : ℝ → H d}
    (hY : Y 0 ∈ pd d) (hXd : DifferentiableAt ℝ X 0) (hYd : DifferentiableAt ℝ Y 0)
    (B : H d)
    (he : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => B) :
    sandwich (invH (Y 0)) (deriv Y 0) - eta c A x (deriv X 0) =
      -S A h+eta₁ c A x h (X 0) := by
  have hS := (hasDerivAt_S_line A x h 0).neg
  have hη := hasDerivAt_eta_line c A x h 0 (by simpa using hx)
  have hh := constraint_first hY hYd hXd hS.differentiableAt hη.differentiableAt B
    (by simp only [sub_eq_add_neg] at he; exact he)
  rw [hS.deriv,hη.deriv] at hh
  simpa only [line_zero] using hh

lemma deriv_deriv_S_line (A : Fin N → H d) (x h : Coordinates N) (a : ℝ) :
    deriv (deriv (fun s => S A (line x h s))) a = 0 := by
  have he : deriv (fun s => S A (line x h s)) = fun _ => S A h := by
    funext s
    exact (hasDerivAt_S_line A x h s).deriv
  rw [he,deriv_const]

lemma second_response_path [NeZero d] (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hXc : ContDiffAt ℝ 2 X 0) (hYc : ContDiffAt ℝ 2 Y 0)
    (B : H d)
    (he : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => B) :
    sandwich (invH (X 0)) (deriv (deriv X) 0) - eta c A x (deriv (deriv Y) 0) =
      jordanCLM (invH (X 0)) (sandwich (invH (X 0)) (deriv X 0)) (deriv X 0) +
        (2 : ℝ) • eta₁ c A x h (deriv Y 0) + eta₂ c A x h (Y 0) := by
  have hηc : ContDiffAt ℝ 2 (fun s => eta c A (line x h s)) 0 :=
    by
    have hc : ContDiffAt ℝ 2 (eta c A) (line x h 0) := by
      simpa only [line_zero] using contDiffAt_eta c A hx
    exact hc.comp 0 (contDiff_line x h).contDiffAt
  have hh := constraint_second hX hXc hYc
    ((contDiff_S A).comp (contDiff_line x h)).contDiffAt hηc B he
  simp only [Function.comp_def] at hh
  rw [deriv_deriv_S_line,add_zero,(hasDerivAt_eta_line c A x h 0 (by simpa using hx)).deriv,
    (hasDerivAt_deriv_eta_line c A x h 0 (by simpa using hx)).deriv] at hh
  simpa only [line_zero] using hh

lemma deriv_deriv_neg_S_line (A : Fin N → H d) (x h : Coordinates N) (a : ℝ) :
    deriv (deriv (fun s => -S A (line x h s))) a = 0 := by
  have he : deriv (fun s => -S A (line x h s)) = fun _ => -S A h := by
    funext s
    exact ((hasDerivAt_S_line A x h s).neg).deriv
  rw [he,deriv_const]

lemma second_response_path_neg [NeZero d] (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) {X Y : ℝ → H d}
    (hY : Y 0 ∈ pd d) (hXc : ContDiffAt ℝ 2 X 0) (hYc : ContDiffAt ℝ 2 Y 0)
    (B : H d)
    (he : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => B) :
    sandwich (invH (Y 0)) (deriv (deriv Y) 0) - eta c A x (deriv (deriv X) 0) =
      jordanCLM (invH (Y 0)) (sandwich (invH (Y 0)) (deriv Y 0)) (deriv Y 0) +
        (2 : ℝ) • eta₁ c A x h (deriv X 0) + eta₂ c A x h (X 0) := by
  have hηc : ContDiffAt ℝ 2 (fun s => eta c A (line x h s)) 0 := by
    have hc : ContDiffAt ℝ 2 (eta c A) (line x h 0) := by
      simpa only [line_zero] using contDiffAt_eta c A hx
    exact hc.comp 0 (contDiff_line x h).contDiffAt
  have hh := constraint_second hY hYc hXc
    ((contDiff_S A).comp (contDiff_line x h)).neg.contDiffAt hηc B
    (by simp only [sub_eq_add_neg] at he; exact he)
  simp only [Function.comp_def] at hh
  rw [deriv_deriv_neg_S_line,add_zero,(hasDerivAt_eta_line c A x h 0 (by simpa using hx)).deriv,
    (hasDerivAt_deriv_eta_line c A x h 0 (by simpa using hx)).deriv] at hh
  simpa only [line_zero] using hh

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StationaryPairing
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

lemma stationary_pairing (X Y P Q U V : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (ε : ℝ)
    (hP : sandwich (invH X) P = η Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = η P + ε • (Hermitian.one : H d)) :
    inner ℝ P (sandwich (invH X) U - η V) +
      inner ℝ Q (sandwich (invH Y) V - η U) = ε * Hermitian.realTrace (U+V) := by
  rw [inner_sub_right, inner_sub_right, inner_sandwich, inner_sandwich, hP, hQ]
  rw [inner_add_left, inner_add_left, inner_smul_leftH, inner_smul_leftH,
    inner_one, inner_one]
  rw [hη Q U, hη P V]
  simp only [realTrace_add]
  ring

end CurrentKS.Variational

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma inner_eta₁ (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (P Y : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ P (eta₁ c A x h Y) =
      ∑ i, c*psi₁ (x i)*h i*inner ℝ (A i) Y*inner ℝ (A i) P := by
  rw [eta₁_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) Y (hA i) (hrank i),
    real_inner_smul_right P _ (c*psi₁ (x i)*h i),
    real_inner_smul_right P (A i) (inner ℝ (A i) Y),real_inner_comm P (A i)]
  ring

lemma inner_eta₂ (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (P Y : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ P (eta₂ c A x h Y) =
      ∑ i, -c*kappa (x i)*(h i)^2*inner ℝ (A i) Y*inner ℝ (A i) P := by
  rw [eta₂_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) Y (hA i) (hrank i),
    real_inner_smul_right P _ (-c*kappa (x i)*(h i)^2),
    real_inner_smul_right P (A i) (inner ℝ (A i) Y),real_inner_comm P (A i)]
  ring

lemma first_input_pairing (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (X Y P Q : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ P (S A h + eta₁ c A x h Y) + inner ℝ Q (-S A h + eta₁ c A x h X) =
      ∑ i, h i*((1+c*psi₁ (x i)*inner ℝ (A i) Y)*inner ℝ (A i) P -
        (1-c*psi₁ (x i)*inner ℝ (A i) X)*inner ℝ (A i) Q) := by
  rw [inner_add_right,inner_add_right,inner_neg_right,inner_eta₁ c A x h P Y hA hrank,
    inner_eta₁ c A x h Q X hA hrank]
  simp only [S,inner_sum]
  rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right P (A i) (h i),real_inner_smul_right Q (A i) (h i),
    real_inner_comm P (A i),real_inner_comm Q (A i)]
  ring

lemma second_input_pairing (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (X Y P Q U V : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ P (jordanCLM (invH X) (sandwich (invH X) U) U +
        (2 : ℝ) • eta₁ c A x h V + eta₂ c A x h Y) +
      inner ℝ Q (jordanCLM (invH Y) (sandwich (invH Y) V) V +
        (2 : ℝ) • eta₁ c A x h U + eta₂ c A x h X) =
      2*energy X Y P Q U V + mixedTerm c A x h P Q U V - c*negativeWeight A x h X Y P Q := by
  rw [jordan_inverse_square,jordan_inverse_square]
  simp only [inner_add_right]
  rw [real_inner_smul_right P _ (2 : ℝ),real_inner_smul_right P _ (2 : ℝ),
    real_inner_smul_right Q _ (2 : ℝ),real_inner_smul_right Q _ (2 : ℝ)]
  rw [inner_eta₁ c A x h P V hA hrank,inner_eta₁ c A x h Q U hA hrank,
    inner_eta₂ c A x h P Y hA hrank,inner_eta₂ c A x h Q X hA hrank]
  have he : 2*(∑ i, c*psi₁ (x i)*h i*inner ℝ (A i) V*inner ℝ (A i) P) +
      2*(∑ i, c*psi₁ (x i)*h i*inner ℝ (A i) U*inner ℝ (A i) Q) +
      (∑ i, -c*kappa (x i)*(h i)^2*inner ℝ (A i) Y*inner ℝ (A i) P) +
      (∑ i, -c*kappa (x i)*(h i)^2*inner ℝ (A i) X*inner ℝ (A i) Q) =
      mixedTerm c A x h P Q U V - c*negativeWeight A x h X Y P Q := by
    unfold mixedTerm negativeWeight
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change _ = 2*(inner ℝ P (sandwich (invH X) (sandwich U (invH X))) +
    inner ℝ Q (sandwich (invH Y) (sandwich V (invH Y)))) + _ - _
  linarith

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PathObjectiveFirst
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State

section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p6
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6
lemma path_objective_first {c ε : ℝ} (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) (hA : ∀ i, A i ∈ psdCone d)
    (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (P Q : H d) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hY : Y 0 ∈ pd d)
    (hXd : DifferentiableAt ℝ X 0) (hYd : DifferentiableAt ℝ Y 0)
    (hP : sandwich (invH (X 0)) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH (Y 0)) Q = eta c A x P + ε • (Hermitian.one : H d))
    (BX BY : H d) (t : ℝ)
    (heX : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => BX)
    (heY : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => BY) :
    deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s)) 0 =
      ∑ i, h i*((1+c*psi₁ (x i)*inner ℝ (A i) (Y 0))*inner ℝ (A i) P -
        (1-c*psi₁ (x i)*inner ℝ (A i) (X 0))*inner ℝ (A i) Q) := by
  rw [(hasDerivAt_path_objective hXd.hasDerivAt hYd.hasDerivAt ε t).deriv]
  erw [← stationary_pairing (X 0) (Y 0) P Q (deriv X 0) (deriv Y 0)
    (eta c A x) (eta_symmetric c A x) ε hP hQ]
  erw [first_response_path c A x h hx hX hXd hYd BX heX,
    first_response_path_neg c A x h hx hY hXd hYd BY heY]
  exact first_input_pairing c A x h (X 0) (Y 0) P Q hA hrank

lemma path_objective_second [NeZero d] {c ε : ℝ} (A : Fin N → H d) (x h : Coordinates N)
    (hx : ∀ i, |x i| < 1) (hA : ∀ i, A i ∈ psdCone d)
    (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (P Q : H d) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hY : Y 0 ∈ pd d)
    (hXc : ContDiffAt ℝ 2 X 0) (hYc : ContDiffAt ℝ 2 Y 0)
    (hP : sandwich (invH (X 0)) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH (Y 0)) Q = eta c A x P + ε • (Hermitian.one : H d))
    (BX BY : H d) (t : ℝ)
    (heX : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => BX)
    (heY : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => BY) :
    deriv (deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s))) 0 =
      2*energy (X 0) (Y 0) P Q (deriv X 0) (deriv Y 0) +
      mixedTerm c A x h P Q (deriv X 0) (deriv Y 0) - c*negativeWeight A x h (X 0) (Y 0) P Q := by
  rw [deriv_deriv_path_objective hXc hYc ε t]
  erw [← stationary_pairing (X 0) (Y 0) P Q (deriv (deriv X) 0) (deriv (deriv Y) 0)
    (eta c A x) (eta_symmetric c A x) ε hP hQ]
  erw [second_response_path c A x h hx hX hXc hYc BX heX,
    second_response_path_neg c A x h hx hY hXc hYc BY heY]
  exact second_input_pairing c A x h (X 0) (Y 0) P Q (deriv X 0) (deriv Y 0) hA hrank

lemma path_objective_second_le [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (P Q : H d) (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d) {X Y : ℝ → H d}
    (hX : X 0 ∈ pd d) (hY : Y 0 ∈ pd d)
    (hXc : ContDiffAt ℝ 2 X 0) (hYc : ContDiffAt ℝ 2 Y 0)
    (hP : sandwich (invH (X 0)) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH (Y 0)) Q = eta c A x P + ε • (Hermitian.one : H d))
    (BX BY : H d) (t : ℝ)
    (heX : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0] fun _ => BX)
    (heY : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0] fun _ => BY) :
    deriv (deriv (fun s => t+ε*Hermitian.realTrace (X s+Y s))) 0 ≤
      3*energy (X 0) (Y 0) P Q (deriv X 0) (deriv Y 0) - (c/2)*negativeWeight A x h (X 0) (Y 0) P Q := by
  rw [path_objective_second A x h hx hA hrank P Q hX hY hXc hYc hP hQ BX BY t heX heY]
  exact secondExpansion_bound hc hε A x h hx hA hrank (X 0) (Y 0) P Q
    (deriv X 0) (deriv Y 0) hX hY hPpos hQpos hP hQ

end
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FaceValueDirectionVariations
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p3
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p3
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p3
attribute [local instance] OAI.CurrentKS.State.faceValueDirectionNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.State.faceValueDirectionNormedSpace
theorem face_value_direction_variations_oai [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (S₀ : H d) (K : ℝ) (hlo : -K • (Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S₀+S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S₀+S A x) (eta c A x), objective ε z ≤ objective ε w)
    (P Q : H d) (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d)
    (hP : sandwich (invH z.2.1) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH z.2.2) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    ∃ U V : H d,
      sandwich (invH z.2.1) U-eta c A x V = S A h+eta₁ c A x h z.2.2 ∧
      sandwich (invH z.2.2) V-eta c A x U = -S A h+eta₁ c A x h z.2.1 ∧
      deriv (fun s => value ε (S₀+S A (line x h s)) (eta c A (line x h s))) 0 =
        ∑ i, h i*((1+c*psi₁ (x i)*inner ℝ (A i) z.2.2)*inner ℝ (A i) P-
          (1-c*psi₁ (x i)*inner ℝ (A i) z.2.1)*inner ℝ (A i) Q) ∧
      deriv (deriv (fun s => value ε (S₀+S A (line x h s)) (eta c A (line x h s)))) 0 ≤
        3*energy z.2.1 z.2.2 P Q U V-(c/2)*negativeWeight A x h z.2.1 z.2.2 P Q := by
  have hS : ContDiffAt ℝ ∞ (fun s => S₀+S A (line x h s)) 0 :=
    contDiffAt_const.add (((contDiff_S A).comp (contDiff_line x h)).contDiffAt)
  have hη : ContDiffAt ℝ ∞ (fun s => eta c A (line x h s)) 0 := by
    have he : ContDiffAt ℝ ∞ (eta c A) (line x h 0) := by
      simpa only [line_zero] using contDiffAt_eta c A hx
    exact he.comp 0 (contDiff_line x h).contDiffAt
  have hp : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ B ∈ psdCone d, eta c A (line x h s) B ∈ psdCone d := by
    filter_upwards [eventually_line_interior x h (a := 0) (by simpa only [line_zero] using hx)] with s hs
    exact eta_positive hc A (fun i => (hs i).le)
  have hs : ∀ᶠ s in 𝓝 (0 : ℝ), SymmetricMap (eta c A (line x h s)) :=
    Filter.Eventually.of_forall fun s => eta_symmetric c A _
  obtain ⟨g,hg,hgc,hres,hd,hdd⟩ := value_derivatives_majorant ε hε
    (fun s => S₀+S A (line x h s)) (fun s => eta c A (line x h s)) 0 hS hη hp hs
    (K := K) (by simpa only [line_zero] using hlo)
    (by simpa only [line_zero] using hhi) z
    (by simpa only [line_zero] using hz) (by simpa only [line_zero] using hmin)
  let X : ℝ → H d := fun s => (g s).1
  let Y : ℝ → H d := fun s => (g s).2
  have hX0 : X 0 = z.2.1 := congrArg Prod.fst hg
  have hY0 : Y 0 = z.2.2 := congrArg Prod.snd hg
  have hX : X 0 ∈ pd d := hX0 ▸ hz.1.1
  have hY : Y 0 ∈ pd d := hY0 ▸ hz.1.2
  have hXc : ContDiffAt ℝ 2 X 0 := contDiffAt_infty.mp hgc.fst 2
  have hYc : ContDiffAt ℝ 2 Y 0 := contDiffAt_infty.mp hgc.snd 2
  have heX : (fun s => invH (X s)+S A (line x h s)+eta c A (line x h s) (Y s)) =ᶠ[𝓝 0]
      fun _ => z.1 • (Hermitian.one : H d)-S₀ := by
    filter_upwards [hres] with s hs
    have he := sub_eq_zero.mp (congrArg Prod.fst hs)
    change invH (X s)+(S₀+S A (line x h s))+eta c A (line x h s) (Y s) = _ at he
    rw [eq_sub_iff_add_eq]
    convert he using 1 <;> first | rfl | abel
  have heY : (fun s => invH (Y s)-S A (line x h s)+eta c A (line x h s) (X s)) =ᶠ[𝓝 0]
      fun _ => z.1 • (Hermitian.one : H d)+S₀ := by
    filter_upwards [hres] with s hs
    have he := sub_eq_zero.mp (congrArg Prod.snd hs)
    change invH (Y s)-(S₀+S A (line x h s))+eta c A (line x h s) (X s) = _ at he
    apply (sub_eq_iff_eq_add).mp
    convert he using 1 <;> first | rfl | abel
  have hPX : sandwich (invH (X 0)) P = eta c A x Q+ε • (Hermitian.one : H d) := by rw [hX0]; exact hP
  have hQY : sandwich (invH (Y 0)) Q = eta c A x P+ε • (Hermitian.one : H d) := by rw [hY0]; exact hQ
  refine ⟨deriv X 0,deriv Y 0,?_,?_,?_,?_⟩
  · simpa only [hX0,hY0] using first_response_path c A x h hx hX
      (hXc.differentiableAt (by norm_num)) (hYc.differentiableAt (by norm_num)) _ heX
  · simpa only [hX0,hY0] using first_response_path_neg c A x h hx hY
      (hXc.differentiableAt (by norm_num)) (hYc.differentiableAt (by norm_num)) _ heY
  · rw [hd]
    simpa only [objective,hX0,hY0] using path_objective_first A x h hx hA hrank P Q hX hY
      (hXc.differentiableAt (by norm_num)) (hYc.differentiableAt (by norm_num)) hPX hQY _ _ z.1 heX heY
  · apply hdd.trans
    simpa only [objective,hX0,hY0] using path_objective_second_le hc hε.le A x h hx hA hrank
      P Q hPpos hQpos hX hY hXc hYc hPX hQY _ _ z.1 heX heY

end
end CurrentKS.State

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.State.face_value_direction_variations_oai := @OAI.CurrentKS.State.face_value_direction_variations_oai
