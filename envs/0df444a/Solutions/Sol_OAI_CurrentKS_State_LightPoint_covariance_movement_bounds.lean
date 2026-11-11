-- Prove2me | solution 1 for OAI.CurrentKS.State.LightPoint.covariance_movement_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:30.180925+00:00
-- url     : https://prove2.me/submissions/268750e4-e2d8-49ab-8e77-0a9df0a6c028

import Mathlib
import Definitions.Def_OAIQ241TT002

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

lemma psi_le_one {x : ℝ} (hx : |x| < 1) : psi x ≤ 1 := by
  have hp := psi_pos hx
  have hc := psi_cube hx
  nlinarith [sq_nonneg x, sq_nonneg (psi x - 1)]

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_Alpha
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section

lemma psi_even (x : ℝ) : psi (-x) = psi x := by simp [psi]

lemma psi_ge_base {x : ℝ} (hx : |x| < 1) : 1-x^2 ≤ psi x := by
  have hp := psi_pos hx
  have hle := psi_le_one hx
  have hc := psi_cube hx
  have hs : psi x ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hs)]

lemma alpha_neg (x A B : ℝ) : alpha (-x) B A = beta x A B := by
  simp [alpha,beta] <;> ring
lemma beta_neg (x A B : ℝ) : beta (-x) B A = alpha x A B := by
  simp [alpha,beta] <;> ring

lemma coefficient_bounds_nonneg {x A B : ℝ} (hx : |x| < 1) (hx0 : 0 ≤ x)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    (2/3 : ℝ) ≤ alpha x A B ∧ alpha x A B ≤ 1 ∧
    1 ≤ beta x A B ∧ beta x A B ≤ 2/(1-x^2) ∧
    beta x A B * (1-x) ≤ 1+x := by
  have hr := base_pos hx
  have xp := (abs_lt.mp hx).2
  have hden : 0 < 3*(1-x^2) := by positivity
  have hmx : 0 ≤ 1-x := by linarith
  have hm := mul_le_mul_of_nonneg_left hBl.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx0)
  have hmA := mul_le_mul_of_nonneg_left hAl.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx0)
  have hl : 2*x*B/(3*(1-x^2)) ≤ (1/3 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (1-x)]
  have hpB : 0 ≤ 2*x*B/(3*(1-x^2)) := by positivity
  have hpA : 0 ≤ 2*x*A/(3*(1-x^2)) := by positivity
  refine ⟨by unfold alpha; linarith, by unfold alpha; linarith,
    by unfold beta; linarith, ?_, ?_⟩
  · unfold beta
    apply (le_div_iff₀ hr).mpr
    field_simp
    nlinarith [sq_nonneg x]
  · have he : beta x A B * (1-x) =
        ((3*(1-x^2)+2*x*A)*(1-x))/(3*(1-x^2)) := by
      unfold beta
      field_simp
    rw [he]
    apply (div_le_iff₀ hden).mpr
    have hmA' := mul_le_mul_of_nonneg_right hmA hmx
    nlinarith [mul_nonneg hx0 hr.le]

lemma product_bounds {x A B : ℝ} (hx : |x| < 1)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    (2/3 : ℝ) ≤ alpha x A B * beta x A B ∧
    alpha x A B * beta x A B ≤ 2/(1-x^2) ∧
    0 < alpha x A B ∧ 0 < beta x A B := by
  have nonneg_case : ∀ y C D : ℝ, |y| < 1 → 0 ≤ y → 0 < C → 0 < D →
      C < 1+y → D < 1-y →
      (2/3 : ℝ) ≤ alpha y C D * beta y C D ∧
      alpha y C D * beta y C D ≤ 2/(1-y^2) ∧
      0 < alpha y C D ∧ 0 < beta y C D := by
    intro y C D hy hy0 hC hD hCl hDl
    obtain ⟨ha,ha',hb,hb',_⟩ := coefficient_bounds_nonneg hy hy0 hC hD hCl hDl
    have hap : 0 < alpha y C D := by linarith
    have hbp : 0 < beta y C D := by linarith
    refine ⟨?_,?_,hap,hbp⟩
    · nlinarith [mul_nonneg hap.le (sub_nonneg.mpr hb)]
    · nlinarith [mul_nonneg hbp.le (sub_nonneg.mpr ha')]
  by_cases hx0 : 0 ≤ x
  · exact nonneg_case x A B hx hx0 hA hB hAl hBl
  · have hh := nonneg_case (-x) B A (by simpa) (by linarith) hB hA
      (by linarith) (by linarith)
    simpa only [alpha_neg,beta_neg,neg_sq,mul_comm,and_assoc,and_comm,and_left_comm] using hh

lemma light_squares_nonneg {x A B : ℝ} (hx : |x| < 1) (hx0 : 0 ≤ x)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    alpha x A B * A^2 ≤ 3 * beta x A B * psi x ∧
    beta x A B * B^2 ≤ 3 * alpha x A B * psi x := by
  obtain ⟨ha,ha',hb,_,hb'⟩ := coefficient_bounds_nonneg hx hx0 hA hB hAl hBl
  have hp := psi_pos hx
  have hpr := psi_ge_base hx
  have hr := base_pos hx
  have hm : 0 < 1-x := by have h := (abs_lt.mp hx).2; linarith
  have hA2 : A^2 ≤ 1-x^2+2*x*A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAl.le) (by linarith : 0 ≤ A+1-x)]
  have hEq : 3*(1-x^2)*beta x A B = 3*(1-x^2)+2*x*A := by
    unfold beta
    field_simp
  have hAs : A^2 ≤ 3*beta x A B*psi x := by
    have hmul := mul_le_mul_of_nonneg_left hpr (by linarith : 0 ≤ 3*beta x A B)
    nlinarith
  have hBs : beta x A B * B^2 ≤ 1-x^2 := by
    have hbpos : 0 ≤ beta x A B := by linarith
    have hsq : B^2 ≤ (1-x)^2 := by nlinarith
    have hv := mul_le_mul_of_nonneg_left hsq hbpos
    have hw := mul_le_mul_of_nonneg_right hb' hm.le
    nlinarith
  constructor
  · nlinarith [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr ha')]
  · nlinarith [mul_nonneg hp.le (sub_nonneg.mpr ha)]

lemma light_squares {x A B : ℝ} (hx : |x| < 1)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    alpha x A B * A^2 ≤ 3 * beta x A B * psi x ∧
    beta x A B * B^2 ≤ 3 * alpha x A B * psi x := by
  by_cases hx0 : 0 ≤ x
  · exact light_squares_nonneg hx hx0 hA hB hAl hBl
  · have hh := light_squares_nonneg (x := -x) (A := B) (B := A)
      (by simpa) (by linarith) hB hA (by linarith) (by linarith)
    simpa only [alpha_neg,beta_neg,psi_even,and_comm] using hh

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_Alpha2
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section

lemma light_rescaling_pos {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    0 < Alpha c x a b ∧ 0 < Beta c x a b ∧ 0 < scaleT c x a b ∧
    0 < scaleL c x a b ∧ 0 < scaleM c x a b := by
  have hap := mul_pos (mul_pos hc (psi_pos hx)) ha
  have hbp := mul_pos (mul_pos hc (psi_pos hx)) hb
  obtain ⟨_,_,hA,hB⟩ := product_bounds hx hap hbp hal hbl
  have hT : 0 < scaleT c x a b := Real.sqrt_pos.mpr (div_pos (mul_pos hA hB) (psi_pos hx))
  exact ⟨hA,hB,hT,div_pos hA hT,div_pos hB hT⟩

lemma scaleT_sq {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    scaleT c x a b^2 = Alpha c x a b*Beta c x a b/psi x := by
  obtain ⟨hA,hB,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  exact Real.sq_sqrt (div_nonneg (mul_nonneg hA.le hB.le) (psi_pos hx).le)

lemma scaleL_mul_scaleM {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    scaleL c x a b*scaleM c x a b = psi x := by
  obtain ⟨hA,hB,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  rw [scaleL,scaleM,div_mul_div_comm,← pow_two,scaleT_sq hc hx ha hb hal hbl]
  field_simp [hA.ne',hB.ne']

lemma rescaled_square_bounds {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    (scaleL c x a b*a)^2 ≤ 3*c⁻¹^2 ∧ (scaleM c x a b*b)^2 ≤ 3*c⁻¹^2 := by
  obtain ⟨hA,hB,hT,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  have hp := psi_pos hx
  obtain ⟨hL,hM⟩ := light_squares hx (mul_pos (mul_pos hc hp) ha)
    (mul_pos (mul_pos hc hp) hb) hal hbl
  change Alpha c x a b*(c*psi x*a)^2 ≤ 3*Beta c x a b*psi x at hL
  change Beta c x a b*(c*psi x*b)^2 ≤ 3*Alpha c x a b*psi x at hM
  have heL : c^2*(scaleL c x a b*a)^2 =
      Alpha c x a b*(c*psi x*a)^2/(Beta c x a b*psi x) := by
    rw [scaleL,mul_pow,div_pow,scaleT_sq hc hx ha hb hal hbl]
    field_simp [hA.ne',hB.ne',hp.ne']
  have heM : c^2*(scaleM c x a b*b)^2 =
      Beta c x a b*(c*psi x*b)^2/(Alpha c x a b*psi x) := by
    rw [scaleM,mul_pow,div_pow,scaleT_sq hc hx ha hb hal hbl]
    field_simp [hA.ne',hB.ne',hp.ne']
  have hL' : c^2*(scaleL c x a b*a)^2 ≤ 3 := by
    rw [heL]
    exact (div_le_iff₀ (mul_pos hB hp)).mpr (by nlinarith)
  have hM' : c^2*(scaleM c x a b*b)^2 ≤ 3 := by
    rw [heM]
    exact (div_le_iff₀ (mul_pos hA hp)).mpr (by nlinarith)
  rw [inv_pow,← div_eq_mul_inv]
  exact ⟨(le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith),
    (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith)⟩

end
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

lemma sandwich_inner_nonneg (X A : H d) (hX : X ∈ psdCone d) :
    0 ≤ inner ℝ A (sandwich X A) := by
  obtain ⟨R,hR,hRX⟩ := exists_psd_square X hX
  have he : sandwich R one = X := by
    apply Subtype.ext
    change (R : Mat d)*1*(R : Mat d) = (X : Mat d)
    simpa only [mul_one] using hRX
  rw [← he,← inner_sandwich_square]
  exact real_inner_self_nonneg

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

lemma smul_order {A B : H d} (h : A ≤ B) {r : ℝ} (hr : 0 ≤ r) : r • A ≤ r • B := by
  apply sub_nonneg.mp
  rw [← smul_sub r B A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h)) hr)

end
end CurrentKS.Hermitian

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SquareShift
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
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}
lemma square_shift (X : H d) (a : ℝ) :
    sandwich (X-a • (Hermitian.one : H d)) Hermitian.one =
      sandwich X Hermitian.one-(2*a) • X+a^2 • (Hermitian.one : H d) := by
  apply Subtype.ext
  change ((X : Mat d)-a • 1)*1*((X : Mat d)-a • 1) =
    (X : Mat d)*1*(X : Mat d)-(2*a) • (X : Mat d)+a^2 • 1
  simp only [mul_one,sub_mul,mul_sub,mul_smul_comm,smul_mul_assoc,one_mul]
  module

lemma square_lower (X : H d) {a : ℝ} (ha : 0 ≤ a)
    (hX : a • (Hermitian.one : H d) ≤ X) :
    a^2 • (Hermitian.one : H d) ≤ sandwich X Hermitian.one := by
  have hsq := (mem_psd_iff_nonneg _).mp (sandwich_psd (X-a • (Hermitian.one : H d))
    (Hermitian.one : H d) one_mem_psdCone)
  rw [square_shift] at hsq
  have hlo := smul_order hX (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha)
  rw [smul_smul] at hlo
  have hh := add_le_add hsq hlo
  have he : sandwich X Hermitian.one-(2*a) • X+a^2 • (Hermitian.one : H d)+(2*a) • X =
      sandwich X Hermitian.one+a^2 • (Hermitian.one : H d) := by abel
  rw [zero_add,he] at hh
  have he' : (2*a*a) • (Hermitian.one : H d) =
      a^2 • (Hermitian.one : H d)+a^2 • (Hermitian.one : H d) := by module
  rw [he'] at hh
  exact (add_le_add_iff_right (a^2 • (Hermitian.one : H d))).mp hh
end
end CurrentKS.Hermitian

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

attribute [local instance] OAI.CurrentKS.Covariance.columnInnerProductSpace
lemma total_movement {Γ : Mat m} (hΓ : Γ.PosSemidef) :
    (∑ j, ‖column (CFC.sqrt Γ) j‖^2) = Γ.trace := by
  have h := sqrt_moments hΓ (1 : Mat m)
  simpa only [quad,Matrix.toLpLin_one,LinearMap.id_apply,real_inner_self_eq_norm_sq,one_mul] using h

end
end CurrentKS.Covariance

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_rf0e926_1 : NormedSpace ℝ (H d) := inferInstance
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

lemma interaction_diag (c : ℝ) (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (l : Fin N → ℝ) (X : H d) (i : Fin N) :
    interaction c A l X i i = c*(l i*inner ℝ (A i) X)^2 := by
  unfold interaction
  rw [inner_eq_trace]
  change c*l i*l i*((A i : Mat d)*((X : Mat d)*(A i : Mat d)*(X : Mat d))).trace.re = _
  rw [← mul_assoc,← mul_assoc,CurrentKS.rank_one_sandwich _ (hA i) (hrank i)]
  rw [Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,Complex.mul_re]
  have him : (((A i : Mat d)*(X : Mat d)).trace).im = 0 := by
    have he := trace_mul_real (A i) X
    exact congrArg Complex.im he |>.symm
  rw [him,mul_zero,sub_zero]
  rw [inner_eq_trace]
  ring

lemma interaction_quad (c : ℝ) (A : Fin N → H d) (l F : Fin N → ℝ) (X : H d) :
    F ⬝ᵥ (interaction c A l X *ᵥ F) =
      c*inner ℝ (responseInput A l F) (sandwich X (responseInput A l F)) := by
  simp only [dotProduct,interaction_mulVec]
  have he (Z : H d) : inner ℝ (responseInput A l F) Z =
      ∑ i, (l i*F i)*inner ℝ (A i) Z := by
    rw [responseInput,sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_smul_left (A i) Z (l i*F i)
  rw [he]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma interaction_psd {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) (l : Fin N → ℝ)
    (X : H d) (hX : X ∈ psdCone d) : (interaction c A l X).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨interaction_symm c A l X,fun F => ?_⟩
  simp only [star_trivial,interaction_quad]
  exact mul_nonneg hc (sandwich_inner_nonneg X _ hX)

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

lemma sum_pair (f : Fin (2*n) → ℝ) :
    (∑ i, f i) = (∑ i, f (pairIndex n (.inl i)))+(∑ i, f (pairIndex n (.inr i))) := by
  rw [← (pairIndex n).sum_comp f,Fintype.sum_sum_type]

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

lemma row_square_sum (C : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    (∑ j, C i j ^ 2) = (C*C.conjTranspose) i i := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,sq]

lemma sqrt_mul_transpose {Γ : Mat m} (hΓ : Γ.PosSemidef) :
    CFC.sqrt Γ*(CFC.sqrt Γ).conjTranspose = Γ := by
  rw [(CFC.sqrt_nonneg Γ).posSemidef.isHermitian.eq,CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg]

lemma rectangular_row_moments (R : Matrix (Fin n) (Fin m) ℝ) {Γ : Mat m}
    (hΓ : Γ.PosSemidef) (i : Fin n) :
    (∑ j, (R.toEuclideanLin (column (CFC.sqrt Γ) j) i)^2) = (R*Γ*R.conjTranspose) i i := by
  have he : R*(CFC.sqrt Γ)*(R*(CFC.sqrt Γ)).conjTranspose = R*Γ*R.conjTranspose := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = R*(CFC.sqrt Γ*(CFC.sqrt Γ).conjTranspose)*R.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [sqrt_mul_transpose hΓ]
  rw [← he,← row_square_sum]
  apply Finset.sum_congr rfl
  intro j _
  rfl

lemma response_row_bound (R : Matrix (Fin n) (Fin m) ℝ) {Γ : Mat m} {κ : ℝ}
    (hΓ : Γ.PosSemidef) (hbound : (κ • (1 : Mat m)-Γ).PosSemidef) (i : Fin n) :
    (∑ j, (R.toEuclideanLin (column (CFC.sqrt Γ) j) i)^2) ≤ κ*(∑ j, R i j^2) := by
  rw [rectangular_row_moments R hΓ,row_square_sum]
  have hh := (hbound.mul_mul_conjTranspose_same R).diag_nonneg (i := i)
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one] at hh
  change 0 ≤ κ*(R*R.conjTranspose) i i-(R*Γ*R.conjTranspose) i i at hh
  exact sub_nonneg.mp hh

end

open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

end CurrentKS.Covariance

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_DiagBlock
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

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

end CurrentKS.Interaction

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_MovementMat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Movement
noncomputable section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

lemma eigenvalue_le_weighted (A : Mat n) (hA : ∀ i j, 0 ≤ A i j)
    (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) (q : ℝ)
    (hq : ∀ i, (A *ᵥ z) i ≤ q*z i)
    (v : Fin n → ℝ) (hv : v ≠ 0) (μ : ℝ) (hμ : A *ᵥ v = μ • v) : μ ≤ q := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    contrapose! hv
    ext i
    exact hv i
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j,Finset.mem_univ j⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|/z i) hn
  have hm : ∀ k, |v k| ≤ (|v i|/z i)*z k := by
    intro k
    exact (div_le_iff₀ (hz k)).mp (hi k (Finset.mem_univ k))
  have hvi : 0 < |v i| := by
    have ht := hi j (Finset.mem_univ j)
    have hp : 0 < |v j|/z j := div_pos (abs_pos.mpr hj) (hz j)
    exact (div_pos_iff.mp (hp.trans_le ht)).resolve_right (by intro h; linarith [hz i]) |>.1
  have hs : |(A *ᵥ v) i| ≤ (|v i|/z i)*(A *ᵥ z) i := by
    calc
      |(A *ᵥ v) i| ≤ ∑ k, |A i k*v k| := by
        simpa only [Matrix.mulVec,dotProduct] using Finset.abs_sum_le_sum_abs (fun k => A i k*v k) Finset.univ
      _ = ∑ k, A i k*|v k| := by simp only [abs_mul,abs_of_nonneg (hA i _)]
      _ ≤ ∑ k, A i k*((|v i|/z i)*z k) := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hm k) (hA i k)
      _ = (|v i|/z i)*(A *ᵥ z) i := by
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have he := congrFun hμ i
  simp only [Pi.smul_apply,smul_eq_mul] at he
  rw [he,abs_mul] at hs
  have hfinal := hs.trans (mul_le_mul_of_nonneg_left (hq i) (div_nonneg (abs_nonneg _) (hz i).le))
  have hcancel : (|v i|/z i)*(q*z i) = q*|v i| := by field_simp [(hz i).ne']
  rw [hcancel] at hfinal
  nlinarith [le_abs_self μ]

lemma product_weighted_bound (A B : Mat n) (hA : ∀ i j, 0 ≤ A i j)
    (z w : Fin n → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (ha : ∀ i, (A *ᵥ w) i ≤ q*z i) (hb : ∀ i, (B *ᵥ z) i ≤ q*w i) (i : Fin n) :
    ((A*B) *ᵥ z) i ≤ q^2*z i := by
  rw [← Matrix.mulVec_mulVec]
  calc
    (A *ᵥ (B *ᵥ z)) i ≤ (A *ᵥ (q • w)) i := by
      change (∑ j, A i j*(B *ᵥ z) j) ≤ ∑ j, A i j*(q*w j)
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hb j) (hA i j)
    _ = q*(A *ᵥ w) i := by simp only [Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
    _ ≤ q*(q*z i) := mul_le_mul_of_nonneg_left (ha i) hq
    _ = q^2*z i := by ring

lemma sqrt_product_posSemidef (A B : Mat n) (hB : B.PosSemidef) :
    (CFC.sqrt A*B*CFC.sqrt A).PosSemidef := by
  have hh := hB.conjTranspose_mul_mul_same (CFC.sqrt A)
  simpa only [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq] using hh

lemma sqrt_product_eigen_bound (A B : Mat n) (hA : A.PosSemidef)
    (hAB : ∀ i j, 0 ≤ (A*B) i j)
    (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) (q : ℝ) (hq : 0 ≤ q)
    (hbound : ∀ i, ((A*B) *ᵥ z) i ≤ q*z i)
    (v : Fin n → ℝ) (hv : v ≠ 0) (μ : ℝ)
    (he : (CFC.sqrt A*B*CFC.sqrt A) *ᵥ v = μ • v) : μ ≤ q := by
  by_cases hm : μ ≤ 0
  · exact hm.trans hq
  have hm' : μ ≠ 0 := ne_of_gt (lt_of_not_ge hm)
  let u := CFC.sqrt A *ᵥ v
  have hu : u ≠ 0 := by
    intro hu
    have hz' : (CFC.sqrt A*B*CFC.sqrt A) *ᵥ v = 0 := by
      rw [← Matrix.mulVec_mulVec,show CFC.sqrt A *ᵥ v = 0 from hu]
      simp
    rw [he] at hz'
    exact hv ((smul_eq_zero.mp hz').resolve_left hm')
  have hue : (A*B) *ᵥ u = μ • u := by
    have hh := congrArg (fun w => CFC.sqrt A *ᵥ w) he
    try dsimp only at hh
    rw [Matrix.mulVec_smul] at hh
    dsimp [u]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Matrix.mulVec_mulVec,mul_assoc]
    rw [← mul_assoc (CFC.sqrt A),CFC.sqrt_mul_sqrt_self A hA.nonneg]
  exact eigenvalue_le_weighted (A*B) hAB z hz q hbound u hu μ hue

lemma sqrt_product_norm_bound (A B : Mat n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : ∀ i j, 0 ≤ (A*B) i j)
    (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) (q : ℝ) (hq : 0 ≤ q)
    (hbound : ∀ i, ((A*B) *ᵥ z) i ≤ q*z i) :
    ‖CFC.sqrt A*B*CFC.sqrt A‖ ≤ q := by
  let C := CFC.sqrt A*B*CFC.sqrt A
  have hc : C.PosSemidef := sqrt_product_posSemidef A B hB
  have heig : ∀ i, ‖hc.isHermitian.eigenvalues i‖ ≤ q := by
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hc.eigenvalues_nonneg i)]
    apply sqrt_product_eigen_bound A B hA hAB z hz q hq hbound
      (hc.isHermitian.eigenvectorBasis i) ?_ _ (hc.isHermitian.mulVec_eigenvectorBasis i)
    exact (ofLp_eq_zero 2).ne.2 (hc.isHermitian.eigenvectorBasis.orthonormal.ne_zero i)
  have hdiag : ‖(Matrix.diagonal (hc.isHermitian.eigenvalues) : Mat n)‖ ≤ q := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hq).mpr heig
  calc
    ‖C‖ = ‖(Matrix.diagonal (hc.isHermitian.eigenvalues) : Mat n)‖ := by
      conv_lhs => rw [hc.isHermitian.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply]
      rw [mul_assoc,CStarRing.norm_coe_unitary_mul,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary]
      rfl
    _ ≤ q := hdiag

end
end CurrentKS.Movement

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Norm
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Movement

section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

lemma norm_one_le : ‖(1 : Mat n)‖ ≤ 1 := by
  have he : (1 : Mat n) = Matrix.diagonal (fun _ => (1 : ℝ)) := by ext i j; simp [Matrix.one_apply]
  rw [he,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr (by intro i; simp)

lemma inverse_geometric_bound (C : Mat n) {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (hC : ‖C‖ ≤ (1-s)^2) : ‖(1-C)⁻¹‖ ≤ s⁻¹ := by
  have hgap : s ≤ 1-‖C‖ := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs₁)]
  have hlt : ‖C‖ < 1 := by linarith
  rw [Matrix.inv_eq_left_inv (geom_series_mul_neg C hlt)]
  have hh := tsum_geometric_le_of_norm_lt_one C hlt
  have hi : (1-‖C‖)⁻¹ ≤ s⁻¹ := inv_anti₀ hs hgap
  have hone := norm_one_le (n := n)
  linarith

lemma inverse_woodbury_sqrt (A B : Mat n) (hA : A.PosSemidef)
    (hC : ‖CFC.sqrt A*B*CFC.sqrt A‖ < 1) :
    (1-A*B)⁻¹ = 1+CFC.sqrt A*(1-CFC.sqrt A*B*CFC.sqrt A)⁻¹*CFC.sqrt A*B := by
  let R := CFC.sqrt A
  let C := R*B*R
  let D := (1-C)⁻¹
  have hD : D*(1-C) = 1 := by
    unfold D
    rw [Matrix.inv_eq_left_inv (geom_series_mul_neg C hC)]
    exact geom_series_mul_neg C hC
  apply Matrix.inv_eq_left_inv
  change (1+R*D*R*B)*(1-A*B) = 1
  have he : R*R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  calc
    _ = 1-A*B+R*(D*(1-C))*R*B := by
      dsimp only [C]
      rw [← he]
      noncomm_ring
    _ = 1 := by rw [hD,mul_one,he]; abel

lemma inverse_product_bound (A B : Mat n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : ∀ i j, 0 ≤ (A*B) i j) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    {s M : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (hM : 0 ≤ M)
    (hbound : ∀ i, ((A*B) *ᵥ z) i ≤ (1-s)^2*z i)
    (ha : ‖A‖ ≤ M) (hb : ‖B‖ ≤ M) : ‖(1-A*B)⁻¹‖ ≤ 1+M^2/s := by
  let R := CFC.sqrt A
  let C := R*B*R
  have hc : ‖C‖ ≤ (1-s)^2 := sqrt_product_norm_bound A B hA hB hAB z hz ((1-s)^2) (sq_nonneg _) hbound
  have hlt : ‖C‖ < 1 := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs₁)]
  have hd : ‖(1-C)⁻¹‖ ≤ s⁻¹ := inverse_geometric_bound C hs hs₁ hc
  have hr : ‖R‖^2 = ‖A‖ := by
    rw [← (CFC.sqrt_nonneg A).posSemidef.isHermitian.isSelfAdjoint.norm_mul_self]
    exact congrArg norm (CFC.sqrt_mul_sqrt_self A hA.nonneg)
  rw [inverse_woodbury_sqrt A B hA hlt]
  calc
    ‖1+R*(1-C)⁻¹*R*B‖ ≤ ‖(1 : Mat n)‖+‖R*(1-C)⁻¹*R*B‖ := norm_add_le _ _
    _ ≤ 1+‖R‖*‖(1-C)⁻¹‖*‖R‖*‖B‖ := by
      gcongr
      · exact norm_one_le
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg R))) (norm_nonneg B))
    _ = 1+‖A‖*‖(1-C)⁻¹‖*‖B‖ := by rw [← hr]; ring
    _ ≤ 1+M*s⁻¹*M := by gcongr
    _ = 1+M^2/s := by ring

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma response_norm_bound (A B R : E →L[ℝ] E) {J M : ℝ}
    (hJ : 0 ≤ J) (hM : 0 ≤ M) (hR : ‖R‖ ≤ J) (hB : ‖B‖ ≤ M)
    (hleft : R.comp (ContinuousLinearMap.id ℝ E-B.comp A) = ContinuousLinearMap.id ℝ E)
    (F G H : E) (hF : F-B G = H) (hG : G-A F = -H) :
    ‖F‖ ≤ J*(1+M)*‖H‖ := by
  have hsolve : F = R (H-B H) := by
    have hf : F-B (A F) = H-B H := by
      have hg : G = A F-H := by rw [eq_sub_iff_add_eq]; calc
        _ = G-(G-A F) := by rw [hG]; simp
        _ = A F := by abel
      rw [hg,map_sub] at hF
      calc
        _ = (F-(B (A F)-B H))-B H := by abel
        _ = H-B H := by rw [hF]
    have hh := congrArg (fun L : E →L[ℝ] E => L F) hleft
    change R (F-B (A F)) = F at hh
    exact hh.symm.trans (congrArg R hf)
  rw [hsolve]
  calc
    ‖R (H-B H)‖ ≤ ‖R‖*‖H-B H‖ := R.le_opNorm _
    _ ≤ J*(‖H‖+‖B H‖) := mul_le_mul hR (norm_sub_le H (B H)) (norm_nonneg _) hJ
    _ ≤ J*(‖H‖+M*‖H‖) := by
      refine mul_le_mul_of_nonneg le_rfl ?_ hJ ?_
      · exact add_le_add le_rfl
          ((B.le_opNorm H).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg H)))
      · exact add_nonneg (norm_nonneg H) (mul_nonneg hM (norm_nonneg H))
    _ = J*(1+M)*‖H‖ := by ring

lemma coupled_response_energy_bound (A B R S : E →L[ℝ] E) {J M : ℝ}
    (hJ : 0 ≤ J) (hM : 0 ≤ M) (hR : ‖R‖ ≤ J) (hS : ‖S‖ ≤ J)
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M)
    (hleftR : R.comp (ContinuousLinearMap.id ℝ E-B.comp A) = ContinuousLinearMap.id ℝ E)
    (hleftS : S.comp (ContinuousLinearMap.id ℝ E-A.comp B) = ContinuousLinearMap.id ℝ E)
    (F G H : E) (hF : F-B G = H) (hG : G-A F = -H) :
    ‖F‖^2+‖G‖^2 ≤ (2*J^2*(1+M)^2)*‖H‖^2 := by
  have hf := response_norm_bound A B R hJ hM hR hB hleftR F G H hF hG
  have hg := response_norm_bound B A S hJ hM hS hA hleftS G F (-H) hG (by simpa using hF)
  rw [norm_neg] at hg
  have hp : 0 ≤ J*(1+M)*‖H‖ := by positivity
  have hfs := sq_le_sq₀ (norm_nonneg F) hp |>.mpr hf
  have hgs := sq_le_sq₀ (norm_nonneg G) hp |>.mpr hg
  nlinarith

end CurrentKS.Movement

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_InverseProductLeft
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Movement

section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

lemma inverse_product_left (A B : Mat n) (hA : A.PosSemidef)
    (hC : ‖CFC.sqrt A*B*CFC.sqrt A‖ < 1) : (1-A*B)⁻¹*(1-A*B) = 1 := by
  let R := CFC.sqrt A
  let C := R*B*R
  have hD : (1-C)⁻¹*(1-C) = 1 := by
    rw [Matrix.inv_eq_left_inv (geom_series_mul_neg C hC)]
    exact geom_series_mul_neg C hC
  have he : R*R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  rw [inverse_woodbury_sqrt A B hA hC]
  change (1+R*(1-C)⁻¹*R*B)*(1-A*B) = 1
  calc
    _ = 1-A*B+R*((1-C)⁻¹*(1-C))*R*B := by
      dsimp only [C]
      rw [← he]
      noncomm_ring
    _ = 1 := by rw [hD,mul_one,he]; abel

lemma matrix_coupled_response_bound (A B : Mat n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAnon : ∀ i j, 0 ≤ A i j) (hBnon : ∀ i j, 0 ≤ B i j)
    (z w : Fin n → ℝ) (hz : ∀ i, 0 < z i) (hw : ∀ i, 0 < w i)
    {s M : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (hM : 0 ≤ M)
    (hAw : ∀ i, (A *ᵥ w) i ≤ (1-s)*z i) (hBz : ∀ i, (B *ᵥ z) i ≤ (1-s)*w i)
    (ha : ‖A‖ ≤ M) (hb : ‖B‖ ≤ M)
    (F G H : EuclideanSpace ℝ (Fin n))
    (hF : F-B.toEuclideanLin G = H) (hG : G-A.toEuclideanLin F = -H) :
    ‖F‖^2+‖G‖^2 ≤ (2*(1+M^2/s)^2*(1+M)^2)*‖H‖^2 := by
  have hnAB : ∀ i j, 0 ≤ (A*B) i j := by
    intro i j
    change 0 ≤ ∑ k, A i k*B k j
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hAnon i k) (hBnon k j)
  have hnBA : ∀ i j, 0 ≤ (B*A) i j := by
    intro i j
    change 0 ≤ ∑ k, B i k*A k j
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hBnon i k) (hAnon k j)
  have hprod := product_weighted_bound A B hAnon z w (1-s) (sub_nonneg.mpr hs₁) hAw hBz
  have hprod' := product_weighted_bound B A hBnon w z (1-s) (sub_nonneg.mpr hs₁) hBz hAw
  have hinv := inverse_product_bound A B hA hB hnAB z hz hs hs₁ hM hprod ha hb
  have hinv' := inverse_product_bound B A hB hA hnBA w hw hs hs₁ hM hprod' hb ha
  have hlt : (1-s)^2 < 1 := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs₁)]
  have hleft := inverse_product_left A B hA ((sqrt_product_norm_bound A B hA hB hnAB z hz _
    (sq_nonneg _) hprod).trans_lt hlt)
  have hleft' := inverse_product_left B A hB ((sqrt_product_norm_bound B A hB hA hnBA w hw _
    (sq_nonneg _) hprod').trans_lt hlt)
  apply coupled_response_energy_bound (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A) (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) ((1-B*A)⁻¹)) (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) ((1-A*B)⁻¹))
    (by positivity) hM _ _ ha hb _ _ F G H hF hG
  · exact hinv'
  · exact hinv
  · have hh := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ)) hleft'
    simp only [map_mul,map_sub,map_one,ContinuousLinearMap.mul_def] at hh
    exact hh
  · have hh := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ)) hleft
    simp only [map_mul,map_sub,map_one,ContinuousLinearMap.mul_def] at hh
    exact hh

end

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}
lemma psd_norm_le_trace (A : Mat n) (hA : A.PosSemidef) : ‖A‖ ≤ A.trace := by
  have ht : 0 ≤ A.trace := Finset.sum_nonneg fun i _ => hA.diag_nonneg
  have heig : ∀ i, ‖hA.isHermitian.eigenvalues i‖ ≤ A.trace := by
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hA.eigenvalues_nonneg i),hA.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  calc
    ‖A‖ = ‖(Matrix.diagonal (hA.isHermitian.eigenvalues) : Mat n)‖ := by
      conv_lhs => rw [hA.isHermitian.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply]
      rw [mul_assoc,CStarRing.norm_coe_unitary_mul,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary]
      rfl
    _ ≤ A.trace := by rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg ht).mpr heig
end CurrentKS.Movement

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_LightPoint
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma inner_smul_right_fixed (A B : H d) (r : ℝ) :
    inner ℝ A (r • B) = r*inner ℝ A B := real_inner_smul_right A B r

namespace LightPoint
variable (p : LightPoint d N)

lemma X_pos : p.X ∈ pd d := p.feasible.1.1
lemma Y_pos : p.Y ∈ pd d := p.feasible.1.2
lemma a_pos [NeZero d] (i : Fin N) : 0 < p.a i :=
  coordinate_pos (p.A i) p.X (p.A_pos i) (p.A_ne_zero i) p.X_pos
lemma b_pos [NeZero d] (i : Fin N) : 0 < p.b i :=
  coordinate_pos (p.A i) p.Y (p.A_pos i) (p.A_ne_zero i) p.Y_pos
lemma pp_pos [NeZero d] (i : Fin N) : 0 < p.pp i :=
  coordinate_pos (p.A i) p.P (p.A_pos i) (p.A_ne_zero i) p.P_pos
lemma qq_pos [NeZero d] (i : Fin N) : 0 < p.qq i :=
  coordinate_pos (p.A i) p.Q (p.A_pos i) (p.A_ne_zero i) p.Q_pos
lemma scales_pos [NeZero d] (i : Fin N) : 0 < p.T i ∧ 0 < p.l i ∧ 0 < p.m i :=
  (light_rescaling_pos (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)).2.2
lemma lm_eq [NeZero d] (i : Fin N) : p.l i*p.m i = psi (p.x i) :=
  scaleL_mul_scaleM (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)
lemma square_bounds [NeZero d] (i : Fin N) :
    (p.l i*p.a i)^2 ≤ 3*(384 : ℝ)⁻¹^2 ∧ (p.m i*p.b i)^2 ≤ 3*(384 : ℝ)⁻¹^2 :=
  rescaled_square_bounds (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)

end LightPoint
end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ResponseMatrix
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

variable {n : ℕ}

lemma pair_norm_sq (v : E (2*n)) : ‖v‖^2 = ‖fstVec v‖^2+‖sndVec v‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  rw [sum_pair]
  rfl

lemma responseMatrix_apply (B : Mat n) (v : E (2*n)) :
    (responseMatrix B).toEuclideanLin v = responseLin B v := by
  ext i
  change (∑ j, responseMatrix B i j*v j) = _
  rw [sum_pair]
  simp only [responseMatrix,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
  change (∑ j, (1 : Mat n) i j*fstVec v j)+(∑ j, -B i j*sndVec v j) = _
  simp only [neg_mul,Finset.sum_neg_distrib]
  change ((1 : Mat n) *ᵥ fstVec v) i-(B *ᵥ sndVec v) i = _
  rw [Matrix.one_mulVec]
  rfl

lemma response_row_squares (B : Mat n) (i : Fin n) :
    (∑ j, responseMatrix B i j^2) = 1+∑ j, B i j^2 := by
  rw [sum_pair]
  simp only [responseMatrix,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,neg_sq]
  have he : (∑ j, (1 : Mat n) i j^2) = 1 := by simp [Matrix.one_apply]
  rw [he]

lemma hermitian_row_norm_bound (B : Mat n) (hB : B.IsHermitian) (i : Fin n) :
    (∑ j, B i j^2) ≤ ‖B‖^2 := by
  let e : E n := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have hn := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B).le_opNorm e
  rw [Matrix.l2_opNorm_toEuclideanCLM,he,mul_one] at hn
  have hh : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B) e‖^2 = ∑ j, B i j^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    have hs : B j i = B i j := by simpa only [Matrix.conjTranspose_apply,star_trivial] using (congrFun (congrFun hB j) i).symm
    simp only [Matrix.ofLp_toEuclideanCLM,e,PiLp.single_apply,Matrix.mulVec, dotProduct]
    simp [hs,Real.norm_eq_abs,sq_abs]
  rw [← hh]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

lemma response_moment_upper (B : Mat n) (hB : B.IsHermitian) {Γ : Mat (2*n)}
    (hΓ : Γ.PosSemidef) (hbound : ((4 : ℝ) • (1 : Mat (2*n))-Γ).PosSemidef) (i : Fin n) :
    (∑ j, (responseLin B (column (CFC.sqrt Γ) j) i)^2) ≤ 4*(1+‖B‖^2) := by
  have hh := response_row_bound (responseMatrix B) hΓ hbound i
  simp only [responseMatrix_apply,response_row_squares] at hh
  exact hh.trans (by nlinarith [hermitian_row_norm_bound B hB i])

lemma constraints_responses (A B : Mat n) (v : E (2*n)) (hv : constraintLin A B v = 0) :
    fstVec v-B.toEuclideanLin (sndVec v) = responseLin B v ∧
    sndVec v-A.toEuclideanLin (fstVec v) = -responseLin B v := by
  refine ⟨rfl,?_⟩
  have hh : responseLin B v-(A.toEuclideanLin (fstVec v)-sndVec v) = 0 := hv
  rw [sub_eq_zero] at hh
  rw [hh]
  abel

end
end CurrentKS.Covariance

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StateIA
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction
open CurrentKS.Covariance CurrentKS.Movement Matrix WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d N : ℕ} (p : LightPoint d N)

lemma s0_pos : 0 < p.s0 := div_pos p.ε_pos (by norm_num)
lemma s0_le_one : p.s0 ≤ 1 := by dsimp [s0] <;> linarith [p.ε_le_one]
lemma C1_ge_one : (1 : ℝ) ≤ p.C1 := le_max_left ..
lemma C1_pos : 0 < p.C1 := lt_of_lt_of_le (by norm_num) p.C1_ge_one

lemma primal_lower [NeZero d] :
    (1/200 : ℝ) • (Hermitian.one : H d) ≤ p.X ∧
    (1/200 : ℝ) • (Hermitian.one : H d) ≤ p.Y := by
  have hh := sublevel_box (p.fixedPart+S p.A p.x) (eta 384 p.A p.x)
    (eta_positive (by norm_num) p.A (fun i => (p.interior i).le)) p.ε_pos (by norm_num : (0 : ℝ) < 100)
    p.lower p.upper p.feasible p.sublevel
  norm_num only [show (2 : ℝ)*100 = 200 by norm_num,show (200 : ℝ)⁻¹ = 1/200 by norm_num] at hh
  exact ⟨hh.2.1.1,hh.2.2.1⟩

lemma primal_square_lower [NeZero d] :
    (1/40000 : ℝ) • (Hermitian.one : H d) ≤ sandwich p.X one ∧
    (1/40000 : ℝ) • (Hermitian.one : H d) ≤ sandwich p.Y one := by
  have hX := square_lower p.X (by norm_num : (0 : ℝ) ≤ 1/200) p.primal_lower.1
  have hY := square_lower p.Y (by norm_num : (0 : ℝ) ≤ 1/200) p.primal_lower.2
  norm_num only [div_pow,one_pow] at hX hY
  exact ⟨hX,hY⟩

open scoped Matrix.Norms.Frobenius in

lemma interaction_row_gap [NeZero d] :
    (∀ i, (p.IA *ᵥ p.wQ) i ≤ (1-p.s0)*p.wP i) ∧
    (∀ i, (p.IB *ᵥ p.wP) i ≤ (1-p.s0)*p.wQ i) := by
  constructor
  · intro i
    have h₁ := inner_mono_right_psd (p.A i) (p.A_pos i) p.primal_square_lower.1
    rw [inner_smul_right_fixed] at h₁
    have h₂ := inner_mono_right_psd (p.A i) (p.A_pos i) p.P_le
    have h₃ : (1/40000 : ℝ)*p.pp i ≤ inner ℝ (p.A i) (sandwich p.X one) := by
      dsimp only [pp] <;> nlinarith
    change (interaction 384 p.A p.l p.X *ᵥ fun j => p.m j*inner ℝ (p.A j) p.Q) i ≤
      (1-p.s0)*(p.l i*inner ℝ (p.A i) p.P)
    rw [interaction_duality 384 p.ε p.A p.x p.A_pos p.A_rank p.l p.m p.lm_eq
      p.X p.P p.Q p.X_pos p.stationary_X i]
    have hh := mul_le_mul_of_nonneg_left h₃ (mul_nonneg p.ε_pos.le (p.scales_pos i).2.1.le)
    dsimp only [s0,pp] at *
    nlinarith
  · intro i
    have h₁ := inner_mono_right_psd (p.A i) (p.A_pos i) p.primal_square_lower.2
    rw [inner_smul_right_fixed] at h₁
    have h₂ := inner_mono_right_psd (p.A i) (p.A_pos i) p.Q_le
    have h₃ : (1/40000 : ℝ)*p.qq i ≤ inner ℝ (p.A i) (sandwich p.Y one) := by
      dsimp only [qq] <;> nlinarith
    change (interaction 384 p.A p.m p.Y *ᵥ fun j => p.l j*inner ℝ (p.A j) p.P) i ≤
      (1-p.s0)*(p.m i*inner ℝ (p.A i) p.Q)
    rw [interaction_duality 384 p.ε p.A p.x p.A_pos p.A_rank p.m p.l
      (fun i => (mul_comm _ _).trans (p.lm_eq i)) p.Y p.Q p.P p.Y_pos p.stationary_Y i]
    have hh := mul_le_mul_of_nonneg_left h₃ (mul_nonneg p.ε_pos.le (p.scales_pos i).2.2.le)
    dsimp only [s0,qq] at *
    nlinarith

lemma IA_psd : p.IA.PosSemidef := interaction_psd (by norm_num) p.A p.l p.X p.X_pos.posSemidef
lemma IB_psd : p.IB.PosSemidef := interaction_psd (by norm_num) p.A p.m p.Y p.Y_pos.posSemidef
lemma IA_norm_le [NeZero d] : ‖p.IA‖ ≤ 3*(N : ℝ) := by
  apply (psd_norm_le_trace p.IA p.IA_psd).trans
  calc
    p.IA.trace ≤ ∑ _ : Fin N, (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp only [IA,Matrix.diag]
      rw [interaction_diag 384 p.A p.A_pos p.A_rank p.l p.X i]
      have hh := p.square_bounds i
      dsimp only [a] at hh
      norm_num at hh
      linarith
    _ = _ := by simp <;> ring
lemma IB_norm_le [NeZero d] : ‖p.IB‖ ≤ 3*(N : ℝ) := by
  apply (psd_norm_le_trace p.IB p.IB_psd).trans
  calc
    p.IB.trace ≤ ∑ _ : Fin N, (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp only [IB,Matrix.diag]
      rw [interaction_diag 384 p.A p.A_pos p.A_rank p.m p.Y i]
      have hh := p.square_bounds i
      dsimp only [b] at hh
      norm_num at hh
      linarith
    _ = _ := by simp <;> ring

lemma coupled_movement [NeZero d] (v : Covariance.E (2*N)) (hv : constraintLin p.IA p.IB v = 0) :
    ‖v‖^2 ≤ p.E0*‖responseLin p.IB v‖^2 := by
  rw [pair_norm_sq]
  obtain ⟨hf,hg⟩ := constraints_responses p.IA p.IB v hv
  exact matrix_coupled_response_bound p.IA p.IB p.IA_psd p.IB_psd
    (interaction_nonneg (by norm_num) p.A p.A_pos p.l (fun i => (p.scales_pos i).2.1.le) p.X)
    (interaction_nonneg (by norm_num) p.A p.A_pos p.m (fun i => (p.scales_pos i).2.2.le) p.Y)
    p.wP p.wQ (fun i => mul_pos (p.scales_pos i).2.1 (p.pp_pos i))
    (fun i => mul_pos (p.scales_pos i).2.2 (p.qq_pos i)) p.s0_pos p.s0_le_one (by positivity)
    p.interaction_row_gap.1 p.interaction_row_gap.2 p.IA_norm_le p.IB_norm_le _ _ _ hf hg

lemma covariance_movement_bounds_oai [NeZero d] {Γ : Covariance.Mat (2*N)}
    (hΓ : Γ.PosSemidef) (hbound : ((4 : ℝ) • (1 : Covariance.Mat (2*N))-Γ).PosSemidef)
    (htr : (23/48 : ℝ)*N ≤ Γ.trace)
    (hc : ∀ j, constraintLin p.IA p.IB (column (CFC.sqrt Γ) j) = 0) :
    (N : ℝ)/p.C1 ≤ (∑ i, ∑ j, (responseLin p.IB (column (CFC.sqrt Γ) j) i)^2) ∧
    ∀ i, (∑ j, (responseLin p.IB (column (CFC.sqrt Γ) j) i)^2) ≤ p.C1 := by
  have hE : p.E0*(∑ i, ∑ j, (responseLin p.IB (column (CFC.sqrt Γ) j) i)^2) ≥ (23/48 : ℝ)*N := by
    calc
      _ = ∑ j, p.E0*‖responseLin p.IB (column (CFC.sqrt Γ) j)‖^2 := by
        simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≥ ∑ j, ‖column (CFC.sqrt Γ) j‖^2 := Finset.sum_le_sum fun j _ => p.coupled_movement _ (hc j)
      _ = Γ.trace := total_movement hΓ
      _ ≥ _ := htr
  refine ⟨?_,fun i => ?_⟩
  · have hC : 48*p.E0/23 ≤ p.C1 := (le_max_left _ _).trans (le_max_right _ _)
    have hn : 0 ≤ ∑ i, ∑ j, (responseLin p.IB (column (CFC.sqrt Γ) j) i)^2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    apply (div_le_iff₀ p.C1_pos).mpr
    have hh := mul_le_mul_of_nonneg_right hC hn
    nlinarith
  · have hh := response_moment_upper p.IB p.IB_psd.isHermitian hΓ hbound i
    have hn := p.IB_norm_le
    have hC : 4*(1+9*(N : ℝ)^2) ≤ p.C1 := (le_max_right _ _).trans (le_max_right _ _)
    have hsq := pow_le_pow_left₀ (norm_nonneg p.IB) hn 2
    nlinarith

end
end CurrentKS.State.LightPoint

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.State.LightPoint.covariance_movement_bounds_oai := @OAI.CurrentKS.State.LightPoint.covariance_movement_bounds_oai
