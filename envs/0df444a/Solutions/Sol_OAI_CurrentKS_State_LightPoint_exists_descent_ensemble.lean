-- Prove2me | solution 1 for OAI.CurrentKS.State.LightPoint.exists_descent_ensemble
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:51:30.47953+00:00
-- url     : https://prove2.me/submissions/c8db0fd1-3e42-42b6-aa2a-c40f4f1e19cc

import Mathlib
import Definitions.Def_OAIQ241TT002
import Theorems.Thm_OAI_CurrentKS_Interaction_state_energy_ensemble
import Theorems.Thm_OAI_CurrentKS_State_LightPoint_Psi_driftCurvature
import Theorems.Thm_OAI_CurrentKS_State_LightPoint_covariance_movement_bounds
import Theorems.Thm_OAI_CurrentKS_State_face_value_direction_variations

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

lemma psi_le_one {x : ℝ} (hx : |x| < 1) : psi x ≤ 1 := by
  have hp := psi_pos hx
  have hc := psi_cube hx
  nlinarith [sq_nonneg x, sq_nonneg (psi x - 1)]

lemma hasDerivAt_psi {x : ℝ} (hx : |x| < 1) : HasDerivAt psi (psi₁ x) x := by
  have hr := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).rpow_const
    (p := (1/3 : ℝ)) (Or.inl (ne_of_gt (base_pos hx)))
  convert hr using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  norm_num only [mul_one, zero_sub, Nat.cast_ofNat]
  simp only [id_eq, pow_one, Pi.sub_apply, Pi.pow_apply]
  rw [Real.rpow_neg (base_pos hx).le, ← psi_sq hx]
  unfold psi₁
  ring

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

lemma psi₁_eq_base {x : ℝ} (hx : |x| < 1) :
    psi₁ x = -(2*x/(3*(1-x^2))) * psi x := by
  have hw := ne_of_gt (psi_pos hx)
  have hb := ne_of_gt (base_pos hx)
  unfold psi₁
  field_simp
  have hc := psi_cube hx
  rw [hc]

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

lemma psi_ge_base {x : ℝ} (hx : |x| < 1) : 1-x^2 ≤ psi x := by
  have hp := psi_pos hx
  have hle := psi_le_one hx
  have hc := psi_cube hx
  have hs : psi x ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hs)]

lemma abs_derivative_ratio {x : ℝ} (hx : |x| < 1) :
    |psi₁ x| / (psi x * kappa x) = 3 * |x| * psi x^2/(3+x^2) := by
  have hw := psi_pos hx
  have hw0 := ne_of_gt hw
  have hx3 : 3+x^2 ≠ 0 := by positivity
  rw [psi₁,abs_div,abs_mul]
  simp only [abs_mul,abs_of_nonneg (sq_nonneg (psi x))]
  norm_num only [abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  unfold kappa
  field_simp
  ring

lemma abs_derivative_ratio_le {x : ℝ} (hx : |x| < 1) :
    |psi₁ x| / (psi x * kappa x) ≤ 1 := by
  rw [abs_derivative_ratio hx]
  apply (div_le_one (by positivity : 0 < 3+x^2)).mpr
  have hp := psi_pos hx
  have hle := psi_le_one hx
  have hs : psi x^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul hs hx.le (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [sq_nonneg x]

lemma weighted_kappa_lower {x : ℝ} (hx : |x| < 1) :
    2/(3*(1-x^2)) ≤ psi x * kappa x := by
  have hp := psi_pos hx
  have h0 := ne_of_gt hp
  have hle := psi_le_one hx
  have hc := psi_cube hx
  rw [← hc]
  unfold kappa
  apply (div_le_iff₀ (by positivity : 0 < 3*psi x^3)).mpr
  field_simp
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (pow_nonneg hp.le 3)]

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

lemma kappa_product_bounds {x A B : ℝ} (hx : |x| < 1)
    (hA : 0 < A) (hB : 0 < B) (hAl : A < 1+x) (hBl : B < 1-x) :
    (1/3 : ℝ) ≤ kappa x / (alpha x A B * beta x A B) ∧
    (1/3 : ℝ) ≤ psi x * kappa x / (alpha x A B * beta x A B) ∧
    psi x / (alpha x A B * beta x A B) ≤ (3/2 : ℝ) := by
  obtain ⟨hl,hu,ha,hb⟩ := product_bounds hx hA hB hAl hBl
  have hp := psi_pos hx
  have hp1 := psi_le_one hx
  have hk := kappa_pos hx
  have hr := base_pos hx
  have hw := weighted_kappa_lower hx
  have hq : alpha x A B * beta x A B ≤ 3 * (psi x * kappa x) := by
    have he : 2/(1-x^2) = 3*(2/(3*(1-x^2))) := by field_simp
    rw [he] at hu
    linarith
  have hprod := mul_pos ha hb
  refine ⟨(le_div_iff₀ hprod).mpr ?_, (le_div_iff₀ hprod).mpr ?_,
    (div_le_iff₀ hprod).mpr ?_⟩
  · nlinarith [mul_le_of_le_one_left hk.le hp1]
  · nlinarith
  · nlinarith

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

lemma Alpha_eq {x : ℝ} (hx : |x| < 1) (c a b : ℝ) :
    Alpha c x a b = 1+c*psi₁ x*b := by
  rw [Alpha,alpha,psi₁_eq_base hx]
  ring

lemma Beta_eq {x : ℝ} (hx : |x| < 1) (c a b : ℝ) :
    Beta c x a b = 1-c*psi₁ x*a := by
  rw [Beta,beta,psi₁_eq_base hx]
  ring

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

lemma rescaled_product_bound {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    (scaleL c x a b*a)*(scaleM c x a b*b) ≤ c⁻¹^2 := by
  have hr := base_pos hx
  have hp := psi_pos hx
  have ha' := mul_pos (mul_pos hc hp) ha
  have hb' := mul_pos (mul_pos hc hp) hb
  have hp' : (c*psi x*a)*(c*psi x*b) ≤ (1+x)*(1-x) :=
    mul_le_mul hal.le hbl.le hb'.le (by linarith [abs_lt.mp hx])
  have hψ : 0 < psi x^2 := sq_pos_of_pos hp
  have hbound : c^2*(psi x*(a*b)) ≤ 1 := by
    have he : (c*psi x*a)*(c*psi x*b) = (c^2*(psi x*(a*b)))*psi x := by ring
    rw [he] at hp'
    have hg := psi_ge_base hx
    nlinarith
  have he : (scaleL c x a b*a)*(scaleM c x a b*b) = psi x*(a*b) := by
    rw [show (scaleL c x a b*a)*(scaleM c x a b*b) =
      (scaleL c x a b*scaleM c x a b)*(a*b) by ring,
      scaleL_mul_scaleM hc hx ha hb hal hbl]
  rw [he,inv_pow,inv_eq_one_div]
  exact (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith)

lemma rescaled_kappa_bounds {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    (1/3 : ℝ) ≤ kappa x/(Alpha c x a b*Beta c x a b) ∧
    (1/3 : ℝ) ≤ kappa x/scaleT c x a b^2 ∧
    (scaleT c x a b^2)⁻¹ ≤ (3/2 : ℝ) := by
  have hp := psi_pos hx
  obtain ⟨hA,hB,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  obtain ⟨h₁,h₂,h₃⟩ := kappa_product_bounds hx (mul_pos (mul_pos hc hp) ha)
    (mul_pos (mul_pos hc hp) hb) hal hbl
  change (1/3 : ℝ) ≤ kappa x/(Alpha c x a b*Beta c x a b) at h₁
  change (1/3 : ℝ) ≤ psi x*kappa x/(Alpha c x a b*Beta c x a b) at h₂
  change psi x/(Alpha c x a b*Beta c x a b) ≤ (3/2 : ℝ) at h₃
  refine ⟨h₁,?_,?_⟩
  · rw [scaleT_sq hc hx ha hb hal hbl]
    convert h₂ using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  · rw [scaleT_sq hc hx ha hb hal hbl,inv_div]
    exact h₃

lemma rescaled_sum_identity {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    scaleT c x a b*(scaleL c x a b*a+scaleM c x a b*b) = a+b := by
  have hT := (light_rescaling_pos hc hx ha hb hal hbl).2.2.1
  rw [scaleL,scaleM]
  field_simp
  rw [Alpha_eq hx,Beta_eq hx]
  ring

lemma rescaled_drift_bounds {c x a b : ℝ} (hc : 0 < c) (hx : |x| < 1)
    (ha : 0 < a) (hb : 0 < b) (hal : c*psi x*a < 1+x) (hbl : c*psi x*b < 1-x) :
    scaleT c x a b*(scaleL c x a b*a+scaleM c x a b*b) ≤ 2/(c*psi x) ∧
    (scaleL c x a b*a+scaleM c x a b*b)/scaleT c x a b ≤ 3/c := by
  have hp := psi_pos hx
  have hs : c*psi x*(a+b) ≤ 2 := by nlinarith
  obtain ⟨hA,hB,hT,_⟩ := light_rescaling_pos hc hx ha hb hal hbl
  have hlo := (product_bounds hx (mul_pos (mul_pos hc hp) ha)
    (mul_pos (mul_pos hc hp) hb) hal hbl).1
  change (2/3 : ℝ) ≤ Alpha c x a b*Beta c x a b at hlo
  refine ⟨?_,?_⟩
  · rw [rescaled_sum_identity hc hx ha hb hal hbl]
    exact (le_div_iff₀ (mul_pos hc hp)).mpr (by nlinarith)
  · have he : (scaleL c x a b*a+scaleM c x a b*b)/scaleT c x a b =
        psi x*(a+b)/(Alpha c x a b*Beta c x a b) := by
      have hh := rescaled_sum_identity hc hx ha hb hal hbl
      have hh' : scaleL c x a b*a+scaleM c x a b*b = (a+b)/scaleT c x a b :=
        (eq_div_iff hT.ne').mpr (by nlinarith)
      rw [hh',div_div,← pow_two,scaleT_sq hc hx ha hb hal hbl]
      field_simp
    rw [he]
    apply (div_le_div_iff₀ (mul_pos hA hB) hc).mpr
    nlinarith

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

lemma sandwich_inverse_left (X A : H d) (hX : X ∈ pd d) :
    sandwich X (sandwich (invH X) A) = A := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  apply Subtype.ext
  change (X : Mat d)*((X : Mat d)⁻¹*(A : Mat d)*(X : Mat d)⁻¹)*(X : Mat d) = (A : Mat d)
  simp only [← mul_assoc, Matrix.mul_nonsing_inv _ hx,one_mul]
  rw [mul_assoc,Matrix.nonsing_inv_mul _ hx,mul_one]

lemma sandwich_inverse_right (X A : H d) (hX : X ∈ pd d) :
    sandwich (invH X) (sandwich X A) = A := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  apply Subtype.ext
  change (X : Mat d)⁻¹*((X : Mat d)*(A : Mat d)*(X : Mat d))*(X : Mat d)⁻¹ = (A : Mat d)
  simp only [← mul_assoc, Matrix.nonsing_inv_mul _ hx,one_mul]
  rw [mul_assoc,Matrix.mul_nonsing_inv _ hx,mul_one]

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r3e40c7_1 : NormedSpace ℝ (H d) := inferInstance
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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r3e40c7_2 : NormedSpace ℝ (H d) := inferInstance
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

lemma eta_response (c : ℝ) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (l m G : Fin N → ℝ) (hlm : ∀ i, l i*m i = psi (x i)) (Y : H d) :
    eta c A x (sandwich Y (responseInput A m G)) =
      responseInput A l (interaction c A m Y *ᵥ G) := by
  rw [eta_rank_one c A x _ hA hrank]
  unfold responseInput
  apply Finset.sum_congr rfl
  intro i _
  rw [interaction_mulVec,← hlm i]
  congr 1
  change c*(l i*m i)*inner ℝ (A i) (sandwich Y (responseInput A m G)) = _
  ring

end
end CurrentKS.Interaction

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Drift
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Progress
noncomputable section
open scoped BigOperators

variable {n : ℕ}

lemma drift_cancel {T a b z w ω : ℝ} (hT : T ≠ 0) :
    T*(z-w)*drift T a b ω+24*(a*z+b*w)*ω = 24*(a*w+b*z)*ω := by
  unfold drift
  field_simp
  ring

lemma drift_abs {T a b ω : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b) (hω : 0 ≤ ω) :
    |drift T a b ω| ≤ 24/T*(a+b)*ω := by
  unfold drift
  rw [abs_mul,abs_mul,abs_div,abs_of_pos hT,abs_of_nonneg hω]
  norm_num only [abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  have hd : |a-b| ≤ a+b := by rw [abs_le]; constructor <;> linarith
  gcongr

lemma drift_size {T a b ω C : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b) (hω : 0 ≤ ω)
    (hs : (a+b)/T ≤ (3/384 : ℝ)) (hC : ω ≤ C) : |drift T a b ω| ≤ C := by
  have h := drift_abs hT ha hb hω
  have hm := mul_le_mul_of_nonneg_right hs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) hω)
  have hC0 : 0 ≤ C := hω.trans hC
  have he : 24/T*(a+b)*ω = (a+b)/T*(24*ω) := by ring
  rw [he] at h
  nlinarith

lemma drift_penalty_bound {T a b ω ψ ψ' k : ℝ}
    (hT : 0 < T) (ha : 0 ≤ a) (hb : 0 ≤ b) (hω : 0 ≤ ω)
    (hψ : 0 < ψ) (hk : 0 ≤ k) (hp : |ψ'| ≤ ψ*k)
    (hs : T*(a+b) ≤ 2/(384*ψ)) :
    ψ'*drift T a b ω-(1/2 : ℝ)*k*ω/T^2 ≤ -(3/8 : ℝ)*k*ω/T^2 := by
  have h := drift_abs hT ha hb hω
  have h1 : ψ'*drift T a b ω ≤ |ψ'| *(24/T*(a+b)*ω) := by
    calc
      _ ≤ |ψ'*drift T a b ω| := le_abs_self _
      _ = |ψ'| *|drift T a b ω| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have h2 : |ψ'| *(24/T*(a+b)*ω) ≤ (ψ*k)*(24/T*(a+b)*ω) := by
    gcongr
  have hs' : ψ*T*(a+b) ≤ (1/192 : ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 384*ψ)).mp hs
    nlinarith
  have h3 : (ψ*k)*(24/T*(a+b)*ω) ≤ (1/8 : ℝ)*k*ω/T^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
    have he : (ψ*k)*(24/T*(a+b)*ω)*T^2 = 24*(ψ*T*(a+b))*(k*ω) := by
      field_simp
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hs' (mul_nonneg hk hω)
    nlinarith
  calc
    _ ≤ (1/8 : ℝ)*k*ω/T^2-(1/2 : ℝ)*k*ω/T^2 := sub_le_sub_right (h1.trans (h2.trans h3)) _
    _ = _ := by ring

lemma weighted_drift_nonpositive (T a b z w ω : Fin n → ℝ)
    (hT : ∀ i, T i ≠ 0) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hz : ∀ i, 0 ≤ z i) (hw : ∀ i, 0 ≤ w i) (hω : ∀ i, 0 ≤ ω i)
    {H : ℝ} (hH : H ≤ 24*(∑ i,(a i*z i+b i*w i)*ω i)-32*(∑ i,(a i*w i+b i*z i)*ω i)) :
    (∑ i,T i*(z i-w i)*drift (T i) (a i) (b i) (ω i))+H ≤ 0 := by
  have he : (∑ i,T i*(z i-w i)*drift (T i) (a i) (b i) (ω i))+
      24*(∑ i,(a i*z i+b i*w i)*ω i) = 24*(∑ i,(a i*w i+b i*z i)*ω i) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simpa only [mul_assoc] using (drift_cancel (a := a i) (b := b i) (z := z i) (w := w i) (ω := ω i) (hT i))
  have hn : 0 ≤ ∑ i,(a i*w i+b i*z i)*ω i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (add_nonneg (mul_nonneg (ha i) (hw i))
      (mul_nonneg (hb i) (hz i))) (hω i)
  linarith

lemma penalty_drift_quantitative (T a b ω ψ ψ' k : Fin n → ℝ)
    (hT : ∀ i, 0 < T i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hω : ∀ i, 0 ≤ ω i) (hψ : ∀ i, 0 < ψ i) (hk : ∀ i, 0 ≤ k i)
    (hp : ∀ i, |ψ' i| ≤ ψ i*k i) (hs : ∀ i, T i*(a i+b i) ≤ 2/(384*ψ i))
    (hlower : ∀ i, (1/3 : ℝ) ≤ k i/T i^2) :
    (∑ i,(ψ' i*drift (T i) (a i) (b i) (ω i)-(1/2 : ℝ)*k i*ω i/T i^2)) ≤
      -(1/8 : ℝ)*(∑ i,ω i) := by
  calc
    _ ≤ ∑ i,-(3/8 : ℝ)*k i*ω i/T i^2 := Finset.sum_le_sum fun i _ =>
      drift_penalty_bound (hT i) (ha i) (hb i) (hω i) (hψ i) (hk i) (hp i) (hs i)
    _ ≤ ∑ i,-(1/8 : ℝ)*ω i := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_right (hlower i) (hω i)
      have he : -(3/8 : ℝ)*k i*ω i/T i^2 = -(3/8 : ℝ)*((k i/T i^2)*ω i) := by ring
      rw [he]
      nlinarith
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma combine_progress {lam n C R P : ℝ} (hlam : 0 ≤ lam) (hC : 0 < C)
    (hR : R ≤ 0) (hP : P ≤ -n/(8*C)) : R+lam*P ≤ -lam*n/(8*C) := by
  have hDenom : 0 < 8 * C := by positivity
  apply (le_div_iff₀ hDenom).mpr
  have hProgress := mul_le_mul_of_nonneg_left ((le_div_iff₀ hDenom).mp hP) hlam
  have hRemainder := mul_nonpos_of_nonpos_of_nonneg hR hDenom.le
  nlinarith

end
end CurrentKS.Progress

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
lemma lT_eq [NeZero d] (i : Fin N) : p.l i*p.T i = 1+384*psi₁ (p.x i)*p.b i := by
  change Alpha 384 (p.x i) (p.a i) (p.b i)/p.T i*p.T i = _
  rw [div_mul_cancel₀ _ (p.scales_pos i).1.ne',Alpha_eq (p.interior i)]
lemma mT_eq [NeZero d] (i : Fin N) : p.m i*p.T i = 1-384*psi₁ (p.x i)*p.a i := by
  change Beta 384 (p.x i) (p.a i) (p.b i)/p.T i*p.T i = _
  rw [div_mul_cancel₀ _ (p.scales_pos i).1.ne',Beta_eq (p.interior i)]
lemma product_bound [NeZero d] (i : Fin N) : (p.l i*p.a i)*(p.m i*p.b i) ≤ (384 : ℝ)⁻¹^2 :=
  rescaled_product_bound (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)
lemma drift_bounds [NeZero d] (i : Fin N) :
    p.T i*(p.l i*p.a i+p.m i*p.b i) ≤ 2/(384*psi (p.x i)) ∧
    (p.l i*p.a i+p.m i*p.b i)/p.T i ≤ (3/384 : ℝ) :=
  rescaled_drift_bounds (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)
lemma kappa_bounds [NeZero d] (i : Fin N) :
    (1/3 : ℝ) ≤ kappa (p.x i)/p.T i^2 ∧ (p.T i^2)⁻¹ ≤ (3/2 : ℝ) :=
  (rescaled_kappa_bounds (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)).2

end LightPoint
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

lemma eventually_line_interior (x h : Coordinates N) {a : ℝ}
    (hx : ∀ i, |line x h a i| < 1) : ∀ᶠ s in 𝓝 a, ∀ i, |line x h s i| < 1 := by
  apply Filter.eventually_all.mpr
  intro i
  exact ((hasDerivAt_line_coord x h a i).continuousAt.abs).eventually (eventually_lt_nhds (hx i))

lemma hasDerivAt_penalty_line (x h : Coordinates N) (a : ℝ) (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => penalty (line x h s)) (penalty₁ (line x h a) h) a := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (hasDerivAt_psi (hx i)).comp a (hasDerivAt_line_coord x h a i)

lemma hasDerivAt_penalty₁_line (x h : Coordinates N) (a : ℝ) (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => penalty₁ (line x h s) h) (penalty₂ (line x h a) h) a := by
  apply HasDerivAt.fun_sum
  intro i _
  convert ((hasDerivAt_psi₁ (hx i)).comp a (hasDerivAt_line_coord x h a i)).mul_const (h i) using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  ring

lemma penalty_line_first (x h : Coordinates N) (hx : ∀ i, |x i| < 1) :
    deriv (fun s => penalty (line x h s)) 0 = penalty₁ x h := by
  simpa only [line_zero] using (hasDerivAt_penalty_line x h 0 (by simpa only [line_zero] using hx)).deriv

lemma penalty_line_second (x h : Coordinates N) (hx : ∀ i, |x i| < 1) :
    deriv (deriv (fun s => penalty (line x h s))) 0 = penalty₂ x h := by
  have he : deriv (fun s => penalty (line x h s)) =ᶠ[𝓝 (0 : ℝ)] fun s => penalty₁ (line x h s) h := by
    filter_upwards [eventually_line_interior x h (a := 0) (by simpa only [line_zero] using hx)] with s hs
    exact (hasDerivAt_penalty_line x h s hs).deriv
  rw [he.deriv_eq]
  simpa only [line_zero] using (hasDerivAt_penalty₁_line x h 0 (by simpa only [line_zero] using hx)).deriv

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
attribute [local instance] OAI.CurrentKS.State.negativeWeightNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.State.negativeWeightNormedSpace
private local instance instTopologicalSpaceContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_r3e40c7_1 : TopologicalSpace (H d →L[ℝ] H d) :=
  (inferInstance : NormedAddCommGroup (H d →L[ℝ] H d)).toUniformSpace.toTopologicalSpace
lemma eta₁_apply (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (Y : H d) :
    eta₁ c A x h Y = ∑ i, (c*psi₁ (x i)*h i) • sandwich (A i) Y := by
  simp only [eta₁,_root_.sum_apply,_root_.smul_apply,sandwichCLM_apply]

end CurrentKS.State

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ResponseInputSub
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

lemma responseInput_sub (A : Fin N → H d) (l F G : Fin N → ℝ) :
    responseInput A l (F-G) = responseInput A l F-responseInput A l G := by
  unfold responseInput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (l i*(F i-G i)) • A i = (l i*F i) • A i-(l i*G i) • A i
  module

lemma responseInput_neg (A : Fin N → H d) (l F : Fin N → ℝ) :
    responseInput A l (-F) = -responseInput A l F := by
  unfold responseInput
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (l i*(-F i)) • A i = -((l i*F i) • A i)
  module

lemma first_rhs_rescaled (c : ℝ) (A : Fin N → H d) (x h Hh T l : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (Y : H d) (hl : ∀ i, l i*T i = 1+c*psi₁ (x i)*inner ℝ (A i) Y)
    (hHT : ∀ i, T i*h i = Hh i) :
    S A h+eta₁ c A x h Y = responseInput A l Hh := by
  rw [S,eta₁_apply,← Finset.sum_add_distrib,responseInput]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) Y (hA i) (hrank i),smul_smul,← add_smul]
  congr 1
  rw [← hHT i,← mul_assoc,hl i]
  ring

lemma second_rhs_rescaled (c : ℝ) (A : Fin N → H d) (x h Hh T m : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X : H d) (hm : ∀ i, m i*T i = 1-c*psi₁ (x i)*inner ℝ (A i) X)
    (hHT : ∀ i, T i*h i = Hh i) :
    -S A h+eta₁ c A x h X = -responseInput A m Hh := by
  rw [S,eta₁_apply,responseInput,← Finset.sum_neg_distrib,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) X (hA i) (hrank i),smul_smul]
  have he : -h i+c*psi₁ (x i)*h i*inner ℝ (A i) X = -(m i*Hh i) := by
    rw [← hHT i,← mul_assoc,hm i]
    ring
  calc
    _ = (-h i+c*psi₁ (x i)*h i*inner ℝ (A i) X) • A i := by module
    _ = (-(m i*Hh i)) • A i := congrArg (fun r : ℝ => r • A i) he
    _ = _ := by module

lemma identify_responses [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (A : Fin N → H d) (x h Hh T l m F G : Coordinates N) (hx : Cube x)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X Y P Q U V : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d) (hPpos : P ∈ pd d) (hQpos : Q ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q+ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P+ε • (Hermitian.one : H d))
    (hlm : ∀ i, l i*m i = psi (x i))
    (hl : ∀ i, l i*T i = 1+c*psi₁ (x i)*inner ℝ (A i) Y)
    (hm : ∀ i, m i*T i = 1-c*psi₁ (x i)*inner ℝ (A i) X)
    (hHT : ∀ i, T i*h i = Hh i)
    (hF : F-(interaction c A m Y *ᵥ G) = Hh)
    (hG : G-(interaction c A l X *ᵥ F) = -Hh)
    (hU : sandwich (invH X) U-eta c A x V = S A h+eta₁ c A x h Y)
    (hV : sandwich (invH Y) V-eta c A x U = -S A h+eta₁ c A x h X) :
    U = sandwich X (responseInput A l F) ∧ V = sandwich Y (responseInput A m G) := by
  have hPX : P = sandwich X (eta c A x Q)+ε • sandwich X (Hermitian.one : H d) := by
    rw [← sandwich_smul,← sandwich_add,← hP,sandwich_inverse_left X P hX]
  have hQY : Q = sandwich Y (eta c A x P)+ε • sandwich Y (Hermitian.one : H d) := by
    rw [← sandwich_smul,← sandwich_add,← hQ,sandwich_inverse_left Y Q hY]
  obtain ⟨W,hW,_⟩ := linConstraint_positive_inverse X Y P Q (eta c A x)
    (eta_positive hc A hx) hX hY hPpos hQpos hε hPX hQY
  have he : (U,V) = (sandwich X (responseInput A l F),sandwich Y (responseInput A m G)) := by
    apply W.injective
    rw [hW,hW,Variational.linConstraint_apply,Variational.linConstraint_apply]
    apply Prod.ext <;> dsimp only [Prod.fst, Prod.snd]
    · erw [hU,first_rhs_rescaled c A x h Hh T l hA hrank Y hl hHT,
        sandwich_inverse_right X _ hX,eta_response c A x hA hrank l m G hlm Y,
        ← responseInput_sub,hF]
    · erw [hV,second_rhs_rescaled c A x h Hh T m hA hrank X hm hHT,
        sandwich_inverse_right Y _ hY,eta_response c A x hA hrank m l F
          (fun i => (mul_comm (m i) (l i)).trans (hlm i)) X,← responseInput_sub,hG,responseInput_neg]
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

end
end CurrentKS.Interaction

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

lemma C1_ge_one : (1 : ℝ) ≤ p.C1 := le_max_left ..
lemma C1_pos : 0 < p.C1 := lt_of_lt_of_le (by norm_num) p.C1_ge_one

end
end CurrentKS.State.LightPoint

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StateR
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open Matrix CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction CurrentKS.Covariance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ} (p : LightPoint d N)

lemma tildeA_pos [NeZero d] (i : Fin N) : 0 < p.tildeA i := mul_pos (p.scales_pos i).2.1 (p.a_pos i)
lemma tildeB_pos [NeZero d] (i : Fin N) : 0 < p.tildeB i := mul_pos (p.scales_pos i).2.2 (p.b_pos i)
lemma wP_pos [NeZero d] (i : Fin N) : 0 < p.wP i := mul_pos (p.scales_pos i).2.1 (p.pp_pos i)
lemma wQ_pos [NeZero d] (i : Fin N) : 0 < p.wQ i := mul_pos (p.scales_pos i).2.2 (p.qq_pos i)
lemma multiplied_direction [NeZero d] (v : Covariance.E (2*N)) (i : Fin N) :
    p.T i*p.direction v i = p.resp v i := by
  exact mul_div_cancel₀ _ (p.scales_pos i).1.ne'

lemma R_first [NeZero d] (h : Coordinates N) :
    deriv (fun s => p.R (line p.x h s)) 0 = ∑ i, h i*(p.T i*(p.wP i-p.wQ i)) := by
  obtain ⟨_,_,_,_,hd,_⟩ := face_value_direction_variations (by norm_num : (0 : ℝ) ≤ 384) p.ε_pos
    p.A p.x h p.interior p.A_pos p.A_rank p.fixedPart 100 p.lower p.upper p.primal p.feasible p.minimal
    p.P p.Q p.P_pos.posSemidef p.Q_pos.posSemidef p.stationary_X p.stationary_Y
  change deriv (fun s => value p.ε (p.fixedPart+S p.A (line p.x h s)) (eta 384 p.A (line p.x h s))) 0 = _
  rw [hd]
  apply Finset.sum_congr rfl
  intro i _
  change h i*((1+384*psi₁ (p.x i)*p.b i)*p.pp i-(1-384*psi₁ (p.x i)*p.a i)*p.qq i) = _
  rw [← p.lT_eq i,← p.mT_eq i]
  dsimp only [wP,wQ]
  ring

lemma R_second [NeZero d] (v : Covariance.E (2*N)) (hv : constraintLin p.IA p.IB v = 0) :
    deriv (deriv (fun s => p.R (line p.x (p.direction v) s))) 0 ≤
      3*p.invEnergy v-192*negativeWeight p.A p.x (p.direction v) p.X p.Y p.P p.Q := by
  obtain ⟨U,V,hU,hV,_,hdd⟩ := face_value_direction_variations (by norm_num : (0 : ℝ) ≤ 384) p.ε_pos
    p.A p.x (p.direction v) p.interior p.A_pos p.A_rank p.fixedPart 100 p.lower p.upper p.primal p.feasible p.minimal
    p.P p.Q p.P_pos.posSemidef p.Q_pos.posSemidef p.stationary_X p.stationary_Y
  obtain ⟨hf,hg⟩ := constraints_responses p.IA p.IB v hv
  have hF : (fun i => fstVec v i)-(interaction 384 p.A p.m p.Y *ᵥ fun i => sndVec v i) = p.resp v := by
    funext i
    exact congrArg (fun w : Covariance.E N => w i) hf
  have hG : (fun i => sndVec v i)-(interaction 384 p.A p.l p.X *ᵥ fun i => fstVec v i) = -p.resp v := by
    funext i
    exact congrArg (fun w : Covariance.E N => w i) hg
  obtain ⟨rfl,rfl⟩ := identify_responses (by norm_num : (0 : ℝ) ≤ 384) p.ε_pos p.A p.x
    (p.direction v) (p.resp v) p.T p.l p.m (fstVec v) (sndVec v) (fun i => (p.interior i).le)
    p.A_pos p.A_rank p.X p.Y p.P p.Q U V p.X_pos p.Y_pos p.P_pos p.Q_pos p.stationary_X p.stationary_Y
    p.lm_eq p.lT_eq p.mT_eq (p.multiplied_direction v) hF hG hU hV
  simpa only [R,invEnergy,X,Y,show (384 : ℝ)/2 = 192 by norm_num] using hdd

lemma crossed_identity [NeZero d] (i : Fin N) :
    p.tildeA i*p.wQ i+p.tildeB i*p.wP i = psi (p.x i)*(p.b i*p.pp i+p.a i*p.qq i) := by
  dsimp only [tildeA,tildeB,wP,wQ]
  rw [← p.lm_eq i]
  ring

lemma negativeWeight_lower [NeZero d] (v : Covariance.E (2*N)) :
    (1/3 : ℝ)*(∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(p.resp v i)^2) ≤
      negativeWeight p.A p.x (p.direction v) p.X p.Y p.P p.Q := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change (1/3 : ℝ)*((p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(p.resp v i)^2) ≤
    kappa (p.x i)*(p.direction v i)^2*(p.b i*p.pp i+p.a i*p.qq i)
  rw [p.crossed_identity i]
  have h₁ : (1/3 : ℝ)*psi (p.x i) ≤ kappa (p.x i)/p.T i^2 := by
    have hh := (psi_bounds (p.interior i).le).2
    linarith [(p.kappa_bounds i).1]
  have hpos : 0 ≤ (p.b i*p.pp i+p.a i*p.qq i)*(p.resp v i)^2 := by
    have ha := (p.a_pos i).le; have hb := (p.b_pos i).le
    have hp := (p.pp_pos i).le; have hq := (p.qq_pos i).le
    positivity
  have hh := mul_le_mul_of_nonneg_right h₁ hpos
  dsimp only [direction]
  convert hh using 1 <;> first | rfl | ring

lemma R_second_rescaled [NeZero d] (v : Covariance.E (2*N)) (hv : constraintLin p.IA p.IB v = 0) :
    deriv (deriv (fun s => p.R (line p.x (p.direction v) s))) 0 ≤
      3*p.invEnergy v-64*(∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(p.resp v i)^2) := by
  have h₁ := p.R_second v hv
  have h₂ := p.negativeWeight_lower v
  linarith

lemma R_ensemble_curvature [NeZero d] {Γ : Covariance.Mat (2*N)}
    (hc : ∀ j, constraintLin p.IA p.IB (column (CFC.sqrt Γ) j) = 0)
    (he : (∑ j, p.invEnergy (column (CFC.sqrt Γ) j)) ≤
      16*(∑ i,(p.tildeA i*p.wP i+p.tildeB i*p.wQ i)*
        (∑ j,(p.resp (column (CFC.sqrt Γ) j) i)^2))) :
    (1/2 : ℝ)*(∑ j,deriv (deriv (fun s => p.R (line p.x (p.direction (column (CFC.sqrt Γ) j)) s))) 0) ≤
      24*(∑ i,(p.tildeA i*p.wP i+p.tildeB i*p.wQ i)*(∑ j,(p.resp (column (CFC.sqrt Γ) j) i)^2))-
      32*(∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(∑ j,(p.resp (column (CFC.sqrt Γ) j) i)^2)) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) fun j _ => p.R_second_rescaled (column (CFC.sqrt Γ) j) (hc j)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hh
  have hs : (∑ j,∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(p.resp (column (CFC.sqrt Γ) j) i)^2) =
      ∑ i,(p.tildeA i*p.wQ i+p.tildeB i*p.wP i)*(∑ j,(p.resp (column (CFC.sqrt Γ) j) i)^2) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hs] at hh
  linarith

end
end CurrentKS.State.LightPoint

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StatePsi
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction CurrentKS.Covariance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ} (p : LightPoint d N)

lemma omega_nonneg (Γ : Covariance.Mat (2*N)) (i : Fin N) : 0 ≤ p.omega Γ i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma R_driftCurvature_nonpos [NeZero d] {Γ : Covariance.Mat (2*N)}
    (hc : ∀ j, constraintLin p.IA p.IB (column (CFC.sqrt Γ) j) = 0)
    (he : (∑ j, p.invEnergy (column (CFC.sqrt Γ) j)) ≤
      16*(∑ i,(p.tildeA i*p.wP i+p.tildeB i*p.wQ i)*p.omega Γ i)) :
    p.driftCurvature p.R Γ ≤ 0 := by
  have hh := p.R_ensemble_curvature hc he
  have hd := Progress.weighted_drift_nonpositive p.T p.tildeA p.tildeB p.wP p.wQ (p.omega Γ)
    (fun i => (p.scales_pos i).1.ne') (fun i => (p.tildeA_pos i).le) (fun i => (p.tildeB_pos i).le)
    (fun i => (p.wP_pos i).le) (fun i => (p.wQ_pos i).le) (p.omega_nonneg Γ) hh
  dsimp only [driftCurvature]
  rw [p.R_first]
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma dirs_energy (Γ : Covariance.Mat (2*N)) :
    (∑ j,∑ i,(p.dirs Γ j i)^2) = ∑ i,p.omega Γ i/p.T i^2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dirs,direction,div_pow,omega,Finset.sum_div]

lemma penalty_driftCurvature [NeZero d] (Γ : Covariance.Mat (2*N)) :
    p.driftCurvature penalty Γ ≤ -(1/8 : ℝ)*(∑ i,p.omega Γ i) := by
  have hh := Progress.penalty_drift_quantitative p.T p.tildeA p.tildeB (p.omega Γ)
    (fun i => psi (p.x i)) (fun i => psi₁ (p.x i)) (fun i => kappa (p.x i))
    (fun i => (p.scales_pos i).1) (fun i => (p.tildeA_pos i).le) (fun i => (p.tildeB_pos i).le)
    (p.omega_nonneg Γ) (fun i => psi_pos (p.interior i)) (fun i => (kappa_pos (p.interior i)).le)
    (fun i => (div_le_one (mul_pos (psi_pos (p.interior i)) (kappa_pos (p.interior i)))).mp
      (abs_derivative_ratio_le (p.interior i))) (fun i => (p.drift_bounds i).1) (fun i => (p.kappa_bounds i).1)
  dsimp only [driftCurvature]
  rw [penalty_line_first p.x (p.mu Γ) p.interior]
  simp_rw [penalty_line_second p.x _ p.interior]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [penalty₁,penalty₂,mu,dirs,direction]
  rw [Finset.sum_comm (f := fun j i => -kappa (p.x i)*(p.resp (column (CFC.sqrt Γ) j) i/p.T i)^2)]
  simp only [Finset.mul_sum,Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [omega]
  simp only [Finset.sum_div,Finset.mul_sum,← Finset.sum_neg_distrib]
  symm
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem exists_descent_ensemble_oai [NeZero d] (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ Γ : Covariance.Mat (2*N), Γ.PosSemidef ∧
      (∀ i, |p.mu Γ i| ≤ p.C1) ∧
      (∑ j,∑ i,(p.dirs Γ j i)^2) ≤ 8*p.C1*N ∧
      p.driftCurvature (p.Psi lam) Γ ≤ -lam*N/(8*p.C1) := by
  obtain ⟨Γ,hΓ,_,hb,ht,hc,he⟩ := state_energy_ensemble (show (384 : ℝ) ≤ 384 from le_rfl) p.ε_pos.le
    p.A p.x p.A_pos p.A_ne_zero p.A_rank p.l p.m (fun i => (p.scales_pos i).2.1)
    (fun i => (p.scales_pos i).2.2) p.lm_eq p.X p.Y p.P p.Q p.X_pos p.Y_pos p.P_pos p.Q_pos
    p.stationary_X p.stationary_Y p.product_bound
  have hem : (∑ j,p.invEnergy (column (CFC.sqrt Γ) j)) ≤
      16*(∑ i,(p.tildeA i*p.wP i+p.tildeB i*p.wQ i)*p.omega Γ i) := he
  obtain ⟨hlo,hi⟩ := p.covariance_movement_bounds hΓ hb ht hc
  change (N : ℝ)/p.C1 ≤ ∑ i,p.omega Γ i at hlo
  change ∀ i, p.omega Γ i ≤ p.C1 at hi
  refine ⟨Γ,hΓ,?_,?_,?_⟩
  · intro i
    exact Progress.drift_size (p.scales_pos i).1 (p.tildeA_pos i).le (p.tildeB_pos i).le
      (p.omega_nonneg Γ i) (p.drift_bounds i).2 (hi i)
  · rw [p.dirs_energy]
    calc
      _ ≤ ∑ _ : Fin N, (3/2 : ℝ)*p.C1 := by
        apply Finset.sum_le_sum
        intro i _
        have hh := mul_le_mul_of_nonneg_left (p.kappa_bounds i).2 (p.omega_nonneg Γ i)
        have hhi := mul_le_mul_of_nonneg_left (hi i) (by norm_num : (0 : ℝ) ≤ 3/2)
        rw [div_eq_mul_inv]
        nlinarith
      _ ≤ 8*p.C1*N := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith [p.C1_pos]
  · rw [p.Psi_driftCurvature]
    apply Progress.combine_progress hlam p.C1_pos (p.R_driftCurvature_nonpos hc hem)
    have hh := p.penalty_driftCurvature Γ
    have heq : -(1/8 : ℝ)*((N : ℝ)/p.C1) = -(N : ℝ)/(8*p.C1) := by ring
    rw [← heq]
    linarith

end
end CurrentKS.State.LightPoint

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.State.LightPoint.exists_descent_ensemble_oai := @OAI.CurrentKS.State.LightPoint.exists_descent_ensemble_oai
