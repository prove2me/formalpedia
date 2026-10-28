-- Prove2me | solution 1 for OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:36:14.409862+00:00
-- url     : https://prove2.me/submissions/5fb0083d-630f-409c-88ca-74da3445004f

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_field_logdet_uniform
import Theorems.Thm_OAI_SKGap_positive_time_root_stability
import Theorems.Thm_OAI_SKGap_smalltime_bad_integral

section
-- module Solutions.OAIQ072_SK.Compat
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableFields
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix
namespace SKGap

theorem overlap_nonneg {n : ℕ} (y : Field n) : 0 ≤ overlap y :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem overlap_lt_one {n : ℕ} (hn : 0 < n) (y : Field n) : overlap y < 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_lt_iff₀ hn').mpr
  simp only [one_mul]
  calc
    (∑ i, magnetization y i ^ 2) < ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
      · intro i _
        exact tanh_sq_lt_one (y i)
    _ = n := by simp

theorem vectorSqNorm_nonneg {n : ℕ} (x : Field n) : 0 ≤ vectorSqNorm x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem hessian_quadratic_formula {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y A x : Field n) :
    quadraticForm (fieldHessian j J y A) x = vectorSqNorm x +
      onsager j y * vectorSqNorm (fun i => sqrt (A i) * x i) -
      quadraticForm J (fun i => sqrt (A i) * x i) -
      (2 * j / n) * (∑ i, magnetization y i * (sqrt (A i) * x i)) ^ 2 := by
  have hi (i : Fin n) :
      (∑ k, x i * fieldHessian j J y A i k * x k) = x i ^ 2 +
        onsager j y * (sqrt (A i) * x i) ^ 2 -
        (∑ k, (sqrt (A i) * x i) * J i k * (sqrt (A k) * x k)) -
        (2 * j / n) * (magnetization y i * (sqrt (A i) * x i)) *
          (∑ k, magnetization y k * (sqrt (A k) * x k)) := by
    calc
      _ = ∑ k, ((if i = k then x i ^ 2 else 0) +
          (if i = k then onsager j y * (sqrt (A i) * x i) ^ 2 else 0) -
          (sqrt (A i) * x i) * J i k * (sqrt (A k) * x k) -
          (2 * j / n) * (magnetization y i * (sqrt (A i) * x i)) *
            (magnetization y k * (sqrt (A k) * x k))) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : i = k
        · subst k
          simp only [fieldHessian, hessianCore, ↓reduceIte]
          ring
        · simp only [fieldHessian, hessianCore, ite_eq_right hk]
          ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
  unfold quadraticForm
  simp_rw [hi]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, vectorSqNorm]
  ring

theorem hessian_lower_bound {n : ℕ} (hn : 0 < n) {j R a : ℝ}
    (hj : 0 ≤ j) {J : Matrix (Fin n) (Fin n) ℝ} (y A : Field n)
    (hA0 : ∀ i, 0 ≤ A i) (hAa : ∀ i, A i ≤ a)
    (hJ : ∀ v : Field n, quadraticForm J v ≤ R * vectorSqNorm v)
    (hcoef : 0 ≤ R - j + 3 * j * overlap y) (x : Field n) :
    (1 - a * (R - j + 3 * j * overlap y)) * vectorSqNorm x ≤
      quadraticForm (fieldHessian j J y A) x := by
  let v : Field n := fun i => sqrt (A i) * x i
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (∑ i, magnetization y i ^ 2) = n * overlap y := by
    unfold overlap
    field_simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (magnetization y) v
  rw [hm] at hcs
  have hscale : 0 ≤ 2 * j / (n : ℝ) := by positivity
  have hrank : (2 * j / n) * (∑ i, magnetization y i * v i) ^ 2 ≤
      2 * j * overlap y * vectorSqNorm v := by
    have he : (2 * j / n) * ((n : ℝ) * overlap y * vectorSqNorm v) =
        2 * j * overlap y * vectorSqNorm v := by field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_left hcs hscale
  have hv : vectorSqNorm v ≤ a * vectorSqNorm x := by
    rw [vectorSqNorm, vectorSqNorm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    dsimp [v]
    rw [mul_pow, sq_sqrt (hA0 i)]
    exact mul_le_mul_of_nonneg_right (hAa i) (sq_nonneg _)
  rw [hessian_quadratic_formula]
  change (1 - a * (R - j + 3 * j * overlap y)) * vectorSqNorm x ≤
    vectorSqNorm x + onsager j y * vectorSqNorm v - quadraticForm J v -
      (2 * j / n) * (∑ i, magnetization y i * v i) ^ 2
  have hmul := mul_le_mul_of_nonneg_left hv hcoef
  dsimp [onsager]
  nlinarith [hJ v, hrank]

theorem magnetization_hasFDerivAt {n : ℕ} (y : Field n) (i : Fin n) :
    HasFDerivAt (fun z : Field n => magnetization z i)
      (spinVariance y i • (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y :=
  (hasDerivAt_tanh (y i)).comp_hasFDerivAt y (hasFDerivAt_apply i y)

theorem overlap_hasFDerivAt {n : ℕ} (y : Field n) :
    HasFDerivAt overlap (overlapDerivative y) y := by
  have hd := (HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).pow 2)).const_mul (n : ℝ)⁻¹
  convert! hd using 1
  · ext z
    simp only [overlap, Finset.sum_apply, div_eq_mul_inv]
    ring
  · ext v
    simp only [overlapDerivative, _root_.smul_apply,
      _root_.sum_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      nsmul_eq_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring

theorem onsager_hasFDerivAt {n : ℕ} (j : ℝ) (y : Field n) :
    HasFDerivAt (onsager j) (-j • overlapDerivative y) y := by
  convert! ((overlap_hasFDerivAt y).const_sub 1).const_mul j using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [_root_.smul_apply, smul_eq_mul, _root_.neg_apply]
  ring

theorem tapField_hasFDerivAt {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    HasFDerivAt (tapField j J h)
      ((fieldJacobian j J y).mulVecLin.toContinuousLinearMap) y := by
  rw [hasFDerivAt_pi']
  intro i
  have hfirst := ((hasFDerivAt_apply i y).sub_const (h i)).add
    ((onsager_hasFDerivAt j y).mul (magnetization_hasFDerivAt y i))
  have hlast := HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).const_mul (J i k))
  convert! hfirst.sub hlast using 1
  · ext z
    simp only [tapField, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, fieldJacobian, hessianCore, _root_.sub_apply,
      _root_.add_apply, _root_.smul_apply,
      _root_.sum_apply, smul_eq_mul, overlapDerivative]
    have hdelta : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) = v i := by
      simp
    have hdeltaV : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
        spinVariance y k * v k) = spinVariance y i * v i := by simp
    calc
      _ = (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) +
          onsager j y * (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
            spinVariance y k * v k) -
          (∑ k, J i k * (spinVariance y k * v k)) -
          (2 * j / n) * magnetization y i *
            (∑ k, (magnetization y k * spinVariance y k) * v k) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [hdelta, hdeltaV]
        ring

theorem vectorNorm_nonneg {n : ℕ} (x : Field n) : 0 ≤ vectorNorm x := norm_nonneg _

theorem vectorNorm_sq {n : ℕ} (x : Field n) : vectorNorm x ^ 2 = vectorSqNorm x := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

theorem vectorNorm_add_le {n : ℕ} (x z : Field n) :
    vectorNorm (x + z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_sub_le {n : ℕ} (x z : Field n) :
    vectorNorm (x - z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_smul {n : ℕ} (a : ℝ) (x : Field n) :
    vectorNorm (fun i => a * x i) = |a| * vectorNorm x := by
  exact norm_smul a (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))

theorem vector_dot_abs_le {n : ℕ} (x z : Field n) :
    |∑ i, x i * z i| ≤ vectorNorm x * vectorNorm z := by
  simpa only [vectorNorm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    PiLp.toLp_apply, mul_comm] using
    abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_diag_le {n : ℕ} {a : Field n} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, |a i| ≤ M) (x : Field n) :
    vectorNorm (fun i => a i * x i) ≤ M * vectorNorm x := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (mul_nonneg hM (vectorNorm_nonneg _))).mp
  rw [mul_pow, vectorNorm_sq, vectorNorm_sq]
  unfold vectorSqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_pow]
  have hi : a i ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hM).mpr (ha i)
  exact mul_le_mul_of_nonneg_right hi (sq_nonneg (x i))

attribute [local irreducible] vectorNorm

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_ConditionalBadSet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma isClosed_badFieldSet (n : ℕ) (j A ε c : ℝ) : IsClosed (badFieldSet n j A ε c) := by
  let X := ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) × ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  let : CompactSpace ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let S : Set (X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ))) :=
    {p | (∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2) ≤ ε^2*(n:ℝ) ∧
      quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1) (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp ≤ c}
  have ha (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.1:Fin n → ℝ) i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
  have hx (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp i) :=
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin n=>ℝ)).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hy (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      tanh (p.2.2 i)) := continuous_tanh.comp ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  have hS : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        ∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2)
        (g := fun _ => ε^2*(n:ℝ)) (by
        apply continuous_finsetSum
        intro i _
        exact ((ha i).sub (continuous_const.sub ((hy i).pow 2))).pow 2) continuous_const
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1)
          (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp) (g := fun _=>c) (by
        dsimp [X,quadraticForm,fieldHessian,hessianCore,plantedInteraction,onsager,overlap,magnetization]
        apply continuous_finsetSum; intro i _
        apply continuous_finsetSum; intro k _
        apply Continuous.mul _ (hx k)
        apply Continuous.mul (hx i)
        apply Continuous.add continuous_const
        apply Continuous.mul _ (Real.continuous_sqrt.comp (ha k))
        apply Continuous.mul (Real.continuous_sqrt.comp (ha i))
        exact (((continuous_const.mul (continuous_const.sub
          ((continuous_finsetSum _ (fun l _ => (hy l).pow 2)).div_const _))).mul continuous_const).sub
          ((by fun_prop : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) => p.2.1 i k)).add continuous_const)).sub
          (((continuous_const.mul (hy i))).mul (hy k))) continuous_const
  have hproj := isClosedMap_snd_of_compactSpace S hS
  convert hproj using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨a,ha,hclose,x,hx,hquad⟩
    have ha' : a ∈ Icc (0 : Fin n → ℝ) (fun _=>A) := ⟨fun i=>(ha i).1,fun i=>(ha i).2⟩
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
    exact ⟨((⟨a,ha'⟩,⟨x,hx'⟩),p),⟨hclose,hquad⟩,rfl⟩
  · rintro ⟨⟨⟨a,x⟩,p'⟩,hS,rfl⟩
    exact ⟨a,fun i=>⟨a.2.1 i,a.2.2 i⟩,hS.1,x,by simpa only [Metric.mem_sphere,dist_zero_right] using x.2,hS.2⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

lemma coordinate_hasLaw {κ : Type*} [Fintype κ] (i : κ) :
    HasLaw (fun g : κ → ℝ => g i) (gaussianReal 0 1) (gaussianCoordinates κ) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) i).map_eq⟩

lemma coordinates_gaussian {κ : Type*} [Fintype κ] :
    HasGaussianLaw (fun g : κ → ℝ => g) (gaussianCoordinates κ) :=
  (iIndepFun_pi (fun _ : κ => aemeasurable_id)).hasGaussianLaw
    (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (i k : κ) :
    cov[fun g : κ → ℝ => g i,fun g : κ → ℝ => g k;gaussianCoordinates κ] =
      if i=k then 1 else 0 := by
  by_cases h : i=k
  · subst k
    rw [ite_eq_left rfl,covariance_self (measurable_pi_apply i).aemeasurable,
      (coordinate_hasLaw i).variance_eq]
    simp
  · rw [ite_eq_right h]
    exact ((iIndepFun_pi (fun _ : κ => aemeasurable_id)).indepFun h).covariance_eq_zero
      (coordinate_hasLaw i).hasGaussianLaw.memLp_two (coordinate_hasLaw k).hasGaussianLaw.memLp_two

lemma linear_gaussian_mean {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    (∫ g, ∑ i, a i*g i ∂gaussianCoordinates κ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => (coordinate_hasLaw i).hasGaussianLaw.integrable.const_mul _)]
  simp [integral_const_mul,(coordinate_hasLaw _).integral_eq]

lemma linear_gaussian_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (a b : κ → ℝ) :
    cov[fun g => ∑ i, a i*g i,fun g => ∑ i, b i*g i;gaussianCoordinates κ] =
      ∑ i, a i*b i := by
  rw [covariance_fun_sum_fun_sum
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,coordinate_covariance]
  simp [mul_comm]

lemma matrix_sample_gaussian {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    HasGaussianLaw (fun g => A*ᵥg) (gaussianCoordinates κ) :=
  coordinates_gaussian.map_fun (GaussianRegression.matrixCLM A)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_GaussianExponentialLinear
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators

lemma linear_gaussian_law {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    HasLaw (fun g : κ→ℝ=>∑ i,a i*g i) (gaussianReal 0 (∑ i,a i^2).toNNReal)
      (gaussianCoordinates κ) := by
  let A : Matrix Unit κ ℝ := fun _=>a
  have hg := (matrix_sample_gaussian A).eval ()
  change HasGaussianLaw (fun g : κ→ℝ=>∑ i,a i*g i) (gaussianCoordinates κ) at hg
  have hl : HasLaw _ _ _ := ⟨hg.aemeasurable,hg.map_eq_gaussianReal⟩
  have hm := linear_gaussian_mean a
  have hv : Var[fun g=>∑ i,a i*g i;gaussianCoordinates κ]=∑ i,a i^2 := by
    rw [← covariance_self hg.aemeasurable]
    simpa only [sq] using linear_gaussian_covariance a a
  change HasLaw (fun g : κ→ℝ=>∑ i,a i*g i) _ _ at hl
  rw [hm,hv] at hl
  exact hl

lemma linear_gaussian_exp_integrable {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    Integrable (fun g : κ→ℝ=>exp (∑ i,a i*g i)) (gaussianCoordinates κ) := by
  have hl := linear_gaussian_law a
  have hi : Integrable exp (gaussianReal 0 (∑ i,a i^2).toNNReal) := by
    simpa using (integrable_exp_mul_gaussianReal (μ:=0) (v:=(∑ i,a i^2).toNNReal) 1)
  rw [← hl.map_eq] at hi
  exact (integrable_map_measure (by fun_prop) hl.aemeasurable).mp hi

lemma linear_gaussian_exp_integral {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    (∫ g : κ→ℝ,exp (∑ i,a i*g i) ∂gaussianCoordinates κ)=exp ((∑ i,a i^2)/2) := by
  have hl := linear_gaussian_law a
  have he := mgf_gaussianReal hl.map_eq 1
  simpa only [mgf,one_mul,zero_mul,one_pow,mul_one,zero_add,
    coe_toNNReal _ (Finset.sum_nonneg (fun i _=>sq_nonneg (a i)))] using he

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianTiltMass
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

lemma absorb_finite_exponential_factor (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℝ,
      (M:ℝ)*exp ((n:ℝ)*r) ≤ exp ((n:ℝ)*(r+ε)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (log ((M:ℝ)+1)/ε)
  refine ⟨N,?_⟩
  intro n hn r
  have hcast : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : log ((M:ℝ)+1) ≤ (n:ℝ)*ε := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  have he : (M:ℝ) ≤ exp ((n:ℝ)*ε) := by
    have h := exp_le_exp.mpr hnlog
    rw [exp_log (by positivity)] at h
    linarith
  calc
    _ ≤ exp ((n:ℝ)*ε)*exp ((n:ℝ)*r) := mul_le_mul_of_nonneg_right he (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

end SKGap

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ProductGaussianDensity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
namespace SKGap.GaussianDensity
variable {ι : Type*} [Fintype ι]

theorem pi_gaussian_density (m : ι → ℝ) (v : ι → ℝ≥0) (hv : ∀ i,v i ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) (v i)) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (∏ i,gaussianPDFReal (m i) (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun x : ι → ℝ => ∏ i,gaussianPDFReal (m i) (v i) (x i))
      (volume.restrict (Set.univ.pi s)) := by
    exact (Integrable.fintype_prod (fun i => integrable_gaussianPDFReal (m i) (v i))).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)))]
  change ENNReal.ofReal (∫ x, (∏ i,gaussianPDFReal (m i) (v i) (x i))
    ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s))=_
  rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_of_var_ne_zero _ (hv i),withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal (m i) (v i)).restrict
    (Filter.Eventually.of_forall (gaussianPDFReal_nonneg _ _))

lemma measurable_productPDF (m : ι → ℝ) (v : ι → ℝ≥0) :
    Measurable (fun x : ι → ℝ => ENNReal.ofReal (∏ i,gaussianPDFReal (m i) (v i) (x i))) := by
  fun_prop

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixCoordinates
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap

variable {ι : Type*}

variable [Fintype ι]

lemma rawCoordinateMatrix_norm (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖rawCoordinateMatrix g‖ ≤ ‖g‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← sq]
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_sq_eq]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type,Fintype.sum_prod_type,
    rawCoordinateMatrix]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma goeMatrix_norm (r : ℝ) (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖goeMatrix r g‖ ≤ sqrt (2*r)*‖g‖ := by
  have he : goeMatrix r g = (sqrt (2*r)/2) •
      (rawCoordinateMatrix g+(rawCoordinateMatrix g)ᵀ) := by ext; rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (sqrt (2*r)/2)*(‖rawCoordinateMatrix g‖+‖(rawCoordinateMatrix g)ᵀ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = sqrt (2*r)*‖rawCoordinateMatrix g‖ := by rw [Matrix.frobenius_norm_transpose]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rawCoordinateMatrix_norm g) (sqrt_nonneg _)

omit [Fintype ι] in
lemma goeMatrix_sub (r : ℝ) (g h : MatrixCoordinates ι → ℝ) :
    goeMatrix r (g-h) = goeMatrix r g-goeMatrix r h := by
  ext i k; simp only [goeMatrix,Pi.sub_apply,Matrix.sub_apply]; ring

lemma goeMatrix_L2_lipschitz (r : ℝ) :
    LipschitzWith ⟨sqrt (2*r),sqrt_nonneg _⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => goeMatrix r g) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simpa only [dist_eq_norm,← goeMatrix_sub] using! goeMatrix_norm r (g-h)

lemma goeMatrix_pi_lipschitz (r : ℝ) :
    LipschitzWith (⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
      (goeMatrix (ι := ι) r) := by
  exact (goeMatrix_L2_lipschitz (ι := ι) r).comp
    (PiLp.lipschitzWith_toLp 2 (fun _ : MatrixCoordinates ι => ℝ))

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GOEGaussian
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goeEntryCoeff_sample (r : ℝ) (g : MatrixCoordinates ι → ℝ) (i k : ι) :
    (goeEntryCoeff r*ᵥg) (i,k) = goeMatrix r g i k := by
  simp only [mulVec,dotProduct,goeEntryCoeff,mul_assoc,add_mul]
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  simp [goeMatrix]

lemma goe_matrix_gaussian (r : ℝ) :
    HasGaussianLaw (fun (g : MatrixCoordinates ι → ℝ) (p : ι × ι) => goeMatrix r g p.1 p.2) (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := matrix_sample_gaussian (goeEntryCoeff (ι := ι) r)
  simpa only [show (fun g => goeEntryCoeff (ι := ι) r*ᵥg) =
    (fun g p => goeMatrix r g p.1 p.2) from funext (fun g => funext (fun p => goeEntryCoeff_sample r g p.1 p.2))] using hh

lemma goe_mean_zero (r : ℝ) (i k : ι) :
    (∫ g, goeMatrix r g i k ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  simpa only [← goeEntryCoeff_sample,mulVec,dotProduct] using linear_gaussian_mean (goeEntryCoeff (ι := ι) r (i,k))

lemma goe_entry_cov {r : ℝ} (hr : 0 ≤ r) (i k l m : ι) :
    cov[fun g => goeMatrix r g i k,fun g => goeMatrix r g l m;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then 1 else 0)*(if k=m then 1 else 0)+
       (if i=m then 1 else 0)*(if k=l then 1 else 0)) := by
  let μ := gaussianCoordinates (MatrixCoordinates ι)
  have hm (a : MatrixCoordinates ι) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  change cov[fun g : MatrixCoordinates ι → ℝ => sqrt (2*r)/2*(g (.inl (i,k))+g (.inl (k,i))),
    fun g => sqrt (2*r)/2*(g (.inl (l,m))+g (.inl (m,l))); μ]=_
  rw [covariance_const_mul_left,covariance_const_mul_right]
  change sqrt (2*r)/2*(sqrt (2*r)/2*cov[(fun g => g (.inl (i,k))) + (fun g => g (.inl (k,i))),
    (fun g => g (.inl (l,m))) + (fun g => g (.inl (m,l)));gaussianCoordinates (MatrixCoordinates ι)]) = _
  rw [covariance_add_left (hm _) (hm _) ((hm _).add (hm _)),
    covariance_add_right (hm _) (hm _) (hm _),
    covariance_add_right (hm _) (hm _) (hm _)]
  simp only [coordinate_covariance,Sum.inl.injEq,Prod.mk.injEq]
  have hs : (sqrt (2*r)/2)^2=r/2 := by rw [div_pow,sq_sqrt (by positivity)]; ring
  have hs' : sqrt (2*r)/2*(sqrt (2*r)/2)=r/2 := by nlinarith only [hs]
  rw [← mul_assoc,hs']
  have hind (p q : Prop) [Decidable p] [Decidable q] :
      (if p ∧ q then (1:ℝ) else 0)=(if p then 1 else 0)*(if q then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hind]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_FiniteSpinCalculus
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKGap

section FiniteSpinCalculus

variable {n : ℕ}

theorem coupling_symm (g : Disorder n) (i k : Fin n) : coupling g i k = coupling g k i := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · simp [coupling, hik, not_lt_of_gt hik]
  · rfl
  · simp [coupling, hki, not_lt_of_gt hki]

end FiniteSpinCalculus

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianQuadratic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
namespace SKGap
open scoped BigOperators

lemma gaussian_integrable_pow (k : ℕ) :
    Integrable (fun x : ℝ => x^k) (gaussianReal 0 1) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq, norm_pow] using
    (IsGaussian.memLp_id (gaussianReal 0 1) (k : ℝ≥0∞) (by simp)).integrable_norm_pow'

lemma gaussian_memLp_sq : MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using gaussian_integrable_pow 4

lemma gaussian_integral_sq : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h
  simpa only [sub_zero, NNReal.coe_one] using h

lemma gaussian_integral_fourth : (∫ x : ℝ, x^4 ∂gaussianReal 0 1) = 3 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x^3) (3*x^2) x := by
    convert! (hasDerivAt_id x).pow 3 using 1; norm_num [Pi.pow_apply, id_eq]
  have hi : Integrable (fun x : ℝ => (x - 0)*x^3) (gaussianReal 0 1) := by
    simpa only [sub_zero, ← pow_succ'] using gaussian_integrable_pow 4
  have h := gaussian_integration_by_parts (by norm_num : (1 : ℝ≥0) ≠ 0)
    hd (gaussian_integrable_pow 3) ((gaussian_integrable_pow 2).const_mul 3) hi
  simpa only [sub_zero, ← pow_succ', integral_const_mul, gaussian_integral_sq,
    NNReal.coe_one, one_mul, mul_one] using h

section Quadratic
variable {ι : Type*} [Fintype ι]

lemma gaussianQuadratic_memLp (a : ι → ℝ) :
    MemLp (gaussianQuadratic a) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  apply memLp_finsetSum
  intro i _
  exact ((gaussian_memLp_sq.const_mul (a i)).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i))

lemma gaussianQuadratic_mean (a : ι → ℝ) :
    (∫ x, gaussianQuadratic a x ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = ∑ i, a i := by
  unfold gaussianQuadratic
  have hi (i : ι) : Integrable (fun x : ι → ℝ => a i * (x i)^2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    ((gaussian_memLp_sq.const_mul (a i)).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)).integrable (by norm_num)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  have he : (∫ x : ι → ℝ, (x i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∫ y : ℝ, y^2 ∂gaussianReal 0 1 :=
    integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
      (f := fun y : ℝ => y^2) (by fun_prop)
  rw [he, gaussian_integral_sq, mul_one]

end Quadratic

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWhitening
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype κ] in
lemma positive_sqrt_data {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∃ R : Matrix ι ι ℝ, R.IsHermitian ∧ R*R=S ∧ IsUnit R.det := by
  let R := CFC.sqrt S
  have hR : R.IsHermitian := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hsq : R*R=S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hu : IsUnit R := isUnit_of_mul_isUnit_left (hsq.symm ▸ hS.isUnit)
  exact ⟨R,hR,hsq,(Matrix.isUnit_iff_isUnit_det R).mp hu⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_WeightedMomentComparison
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma sum_abs_le_sqrt_card_l2 (d : ι → ℝ) :
    (∑ i, |d i|) ≤ √(Fintype.card ι:ℝ)*√(∑ i,d i^2) := by
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι => (1:ℝ)) (fun i => |d i|)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianVectorMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal

lemma gaussian_integral_fourth_variance (v : ℝ≥0) :
    (∫ x : ℝ,x^4 ∂gaussianReal 0 v)=3*(v:ℝ)^2 := by
  have hm : (gaussianReal 0 1).map (fun x : ℝ => sqrt (v:ℝ)*x)=gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hm,integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow,integral_const_mul,gaussian_integral_fourth]
  rw [show sqrt (v:ℝ)^4=(v:ℝ)^2 by rw [show 4=2*2 by norm_num,pow_mul,Real.sq_sqrt v.coe_nonneg]]
  ring

lemma gaussian_fourth_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^4) (gaussianReal 0 v) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq,norm_pow] using
    (IsGaussian.memLp_id (gaussianReal 0 v) (4:ℝ≥0∞) (by norm_num)).integrable_norm_pow'

lemma linear_gaussian_fourth {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    (∫ g,(∑ i,a i*g i)^4 ∂gaussianCoordinates κ)=3*(∑ i,a i^2)^2 := by
  let A : Matrix Unit κ ℝ := fun _ => a
  have hg := (matrix_sample_gaussian A).eval ()
  change HasGaussianLaw (fun g : κ → ℝ => ∑ i,a i*g i) (gaussianCoordinates κ) at hg
  have hl : HasLaw _ _ _ := ⟨hg.aemeasurable,hg.map_eq_gaussianReal⟩
  have hm := linear_gaussian_mean a
  have hv : Var[fun g => ∑ i,a i*g i;gaussianCoordinates κ]=∑ i,a i^2 := by
    rw [← covariance_self hg.aemeasurable]
    simpa only [sq] using linear_gaussian_covariance a a
  change HasLaw (fun g : κ → ℝ => ∑ i,a i*g i) _ _ at hl
  rw [hm,hv] at hl
  have he := hl.integral_comp (f := fun x : ℝ => x^4) (by fun_prop)
  simp only [Function.comp_def] at he
  rw [he,gaussian_integral_fourth_variance]
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)))]

lemma linear_gaussian_fourth_integrable {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    Integrable (fun g => (∑ i,a i*g i)^4) (gaussianCoordinates κ) := by
  let A : Matrix Unit κ ℝ := fun _ => a
  have hg := (matrix_sample_gaussian A).eval ()
  change HasGaussianLaw (fun g : κ → ℝ => ∑ i,a i*g i) (gaussianCoordinates κ) at hg
  have hl : HasLaw _ _ _ := ⟨hg.aemeasurable,hg.map_eq_gaussianReal⟩
  rw [linear_gaussian_mean a] at hl
  have hi := gaussian_fourth_integrable (Var[fun g : κ → ℝ => ∑ i,a i*g i;gaussianCoordinates κ].toNNReal)
  rw [← hl.map_eq] at hi
  exact (integrable_map_measure (by fun_prop) hl.aemeasurable).mp hi

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TAPScalarTaylor
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Set

lemma scalar_remainder_of_lipschitz_derivative {f f' : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hl : ∀ x y, |f' x-f' y| ≤ L*|x-y|) (x d : ℝ) :
    |f (x+d)-f x-f' x*d| ≤ L*d^2 := by
  let R : ℝ → ℝ := fun z => f z-f x-f' x*(z-x)
  have hder (z : ℝ) : HasDerivAt R (f' z-f' x) z := by
    dsimp [R]
    convert! ((hd z).sub_const (f x)).sub (((hasDerivAt_id z).sub_const x).const_mul (f' x)) using 1; simp
  have bnd (z : ℝ) (hz : z ∈ segment ℝ x (x+d)) : ‖f' z-f' x‖ ≤ L*|d| := by
    rw [Real.norm_eq_abs]
    apply (hl z x).trans
    apply mul_le_mul_of_nonneg_left _ hL
    simpa only [Real.norm_eq_abs,add_sub_cancel_left] using norm_sub_le_of_mem_segment hz
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ segment ℝ x (x+d)) => (hder z).hasDerivWithinAt) bnd
    (convex_segment x (x+d)) (left_mem_segment ℝ x (x+d)) (right_mem_segment ℝ x (x+d))
  simpa only [R,sub_self,mul_zero,sub_zero,add_sub_cancel_left,Real.norm_eq_abs,
    mul_assoc,← pow_two,sq_abs] using hh

lemma tanh_lipschitz_abs (x y : ℝ) : |tanh x-tanh y| ≤ |x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_tanh z).hasDerivWithinAt)
    (C := 1) (fun z _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one z).le)]
      linarith [sq_nonneg (tanh z)]) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma scalar_variance_lipschitz_abs (x y : ℝ) :
    |(1-tanh x^2)-(1-tanh y^2)| ≤ 2*|x-y| := by
  have hsum : |tanh x+tanh y| ≤ 2 := (abs_add_le _ _).trans (by
    linarith [(abs_tanh_lt_one x).le,(abs_tanh_lt_one y).le])
  calc
    _ = |tanh x-tanh y| * |tanh x+tanh y| := by
      rw [show (1-tanh x^2)-(1-tanh y^2) = -((tanh x-tanh y)*(tanh x+tanh y)) by ring, abs_neg, abs_mul]
    _ ≤ |x-y| * 2 := mul_le_mul (tanh_lipschitz_abs x y) hsum (abs_nonneg _) (abs_nonneg _)
    _ = _ := mul_comm _ _

lemma tanh_scalar_remainder (x d : ℝ) :
    |tanh (x+d)-tanh x-(1-tanh x^2)*d| ≤ 2*d^2 :=
  scalar_remainder_of_lipschitz_derivative (by norm_num) hasDerivAt_tanh
    scalar_variance_lipschitz_abs x d

lemma scalar_variance_hasDeriv (x : ℝ) :
    HasDerivAt (fun z => 1-tanh z^2) (-2*tanh x*(1-tanh x^2)) x := by
  convert! (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_tanh x).pow 2) using 1; ring

lemma scalar_variance_deriv_lipschitz_abs (x y : ℝ) :
    |(-2*tanh x*(1-tanh x^2))-(-2*tanh y*(1-tanh y^2))| ≤ 6*|x-y| := by
  have hu : |tanh x| ≤ 1 := (abs_tanh_lt_one x).le
  have hv : |1-tanh y^2| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one y).le)]
    linarith [sq_nonneg (tanh y)]
  calc
    _ = 2*|tanh x*((1-tanh x^2)-(1-tanh y^2))+
        (tanh x-tanh y)*(1-tanh y^2)| := by
      rw [show (-2*tanh x*(1-tanh x^2))-(-2*tanh y*(1-tanh y^2))=
        -(2*(tanh x*((1-tanh x^2)-(1-tanh y^2))+
        (tanh x-tanh y)*(1-tanh y^2))) by ring,abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    _ ≤ 2*(|tanh x| * |(1-tanh x^2)-(1-tanh y^2)|+
        |tanh x-tanh y| * |1-tanh y^2|) := by gcongr; exact (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])
    _ ≤ 2*(1*(2*|x-y|)+|x-y| * 1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (mul_le_mul hu (scalar_variance_lipschitz_abs x y) (abs_nonneg _) (by norm_num))
        (mul_le_mul (tanh_lipschitz_abs x y) hv (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

lemma scalar_variance_remainder (x d : ℝ) :
    |(1-tanh (x+d)^2)-(1-tanh x^2)-(-2*tanh x*(1-tanh x^2))*d| ≤ 6*d^2 :=
  scalar_remainder_of_lipschitz_derivative (by norm_num) scalar_variance_hasDeriv
    scalar_variance_deriv_lipschitz_abs x d
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TAPVectorTaylor
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators

lemma varianceAverage_eq_average {n : ℕ} (hn : 0 < n) (y : Field n) :
    varianceAverage y=(∑ i,spinVariance y i)/(n:ℝ) := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  dsimp [varianceAverage,overlap,spinVariance]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp

lemma varianceAverage_bounds {n : ℕ} (hn : 0 < n) (y : Field n) :
    0 ≤ varianceAverage y ∧ varianceAverage y ≤ 1 := by
  dsimp [varianceAverage]
  exact ⟨sub_nonneg.mpr (overlap_lt_one hn y).le,sub_le_self _ (overlap_nonneg y)⟩

lemma magnetization_norm_bound {n : ℕ} (y : Field n) :
    vectorNorm (magnetization y) ≤ sqrt (n:ℝ) := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (sqrt_nonneg _)).mp
  rw [vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _i : Fin n,(1:ℝ) := Finset.sum_le_sum (fun i _ => (tanh_sq_lt_one (y i)).le)
    _ = _ := by simp

lemma vectorNorm_le_of_sq_sum {n : ℕ} {v : Field n} {c : ℝ} (hc : 0 ≤ c)
    (hb : ∑ i,v i^2 ≤ c^2) : vectorNorm v ≤ c := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) hc).mp
  exact (vectorNorm_sq v).trans_le hb

lemma magnetization_difference_norm {n : ℕ} (y d : Field n) :
    vectorNorm (magnetization (y+d)-magnetization y) ≤ vectorNorm d := by
  apply vectorNorm_le_of_sq_sum (vectorNorm_nonneg _)
  rw [vectorNorm_sq]
  apply Finset.sum_le_sum
  intro i _
  have hh := tanh_lipschitz_abs (y i+d i) (y i)
  rw [add_sub_cancel_left] at hh
  simpa only [Pi.sub_apply,Pi.add_apply,magnetization,sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hh |>.trans_eq (sq_abs (d i))

lemma magnetization_remainder_norm {n : ℕ} (y d : Field n) :
    vectorNorm (magnetizationRemainder y d) ≤ 2*sqrt (∑ i,d i^4) := by
  apply vectorNorm_le_of_sq_sum (by positivity)
  rw [mul_pow,Real.sq_sqrt (Finset.sum_nonneg (fun i _ => (by positivity : 0 ≤ d i^4))),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := tanh_scalar_remainder (y i) (d i)
  have hh' := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
  simpa only [magnetizationRemainder,Pi.sub_apply,Pi.add_apply,magnetization,spinVariance,
    sq_abs,mul_pow,← pow_mul] using hh'

lemma varianceAverage_remainder {n : ℕ} (hn : 0 < n) (y d : Field n) :
    |varianceAverage (y+d)-varianceAverage y-varianceLinear y d| ≤
      6/(n:ℝ)*vectorNorm d^2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [varianceAverage_eq_average hn,varianceAverage_eq_average hn,vectorNorm_sq]
  have he : (∑ i,spinVariance (y+d) i)/(n:ℝ)-
      (∑ i,spinVariance y i)/(n:ℝ)-varianceLinear y d=
      (∑ i,(spinVariance (y+d) i-spinVariance y i-
        (-2*magnetization y i*spinVariance y i)*d i))/(n:ℝ) := by
    have hlin : (∑ i,(-2*magnetization y i*spinVariance y i)*d i)=
        -2*∑ i,magnetization y i*spinVariance y i*d i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    simp only [varianceLinear,Finset.sum_sub_distrib,hlin]
    field_simp
  rw [he,abs_div,abs_of_pos hn0]
  apply (div_le_iff₀ hn0).mpr
  calc
    _ ≤ ∑ i,|(spinVariance (y+d) i-spinVariance y i-(-2*magnetization y i*spinVariance y i)*d i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,6*d i^2 := Finset.sum_le_sum (fun i _ => scalar_variance_remainder (y i) (d i))
    _ = _ := by simp only [vectorSqNorm,← Finset.mul_sum]; field_simp

lemma varianceAverage_difference {n : ℕ} (hn : 0 < n) (y d : Field n) :
    |varianceAverage (y+d)-varianceAverage y| ≤ 2/sqrt (n:ℝ)*vectorNorm d := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs0 : sqrt (n:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr hn0)
  rw [varianceAverage_eq_average hn,varianceAverage_eq_average hn,← sub_div,
    ← Finset.sum_sub_distrib,abs_div,abs_of_pos hn0]
  apply (div_le_iff₀ hn0).mpr
  calc
    _ ≤ ∑ i,|spinVariance (y+d) i-spinVariance y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,2*|d i| := Finset.sum_le_sum (fun i _ => by
      simpa only [spinVariance,magnetization,Pi.add_apply,add_sub_cancel_left] using scalar_variance_lipschitz_abs (y i+d i) (y i))
    _ = 2*∑ i,|d i| := by rw [Finset.mul_sum]
    _ ≤ 2*(sqrt (n:ℝ)*vectorNorm d) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hh := sum_abs_le_sqrt_card_l2 d
      have he : sqrt (∑ i,d i^2)=vectorNorm d := by
        change sqrt (vectorSqNorm d)=vectorNorm d
        rw [← vectorNorm_sq,Real.sqrt_sq (vectorNorm_nonneg _)]
      simpa only [Fintype.card_fin,he] using hh
    _ = _ := by field_simp; rw [Real.sq_sqrt hn0.le]; ring

lemma tap_remainder_identity {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y d : Field n) :
    tapField j J h (y+d)-tapField j J h y-(fieldJacobian j J y)*ᵥd=
      (j*varianceAverage y) • magnetizationRemainder y d+
      (j*(varianceAverage (y+d)-varianceAverage y-varianceLinear y d)) • magnetization y+
      (j*(varianceAverage (y+d)-varianceAverage y)) • (magnetization (y+d)-magnetization y)-
      J*ᵥmagnetizationRemainder y d := by
  have hjac (i : Fin n) : (fieldJacobian j J y*ᵥd) i=
      d i+onsager j y*(spinVariance y i*d i)-
      (∑ k,J i k*(spinVariance y k*d k))+j*varianceLinear y d*magnetization y i := by
    change (∑ k,fieldJacobian j J y i k*d k)=_
    have he : (∑ k,fieldJacobian j J y i k*d k)=
        (∑ k,(if i=k then 1 else (0:ℝ))*d k)+
        onsager j y*(∑ k,(if i=k then 1 else (0:ℝ))*spinVariance y k*d k)-
        (∑ k,J i k*(spinVariance y k*d k))-
        (2*j/(n:ℝ))*magnetization y i*(∑ k,magnetization y k*spinVariance y k*d k) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [fieldJacobian,hessianCore]
      ring
    rw [he]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    dsimp [varianceLinear]
    ring
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [hjac]
  simp only [tapField,Pi.add_apply,onsager,varianceAverage,magnetizationRemainder,Pi.sub_apply,
    Matrix.mulVec,dotProduct,mul_sub,Finset.sum_sub_distrib]
  ring

attribute [local irreducible] vectorNorm varianceAverage varianceLinear magnetizationRemainder tapField fieldJacobian magnetization

theorem tap_remainder_norm {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y d : Field n) :
    vectorNorm (tapField j J h (y+d)-tapField j J h y-(fieldJacobian j J y)*ᵥd) ≤
      2*(j+K)*sqrt (∑ i,d i^4)+(8*j/sqrt (n:ℝ))*vectorNorm d^2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hsn : sqrt (n:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr hn0)
  have hnd := vectorNorm_nonneg d
  let rm := magnetizationRemainder y d
  let rb := varianceAverage (y+d)-varianceAverage y-varianceLinear y d
  let db := varianceAverage (y+d)-varianceAverage y
  have hb := varianceAverage_bounds hn y
  have h₁ : vectorNorm ((j*varianceAverage y) • rm) ≤ j*vectorNorm rm := by
    change vectorNorm (fun i => (j*varianceAverage y)*rm i) ≤ _
    rw [vectorNorm_smul,abs_of_nonneg (mul_nonneg hj hb.1)]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hb.2]) (vectorNorm_nonneg _)
  have h₂ : vectorNorm ((j*rb) • magnetization y) ≤
      (6*j/sqrt (n:ℝ))*vectorNorm d^2 := by
    change vectorNorm (fun i => (j*rb)*magnetization y i) ≤ _
    rw [vectorNorm_smul,abs_mul,abs_of_nonneg hj]
    calc
      _ ≤ (j*(6/(n:ℝ)*vectorNorm d^2))*sqrt (n:ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (varianceAverage_remainder hn y d) hj)
          (magnetization_norm_bound y) (vectorNorm_nonneg _) (by positivity)
      _ = _ := by field_simp; rw [Real.sq_sqrt hn0.le]; ring
  have h₃ : vectorNorm ((j*db) • (magnetization (y+d)-magnetization y)) ≤
      (2*j/sqrt (n:ℝ))*vectorNorm d^2 := by
    change vectorNorm (fun i => (j*db)*(magnetization (y+d)-magnetization y) i) ≤ _
    rw [vectorNorm_smul,abs_mul,abs_of_nonneg hj]
    calc
      _ ≤ (j*(2/sqrt (n:ℝ)*vectorNorm d))*vectorNorm d :=
        mul_le_mul (mul_le_mul_of_nonneg_left (varianceAverage_difference hn y d) hj)
          (magnetization_difference_norm y d) (vectorNorm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [tap_remainder_identity]
  calc
    _ ≤ (vectorNorm ((j*varianceAverage y) • rm)+vectorNorm ((j*rb) • magnetization y)+
      vectorNorm ((j*db) • (magnetization (y+d)-magnetization y)))+vectorNorm (J*ᵥrm) := by
        exact (vectorNorm_sub_le _ _).trans
          (add_le_add ((vectorNorm_add_le _ _).trans
            (add_le_add (vectorNorm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (j*vectorNorm rm+(6*j/sqrt (n:ℝ))*vectorNorm d^2+
      (2*j/sqrt (n:ℝ))*vectorNorm d^2)+K*vectorNorm rm :=
        add_le_add (add_le_add (add_le_add h₁ h₂) h₃) (hJ rm)
    _ = (j+K)*vectorNorm rm+(8*j/sqrt (n:ℝ))*vectorNorm d^2 := by ring
    _ ≤ (j+K)*(2*sqrt (∑ i,d i^4))+(8*j/sqrt (n:ℝ))*vectorNorm d^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (magnetization_remainder_norm y d) (add_nonneg hj hK)) le_rfl
    _ = _ := by ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalWhitening
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators MatrixOrder

lemma vectorNorm_sq_dot {n : ℕ} (x : Field n) : vectorNorm x^2=x⬝ᵥx := by
  rw [vectorNorm_sq]
  simp only [vectorSqNorm,dotProduct,pow_two]

lemma gram_energy {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (x : Field n) :
    x⬝ᵥ((Lᵀ*L)*ᵥx)=vectorNorm (L*ᵥx)^2 := by
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,vectorNorm_sq_dot]

lemma regularizedGram_posDef {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    {γ : ℝ} (hγ : 0 < γ) : (Lᵀ*L+γ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hL : (Lᵀ*L).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self L
  exact Matrix.PosDef.posSemidef_add hL (Matrix.PosDef.one.smul hγ)

lemma squareRoot_energy {n : ℕ} (L R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.IsHermitian) (γ : ℝ) (hRR : R*R=Lᵀ*L+γ • 1) (x : Field n) :
    vectorNorm (R*ᵥx)^2=vectorNorm (L*ᵥx)^2+γ*vectorNorm x^2 := by
  have ht : Rᵀ=R := hR.eq
  rw [← gram_energy,ht,hRR,Matrix.add_mulVec,dotProduct_add,gram_energy,
    Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,smul_eq_mul]
  simp only [vectorNorm_sq_dot]

theorem localGaussian_whitening {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U.IsHermitian ∧ IsUnit U.det ∧
      U*(Lᵀ*L+γ • 1)*U=1 ∧
      (∀ g : Field n, vectorNorm (L*ᵥ(U*ᵥg)) ≤ vectorNorm g) ∧
      (∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ) := by
  obtain ⟨R,hR,hRR,hu⟩ := positive_sqrt_data (regularizedGram_posDef L hγ)
  have hi : R⁻¹.IsHermitian := by
    change (R⁻¹)ᵀ=R⁻¹
    rw [Matrix.transpose_nonsing_inv,show Rᵀ=R from hR.eq]
  refine ⟨R⁻¹,hi,?_,?_,?_,?_⟩
  · rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact hu.inv
  · rw [← hRR]
    simp only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hu,Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hu]
  · intro g
    have he := squareRoot_energy L R hR γ hRR (R⁻¹*ᵥg)
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec] at he
    exact (sq_le_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
      (by nlinarith [mul_nonneg hγ.le (sq_nonneg (vectorNorm (R⁻¹*ᵥg)))])
  · intro g
    have he := squareRoot_energy L R hR γ hRR (R⁻¹*ᵥg)
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec] at he
    apply (le_div_iff₀ (sqrt_pos.mpr hγ)).mpr
    apply (sq_le_sq₀ (mul_nonneg (vectorNorm_nonneg _) (sqrt_nonneg _)) (vectorNorm_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt hγ.le]
    nlinarith [sq_nonneg (vectorNorm (L*ᵥ(R⁻¹*ᵥg)))]

lemma symmetric_row_sq_bound {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ c*vectorNorm g) (i : Fin n) :
    ∑ k,U i k^2 ≤ c^2 := by
  let e : Field n := Pi.single i 1
  have he : vectorNorm e=1 := by
    apply (sq_eq_sq₀ (vectorNorm_nonneg _) zero_le_one).mp
    simp [vectorNorm_sq,vectorSqNorm,e,Pi.single_apply]
  have hx : U*ᵥe=fun k => U i k := by
    ext k
    simp only [e,Matrix.mulVec_single,MulOpposite.op_one,one_smul,Matrix.col_apply]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_apply] using congrFun (congrFun hU.eq i) k
  have hh := hbound e
  rw [hx,he,mul_one] at hh
  simpa only [vectorNorm_sq,vectorSqNorm] using
    (sq_le_sq₀ (vectorNorm_nonneg _) hc).mpr hh

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
attribute [local irreducible] vectorNorm varianceAverage varianceLinear magnetizationRemainder tapField fieldJacobian magnetization

lemma vectorNorm_fourth_le {n : ℕ} (d : Field n) :
    vectorNorm d^4 ≤ (n:ℝ)*∑ i,d i^4 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1:ℝ)) (fun i => d i^2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    ← pow_mul] at hc
  rw [show vectorNorm d^4=(vectorNorm d^2)^2 by ring,vectorNorm_sq]
  exact hc

lemma tap_remainder_sq {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y d : Field n) :
    vectorNorm (tapField j J h (y+d)-tapField j J h y-(fieldJacobian j J y)*ᵥd)^2 ≤
      (8*(j+K)^2+128*j^2)*∑ i,d i^4 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 ≤ ∑ i,d i^4 := Finset.sum_nonneg (fun i _ => by positivity)
  have h1 := tap_remainder_norm hn hj hK J hJ h y d
  have ha : 0 ≤ 2*(j+K)*sqrt (∑ i,d i^4) := by positivity
  have hb : 0 ≤ (8*j/sqrt (n:ℝ))*vectorNorm d^2 := by positivity
  have hsq := (sq_le_sq₀ (vectorNorm_nonneg _) (add_nonneg ha hb)).mpr h1
  have hcs : (2*(j+K)*sqrt (∑ i,d i^4)+(8*j/sqrt (n:ℝ))*vectorNorm d^2)^2 ≤
      2*(2*(j+K)*sqrt (∑ i,d i^4))^2+2*((8*j/sqrt (n:ℝ))*vectorNorm d^2)^2 := by
    nlinarith [sq_nonneg (2*(j+K)*sqrt (∑ i,d i^4)-(8*j/sqrt (n:ℝ))*vectorNorm d^2)]
  have he : 2*(2*(j+K)*sqrt (∑ i,d i^4))^2+2*((8*j/sqrt (n:ℝ))*vectorNorm d^2)^2=
      8*(j+K)^2*(∑ i,d i^4)+(128*j^2/(n:ℝ))*vectorNorm d^4 := by
    simp only [mul_pow,div_pow,Real.sq_sqrt hs,Real.sq_sqrt hn0.le]
    ring
  apply (hsq.trans hcs).trans
  rw [he]
  calc
    _ ≤ 8*(j+K)^2*(∑ i,d i^4)+(128*j^2/(n:ℝ))*((n:ℝ)*∑ i,d i^4) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (vectorNorm_fourth_le d) (by positivity))
    _ = _ := by field_simp

lemma varianceAverage_sq_difference {n : ℕ} (hn : 0 < n) (y d : Field n) :
    |varianceAverage (y+d)^2-varianceAverage y^2| ≤ 4/sqrt (n:ℝ)*vectorNorm d := by
  have hb := varianceAverage_bounds hn y
  have hb' := varianceAverage_bounds hn (y+d)
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg hb'.1 hb.1)]
  have hh := varianceAverage_difference hn y d
  calc
    _ ≤ 2*(2/sqrt (n:ℝ)*vectorNorm d) := mul_le_mul
      (show varianceAverage (y+d)+varianceAverage y ≤ 2 by linarith) hh
      (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_LocalGaussianMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal

lemma matrix_fourth_sum_integrable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) :
    Integrable (fun g => ∑ i,((A*ᵥg) i)^4) (gaussianCoordinates κ) := by
  apply integrable_finsetSum
  intro i _
  exact linear_gaussian_fourth_integrable (A i)

lemma matrix_fourth_sum_mean {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) :
    (∫ g,∑ i,((A*ᵥg) i)^4 ∂gaussianCoordinates κ)=3*∑ i,(∑ k,A i k^2)^2 := by
  simp only [Matrix.mulVec,dotProduct]
  rw [integral_finsetSum _ (fun i _ => linear_gaussian_fourth_integrable (A i)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact linear_gaussian_fourth (A i)

lemma matrix_fourth_sum_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i,∑ k,A i k^2 ≤ c) :
    (∫ g,∑ i,((A*ᵥg) i)^4 ∂gaussianCoordinates (Fin m)) ≤ 3*(n:ℝ)*c^2 := by
  rw [matrix_fourth_sum_mean]
  have hs : (∑ i : Fin n,(∑ k,A i k^2)^2) ≤ ∑ _i : Fin n,c^2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (Finset.sum_nonneg (fun k _ => sq_nonneg _)) hc).mpr (hb i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  nlinarith

lemma matrix_norm_fourth_integrable {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    Integrable (fun g => vectorNorm (A*ᵥg)^4) (gaussianCoordinates (Fin m)) := by
  apply ((matrix_fourth_sum_integrable A).const_mul (n:ℝ)).mono' ?_ ?_
  · have he : (fun g => vectorNorm (A*ᵥg)^4)=fun g => (∑ i,((A*ᵥg) i)^2)^2 := by
      funext g
      rw [show vectorNorm (A*ᵥg)^4=(vectorNorm (A*ᵥg)^2)^2 by ring,vectorNorm_sq]
      rfl
    rw [he]
    fun_prop
  · filter_upwards [] with g
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact vectorNorm_fourth_le (A*ᵥg)

lemma matrix_norm_fourth_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i,∑ k,A i k^2 ≤ c) :
    (∫ g,vectorNorm (A*ᵥg)^4 ∂gaussianCoordinates (Fin m)) ≤ 3*(n:ℝ)^2*c^2 := by
  calc
    _ ≤ ∫ g,(n:ℝ)*(∑ i,((A*ᵥg) i)^4) ∂gaussianCoordinates (Fin m) :=
      integral_mono (matrix_norm_fourth_integrable A)
        ((matrix_fourth_sum_integrable A).const_mul _) (fun g => vectorNorm_fourth_le _)
    _ = (n:ℝ)*(∫ g,∑ i,((A*ᵥg) i)^4 ∂gaussianCoordinates (Fin m)) := integral_const_mul _ _
    _ ≤ (n:ℝ)*(3*(n:ℝ)*c^2) := mul_le_mul_of_nonneg_left (matrix_fourth_sum_bound A hc hb) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem localGaussian_fourth_moments {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsHermitian) {γ σ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ) :
    (∫ g,∑ i,((σ • U)*ᵥg) i^4 ∂gaussianCoordinates (Fin n)) ≤ 3*(n:ℝ)*σ^4/γ^2 ∧
    (∫ g,vectorNorm ((σ • U)*ᵥg)^4 ∂gaussianCoordinates (Fin n)) ≤ 3*(n:ℝ)^2*σ^4/γ^2 := by
  have hb (i : Fin n) : ∑ k,(σ • U) i k^2 ≤ σ^2/γ := by
    have hh := symmetric_row_sq_bound hU (inv_nonneg.mpr (sqrt_nonneg γ))
      (fun g => by simpa only [div_eq_mul_inv,mul_comm] using hbound g) i
    rw [inv_pow,Real.sq_sqrt hγ.le] at hh
    simp only [Matrix.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg σ)).trans_eq (by ring)
  have h1 := matrix_fourth_sum_bound (σ • U) (div_nonneg (sq_nonneg σ) hγ.le) hb
  have h2 := matrix_norm_fourth_bound (σ • U) (div_nonneg (sq_nonneg σ) hγ.le) hb
  constructor
  · convert h1 using 1; ring
  · convert h2 using 1; ring

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma gaussian_vectorSqNorm_integrable (n : ℕ) :
    Integrable (vectorSqNorm (n := n)) (gaussianCoordinates (Fin n)) := by
  have hh := (gaussianQuadratic_memLp (fun _ : Fin n => (1:ℝ))).integrable (by norm_num)
  change Integrable (fun g : Field n => ∑ i,1*g i^2) (gaussianCoordinates (Fin n)) at hh
  change Integrable (fun g : Field n => ∑ i,g i^2) (gaussianCoordinates (Fin n))
  simpa only [one_mul] using hh

lemma gaussian_vectorSqNorm_mean (n : ℕ) :
    (∫ g,vectorSqNorm g ∂gaussianCoordinates (Fin n))=(n:ℝ) := by
  simpa only [vectorSqNorm,gaussianQuadratic,one_mul,gaussianCoordinates,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
    gaussianQuadratic_mean (fun _ : Fin n => (1:ℝ))

lemma localGaussianBall_measurable (n : ℕ) : MeasurableSet (localGaussianBall n) := by
  unfold localGaussianBall vectorSqNorm
  exact measurableSet_le (by fun_prop) measurable_const

lemma localGaussianBall_norm {n : ℕ} {g : Field n} (hg : g ∈ localGaussianBall n) :
    vectorNorm g ≤ 2*sqrt (n:ℝ) := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (by positivity)).mp
  rw [vectorNorm_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa only [localGaussianBall,Set.mem_ofPred_eq,show (2:ℝ)^2=4 by norm_num] using hg

theorem localGaussianBall_probability {n : ℕ} (hn : 0 < n) :
    3/4 ≤ (gaussianCoordinates (Fin n)).real (localGaussianBall n) := by
  let μ := gaussianCoordinates (Fin n)
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hh := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (ae_of_all _ (fun g => vectorSqNorm_nonneg g))
    (gaussian_vectorSqNorm_integrable n) (4*(n:ℝ))
  rw [gaussian_vectorSqNorm_mean] at hh
  have hsub : (localGaussianBall n)ᶜ ⊆ {g | 4*(n:ℝ) ≤ vectorSqNorm g} := by
    intro g hg
    change ¬ vectorSqNorm g ≤ 4*(n:ℝ) at hg
    exact (lt_of_not_ge hg).le
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hc := probReal_compl_eq_one_sub (μ := μ) (localGaussianBall_measurable n)
  rw [hc] at hmono
  nlinarith

lemma localGaussianBall_ne_zero {n : ℕ} (hn : 0 < n) :
    gaussianCoordinates (Fin n) (localGaussianBall n) ≠ 0 := by
  intro he
  have hh := localGaussianBall_probability hn
  simp only [measureReal_def,he,ENNReal.toReal_zero] at hh
  norm_num at hh

lemma integrable_cond_of_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {s : Set Ω} {f : Ω → E}
    (hs : μ s ≠ 0) (hf : Integrable f μ) : Integrable f (cond μ s) := by
  exact hf.restrict.smul_measure (ENNReal.inv_ne_top.mpr hs)

lemma integral_cond_nonneg_le_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω} {f : Ω → ℝ}
    (hp : 1/2 ≤ μ.real s)
    (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    (∫ x,f x ∂cond μ s) ≤ 2*∫ x,f x ∂μ := by
  have hps : 0 < μ.real s := by linarith
  have his : 0 ≤ ∫ x in s,f x ∂μ := integral_nonneg_of_ae (ae_restrict_of_ae hn)
  have hsle : (∫ x in s,f x ∂μ) ≤ ∫ x,f x ∂μ :=
    integral_mono_measure μ.restrict_le_self hn hf
  have hinv : (μ.real s)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hps).mpr (by linarith)
  rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv]
  change (μ.real s)⁻¹*(∫ x in s,f x ∂μ) ≤ _
  exact (mul_le_mul_of_nonneg_right hinv his).trans (mul_le_mul_of_nonneg_left hsle (by norm_num))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalVolumeEnergy
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma continuous_vectorNorm (n : ℕ) : Continuous (vectorNorm (n := n)) := by
  unfold vectorNorm
  exact continuous_norm.comp (PiLp.continuous_toLp 2 _)

lemma continuous_tapField {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    Continuous (tapField j J h) := by
  exact continuous_iff_continuousAt.mpr (fun y => (tapField_hasFDerivAt j J h y).continuousAt)

lemma tap_remainder_sq_integrable {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun g => vectorNorm (tapField j J h (y+A*ᵥg)-tapField j J h y-
      (fieldJacobian j J y)*ᵥ(A*ᵥg))^2) (gaussianCoordinates (Fin n)) := by
  apply ((matrix_fourth_sum_integrable A).const_mul (8*(j+K)^2+128*j^2)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact ((continuous_vectorNorm n).comp
      (((continuous_tapField j J h).comp (by fun_prop)).sub continuous_const |>.sub (by fun_prop))).pow 2
  · filter_upwards [] with g
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact tap_remainder_sq hn hj hK J hJ h y (A*ᵥg)

theorem localGaussian_remainder_cond {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsHermitian) {γ σ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ) :
    (∫ g,vectorNorm (tapField j J h (y+(σ • U)*ᵥg)-tapField j J h y-
      (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg))^2
      ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n)) ≤
      6*(8*(j+K)^2+128*j^2)*(n:ℝ)*σ^4/γ^2 := by
  let C := 8*(j+K)^2+128*j^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi := tap_remainder_sq_integrable hn hj hK J hJ h y (σ • U)
  have hp : 1/2 ≤ (gaussianCoordinates (Fin n)).real (localGaussianBall n) :=
    (by norm_num : (1:ℝ)/2 ≤ 3/4).trans (localGaussianBall_probability hn)
  have hc := integral_cond_nonneg_le_two hp hi (ae_of_all _ (fun g => sq_nonneg _))
  have hb : (∫ g,vectorNorm (tapField j J h (y+(σ • U)*ᵥg)-tapField j J h y-
      (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg))^2 ∂gaussianCoordinates (Fin n)) ≤
      C*(3*(n:ℝ)*σ^4/γ^2) := by
    calc
      _ ≤ ∫ g,C*(∑ i,(((σ • U)*ᵥg) i)^4) ∂gaussianCoordinates (Fin n) :=
        integral_mono hi ((matrix_fourth_sum_integrable _).const_mul _)
          (fun g => tap_remainder_sq hn hj hK J hJ h y _)
      _ = C*(∫ g,∑ i,(((σ • U)*ᵥg) i)^4 ∂gaussianCoordinates (Fin n)) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (localGaussian_fourth_moments hU hγ hbound).1 hC
  calc
    _ ≤ 2*(C*(3*(n:ℝ)*σ^4/γ^2)) := hc.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by dsimp [C]; ring

lemma vectorNorm_add_sq_young {n : ℕ} (u v : Field n) {η : ℝ} (hη : 0 < η) :
    vectorNorm (u+v)^2 ≤ (1+η)*vectorNorm u^2+(1+η⁻¹)*vectorNorm v^2 := by
  have hh := (sq_le_sq₀ (vectorNorm_nonneg _) (add_nonneg (vectorNorm_nonneg u)
    (vectorNorm_nonneg v))).mpr (vectorNorm_add_le u v)
  have hy : 2*vectorNorm u*vectorNorm v ≤ η*vectorNorm u^2+η⁻¹*vectorNorm v^2 := by
    apply (mul_le_mul_iff_right₀ hη).mp
    have he : η⁻¹*η=1 := inv_mul_cancel₀ hη.ne'
    nlinarith [sq_nonneg (η*vectorNorm u-vectorNorm v)]
  nlinarith

theorem local_energy_pointwise {n : ℕ} (u v R g : Field n) {σ η ρ : ℝ}
    (hσ : 0 < σ) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (hu : vectorNorm u ≤ ρ*sqrt (n:ℝ))
    (hv : vectorNorm v ≤ σ*vectorNorm g) (hg : g ∈ localGaussianBall n) :
    vectorNorm g^2/2-vectorNorm (u+v+R)^2/(2*σ^2) ≥
      -2*η*(n:ℝ)-(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2)/σ^2 := by
  have hsσ : 0 < σ^2 := sq_pos_of_pos hσ
  have hu2 := (sq_le_sq₀ (vectorNorm_nonneg u) (by positivity)).mpr hu
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hu2
  have hv2 := (sq_le_sq₀ (vectorNorm_nonneg v) (mul_nonneg hσ.le (vectorNorm_nonneg g))).mpr hv
  rw [mul_pow] at hv2
  have hUR := vectorNorm_add_sq_young u R (η := 1) (by norm_num)
  norm_num only [inv_one,one_add_one_eq_two] at hUR
  have hh := vectorNorm_add_sq_young v (u+R) hη
  have he : v+(u+R)=u+v+R := by abel
  rw [he] at hh
  have hpos : 0 ≤ 1+η⁻¹ := by positivity
  have hcombine : vectorNorm (u+v+R)^2 ≤ (1+η)*σ^2*vectorNorm g^2+
      2*(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2) := by
    calc
      _ ≤ (1+η)*vectorNorm v^2+(1+η⁻¹)*(2*vectorNorm u^2+2*vectorNorm R^2) :=
        hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hUR hpos))
      _ ≤ (1+η)*(σ^2*vectorNorm g^2)+(1+η⁻¹)*(2*(ρ^2*(n:ℝ))+2*vectorNorm R^2) :=
        add_le_add (mul_le_mul_of_nonneg_left hv2 (by positivity))
          (mul_le_mul_of_nonneg_left (by linarith) hpos)
      _ = _ := by ring
  have hgn : vectorNorm g^2 ≤ 4*(n:ℝ) := by rw [vectorNorm_sq]; exact hg
  apply (mul_le_mul_iff_right₀ hsσ).mp
  have he1 : (-2*η*(n:ℝ)-(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2)/σ^2)*σ^2=
      -2*η*(n:ℝ)*σ^2-(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2) := by
    rw [sub_mul,div_mul_cancel₀ _ hsσ.ne']
  have he2 : (vectorNorm g^2/2-vectorNorm (u+v+R)^2/(2*σ^2))*σ^2=
      (σ^2*vectorNorm g^2-vectorNorm (u+v+R)^2)/2 := by
    field_simp
  rw [mul_comm (σ^2) _,mul_comm (σ^2) _,he1,he2]
  nlinarith [mul_le_mul_of_nonneg_left hgn (mul_nonneg hη.le hsσ.le)]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma localGaussianBall_compact (n : ℕ) : IsCompact (localGaussianBall n) := by
  apply (isCompact_Icc : IsCompact (Icc (fun _ : Fin n => -2*sqrt (n:ℝ)) (fun _ : Fin n => 2*sqrt (n:ℝ)))).of_isClosed_subset
  · apply isClosed_le _ continuous_const
    unfold vectorSqNorm
    fun_prop
  · intro g hg
    have hb := localGaussianBall_norm hg
    have hc (i : Fin n) : |g i| ≤ 2*sqrt (n:ℝ) := by
      have hh := PiLp.norm_apply_le (WithLp.toLp 2 g) i
      exact (show |g i| ≤ vectorNorm g by simpa only [Real.norm_eq_abs,vectorNorm] using hh).trans hb
    exact ⟨fun i => by simpa only [neg_mul] using (abs_le.mp (hc i)).1,fun i => (abs_le.mp (hc i)).2⟩

lemma localGaussian_cond_integrable {n : ℕ} (hn : 0 < n) {f : Field n → ℝ}
    (hf : Continuous f) : Integrable f (cond (gaussianCoordinates (Fin n)) (localGaussianBall n)) := by
  exact (hf.continuousOn.integrableOn_compact (localGaussianBall_compact n)).smul_measure
    (ENNReal.inv_ne_top.mpr (localGaussianBall_ne_zero hn))

lemma localExponent_continuous {n : ℕ} (j σ : ℝ) (J U : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    Continuous (localExponent j σ J U h y) := by
  have hb : Continuous (varianceAverage (n := n)) := by
    unfold varianceAverage
    exact continuous_const.sub (continuous_iff_continuousAt.mpr (fun y => (overlap_hasFDerivAt y).continuousAt))
  exact (((continuous_vectorNorm n).pow 2 |>.div_const 2).sub
    (((continuous_vectorNorm n).comp ((continuous_tapField j J h).comp (by fun_prop))).pow 2 |>.div_const _)).add
      (((hb.comp (by fun_prop)).pow 2 |>.const_mul ((n:ℝ)*j)).div_const 2)

lemma localGaussian_displacement {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ} {γ σ : ℝ}
    (_hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ)
    {g : Field n} (hg : g ∈ localGaussianBall n) :
    vectorNorm ((σ • U)*ᵥg) ≤ (2*σ/sqrt γ)*sqrt (n:ℝ) := by
  rw [Matrix.smul_mulVec]
  change vectorNorm (fun i => σ*(U*ᵥg) i) ≤ _
  rw [vectorNorm_smul,abs_of_nonneg hσ]
  calc
    _ ≤ σ*(vectorNorm g/sqrt γ) := mul_le_mul_of_nonneg_left (hbound g) hσ
    _ ≤ σ*((2*sqrt (n:ℝ))/sqrt γ) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (localGaussianBall_norm hg) (sqrt_nonneg _)) hσ
    _ = _ := by ring

lemma localGaussian_variance_change {n : ℕ} (hn : 0 < n) (y : Field n)
    {U : Matrix (Fin n) (Fin n) ℝ} {γ σ : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ)
    {g : Field n} (hg : g ∈ localGaussianBall n) :
    |varianceAverage (y+(σ • U)*ᵥg)^2-varianceAverage y^2| ≤ 8*σ/sqrt γ := by
  have hn0 : sqrt (n:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ 4/sqrt (n:ℝ)*vectorNorm ((σ • U)*ᵥg) := varianceAverage_sq_difference hn y _
    _ ≤ 4/sqrt (n:ℝ)*((2*σ/sqrt γ)*sqrt (n:ℝ)) := mul_le_mul_of_nonneg_left
      (localGaussian_displacement hγ hσ hbound hg) (by positivity)
    _ = _ := by field_simp; ring

theorem localGaussian_exponent_bound {n : ℕ} (hn : 0 < n) {j K γ σ η ρ : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (hγ : 0 < γ) (hσ : 0 < σ) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (J U : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    (hU : U.IsHermitian)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ)
    (hlin : ∀ g : Field n, vectorNorm ((fieldJacobian j J y)*ᵥ(U*ᵥg)) ≤ vectorNorm g)
    (hres : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ)) :
    (n:ℝ)*(j*varianceAverage y^2/2-2*η-
      (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)-4*j*σ/sqrt γ) ≤
      ∫ g,localExponent j σ J U h y g
        ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n) := by
  let μ := cond (gaussianCoordinates (Fin n)) (localGaussianBall n)
  let : IsProbabilityMeasure μ := cond_isProbabilityMeasure (localGaussianBall_ne_zero hn)
  let R : Field n → Field n := fun g => tapField j J h (y+(σ • U)*ᵥg)-tapField j J h y-
    (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg)
  have hiR : Integrable (fun g => vectorNorm (R g)^2) μ :=
    integrable_cond_of_integrable (localGaussianBall_ne_zero hn)
      (tap_remainder_sq_integrable hn hj hK J hJ h y _)
  have hR := localGaussian_remainder_cond hn hj hK J hJ h y hU hγ hbound (σ := σ)
  change (∫ g,vectorNorm (R g)^2 ∂μ) ≤ _ at hR
  let f : Field n → ℝ := fun g => (n:ℝ)*j*varianceAverage y^2/2-2*η*(n:ℝ)-
    (1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm (R g)^2)/σ^2-4*(n:ℝ)*j*σ/sqrt γ
  have hif : Integrable f μ := by
    exact (((integrable_const _).sub (integrable_const _)).sub
      (((integrable_const _).add hiR).const_mul _ |>.div_const _)).sub (integrable_const _)
  have hmono : (∫ g,f g ∂μ) ≤ ∫ g,localExponent j σ J U h y g ∂μ := by
    apply integral_mono_ae hif (localGaussian_cond_integrable hn (localExponent_continuous _ _ _ _ _ _))
    apply ae_cond_of_forall_mem (localGaussianBall_measurable n)
    intro g hg
    let v := (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg)
    have hv : vectorNorm v ≤ σ*vectorNorm g := by
      dsimp [v]
      rw [Matrix.smul_mulVec,Matrix.mulVec_smul]
      change vectorNorm (fun i => σ*((fieldJacobian j J y)*ᵥ(U*ᵥg)) i) ≤ _
      rw [vectorNorm_smul,abs_of_pos hσ]
      exact mul_le_mul_of_nonneg_left (hlin g) hσ.le
    have hh := local_energy_pointwise (tapField j J h y) v (R g) g hσ hη hρ hres hv hg
    have he : tapField j J h y+v+R g=tapField j J h (y+(σ • U)*ᵥg) := by dsimp [v,R]; abel
    rw [he] at hh
    have hb := (abs_le.mp (localGaussian_variance_change hn y hγ hσ.le hbound hg)).1
    have hbj := mul_le_mul_of_nonneg_left hb (show 0 ≤ (n:ℝ)*j/2 by positivity)
    dsimp [f,localExponent]
    ring_nf at hh hbj ⊢
    linarith only [hh,hbj]
  have he : (∫ g,f g ∂μ)=(n:ℝ)*j*varianceAverage y^2/2-2*η*(n:ℝ)-
      (1+η⁻¹)*(ρ^2*(n:ℝ)+∫ g,vectorNorm (R g)^2 ∂μ)/σ^2-4*(n:ℝ)*j*σ/sqrt γ := by
    have hfEq : f=fun g => ((n:ℝ)*j*varianceAverage y^2/2-2*η*(n:ℝ)-
        (1+η⁻¹)*ρ^2*(n:ℝ)/σ^2-4*(n:ℝ)*j*σ/sqrt γ)-
        ((1+η⁻¹)/σ^2)*vectorNorm (R g)^2 := by
      funext g
      dsimp [f]
      ring
    rw [hfEq,integral_sub (integrable_const _) (hiR.const_mul _),integral_const_mul]
    simp only [integral_const,probReal_univ,one_smul]
    ring
  rw [he] at hmono
  apply le_trans ?_ hmono
  have hh := mul_le_mul_of_nonneg_left hR (show 0 ≤ (1+η⁻¹)/σ^2 by positivity)
  have hsσ : σ ≠ 0 := hσ.ne'
  have heq : (1+η⁻¹)*(ρ^2*(n:ℝ)+6*(8*(j+K)^2+128*j^2)*(n:ℝ)*σ^4/γ^2)/σ^2=
      (n:ℝ)*(1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2) := by
    field_simp
  ring_nf at hh heq ⊢
  linarith only [hh,heq]

theorem localGaussian_jensen {n : ℕ} (hn : 0 < n) (j σ : ℝ)
    (J U : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    exp (∫ g,localExponent j σ J U h y g ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n)) ≤
      ∫ g,exp (localExponent j σ J U h y g) ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n) := by
  let := cond_isProbabilityMeasure (localGaussianBall_ne_zero hn)
  exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => mem_univ _))
    (localGaussian_cond_integrable hn (localExponent_continuous _ _ _ _ _ _))
    (localGaussian_cond_integrable hn (continuous_exp.comp (localExponent_continuous _ _ _ _ _ _)))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalVolumeChange
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma map_affine_matrix_volume {n : ℕ} (y : Field n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) :
    Measure.map (fun g : Field n => y+A*ᵥg) volume = ENNReal.ofReal |A.det⁻¹| • volume := by
  have he : (fun g : Field n => y+A*ᵥg) = (fun z => y+z) ∘ (fun g => A*ᵥg) := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop)]
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hA
  change Measure.map (fun g => A*ᵥg) volume=_ at hm
  rw [hm,Measure.map_smul,map_add_left_eq_self]

lemma affine_set_lintegral_le {n : ℕ} (y : Field n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) {B E : Set (Field n)} (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hBE : ∀ g ∈ B,y+A*ᵥg ∈ E) (f : Field n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g in B,f (y+A*ᵥg)) ≤ ENNReal.ofReal |A.det⁻¹| * ∫⁻ z in E,f z := by
  calc
    _ = ∫⁻ g,(B.indicator (fun g => f (y+A*ᵥg))) g := (lintegral_indicator hB _).symm
    _ ≤ ∫⁻ g,(E.indicator f) (y+A*ᵥg) := by
      apply lintegral_mono
      intro g
      by_cases hg : g ∈ B
      · simp only [indicator_of_mem hg, indicator_of_mem (hBE g hg),le_refl]
      · rw [indicator_of_notMem hg]
        exact bot_le
    _ = ∫⁻ z,E.indicator f z ∂Measure.map (fun g : Field n => y+A*ᵥg) volume :=
      (lintegral_map (hf.indicator hE) (by fun_prop)).symm
    _ = _ := by rw [map_affine_matrix_volume y A hA,lintegral_smul_measure,lintegral_indicator hE]; rfl

lemma gaussian_standard_density {n : ℕ} : gaussianCoordinates (Fin n) =
    (volume : Measure (Field n)).withDensity (fun g =>
      ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^(n:ℕ)*exp (-vectorNorm g^2/2))) := by
  rw [gaussianCoordinates,GaussianDensity.pi_gaussian_density (hv := fun _ => one_ne_zero)]
  congr 1
  funext g
  congr 1
  simp only [gaussianPDFReal,sub_zero,NNReal.coe_one,mul_one,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,← exp_sum,← Finset.sum_div,
    ← Finset.sum_neg_distrib,vectorNorm_sq,vectorSqNorm]

lemma gaussian_tilt_cancellation {n : ℕ} {B : Set (Field n)} (hB : MeasurableSet B)
    (φ : Field n → ℝ) (hφ : Measurable φ) :
    (∫⁻ g in B,ENNReal.ofReal (exp (vectorNorm g^2/2+φ g)) ∂gaussianCoordinates (Fin n)) =
    ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n) * ∫⁻ g in B,ENNReal.ofReal (exp (φ g)) := by
  have hnorm : Measurable (vectorNorm (n := n)) := (continuous_vectorNorm n).measurable
  rw [gaussian_standard_density,restrict_withDensity hB,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have he (g : Field n) :
      ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n*exp (-vectorNorm g^2/2)) *
        ENNReal.ofReal (exp (vectorNorm g^2/2+φ g)) =
      ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n) * ENNReal.ofReal (exp (φ g)) := by
    rw [← ENNReal.ofReal_mul (by positivity),mul_assoc,← exp_add]
    have hh : -vectorNorm g^2/2+(vectorNorm g^2/2+φ g)=φ g := by ring
    rw [hh,ENNReal.ofReal_mul (by positivity)]
  simp_rw [Pi.mul_apply,he]
  exact lintegral_const_mul _ (by fun_prop)

theorem local_volume_change_of_variables {n : ℕ} (y : Field n)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.det ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    {B E : Set (Field n)} (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hBE : ∀ g ∈ B,y+(σ • U)*ᵥg ∈ E) (φ : Field n → ℝ) (hφ : Measurable φ) :
    ENNReal.ofReal |U.det| *
      (∫⁻ g in B,ENNReal.ofReal (exp (vectorNorm g^2/2+φ (y+(σ • U)*ᵥg)))
        ∂gaussianCoordinates (Fin n)) ≤
    ENNReal.ofReal (((sqrt (2*Real.pi)*σ)⁻¹)^n) * ∫⁻ z in E,ENNReal.ofReal (exp (φ z)) := by
  have hA : (σ • U).det ≠ 0 := by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hσ.ne') hU
  rw [gaussian_tilt_cancellation hB (fun g => φ (y+(σ • U)*ᵥg)) (hφ.comp (by fun_prop))]
  have hh := affine_set_lintegral_le y (σ • U) hA hB hE hBE (fun z => ENNReal.ofReal (exp (φ z))) (by fun_prop)
  calc
    _ ≤ ENNReal.ofReal |U.det| * (ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n)*
        (ENNReal.ofReal |(σ • U).det⁻¹| * ∫⁻ z in E,ENNReal.ofReal (exp (φ z)))) := by gcongr
    _ = _ := by
      rw [← mul_assoc,← mul_assoc,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Matrix.det_smul,Fintype.card_fin,abs_inv,abs_mul,abs_pow,abs_of_pos hσ,mul_inv]
      have hUd : |U.det| ≠ 0 := abs_ne_zero.mpr hU
      rw [mul_inv,mul_pow]
      simp only [← inv_pow]
      field_simp

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma conditional_lintegral_identity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B : Set Ω} (hB : μ B ≠ 0) (f : Ω → ℝ≥0∞) :
    μ B*(∫⁻ x,f x ∂cond μ B)=∫⁻ x in B,f x ∂μ := by
  rw [ProbabilityTheory.cond,lintegral_smul_measure]
  change μ B*((μ B)⁻¹*(∫⁻ x in B,f x ∂μ))=_
  rw [← mul_assoc,ENNReal.mul_inv_cancel hB (measure_ne_top _ _),one_mul]

lemma whitening_logdet {n : ℕ} (U Q : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.det ≠ 0) (hQ : 0 < Q.det) (he : U*Q*U=1) :
    log |U.det| = -log Q.det/2 := by
  have hd : |U.det|^2*Q.det=1 := by
    have hh := congrArg Matrix.det he
    rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_one] at hh
    rw [sq_abs]
    nlinarith only [hh]
  have hh := congrArg log hd
  rw [log_mul (pow_ne_zero _ (abs_ne_zero.mpr hU)) hQ.ne',log_pow,log_one] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma localAction_continuous {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) : Continuous (localAction j σ J h) := by
  have hb : Continuous (varianceAverage (n := n)) := by
    unfold varianceAverage
    exact continuous_const.sub (continuous_iff_continuousAt.mpr (fun y => (overlap_hasFDerivAt y).continuousAt))
  exact (((continuous_vectorNorm n).comp (continuous_tapField j J h)).pow 2 |>.neg |>.div_const _).add
    ((hb.pow 2 |>.const_mul _).div_const _)

theorem local_volume_quantitative {n : ℕ} (hn : 0 < n) {j K γ σ η ρ r ε₁ : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (hγ : 0 < γ) (hσ : 0 < σ) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    {E : Set (Field n)} (hE : MeasurableSet E)
    (hball : ∀ d : Field n,vectorNorm d ≤ r*sqrt (n:ℝ) → y+d ∈ E)
    (hsmall : 2*σ/sqrt γ ≤ r)
    (hdet : log ((fieldJacobian j J y)ᵀ*(fieldJacobian j J y)+γ • 1).det ≤
      (n:ℝ)*(j*varianceAverage y^2+ε₁))
    (hres : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ)) :
    ENNReal.ofReal ((3/4:ℝ)*exp (-(n:ℝ)*(ε₁/2+2*η+
      (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ))) ≤
      localVolume j σ J h E := by
  let L := fieldJacobian j J y
  let Q := Lᵀ*L+γ • (1 : Matrix (Fin n) (Fin n) ℝ)
  obtain ⟨U,hUH,hUd,hUQ,hlin,hbound⟩ := localGaussian_whitening L hγ
  have hU : U.det ≠ 0 := isUnit_iff_ne_zero.mp hUd
  have hQ : 0 < Q.det := (regularizedGram_posDef L hγ).det_pos
  have hlog := whitening_logdet U Q hU hQ hUQ
  let μ := gaussianCoordinates (Fin n)
  let B := localGaussianBall n
  let l : ℝ := j*varianceAverage y^2/2-2*η-
    (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)-4*j*σ/sqrt γ
  have hjensen : exp ((n:ℝ)*l) ≤ ∫ g,exp (localExponent j σ J U h y g) ∂cond μ B := by
    exact (exp_le_exp.mpr (localGaussian_exponent_bound hn hj hK hγ hσ hη hρ
      J U hJ h y hUH hbound hlin hres)).trans (localGaussian_jensen hn j σ J U h y)
  have hp : ENNReal.ofReal (3/4:ℝ) ≤ μ B := by
    have hh := ENNReal.ofReal_le_ofReal (localGaussianBall_probability hn)
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
  have hcond : ENNReal.ofReal (exp ((n:ℝ)*l)) ≤
      ∫⁻ g,ENNReal.ofReal (exp (localExponent j σ J U h y g)) ∂cond μ B := by
    have hi : Integrable (fun g => exp (localExponent j σ J U h y g)) (cond μ B) :=
      localGaussian_cond_integrable hn (continuous_exp.comp (localExponent_continuous _ _ _ _ _ _))
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => (exp_pos _).le))]
    exact ENNReal.ofReal_le_ofReal hjensen
  have hvol := local_volume_change_of_variables y U hU hσ (localGaussianBall_measurable n) hE
    (fun g hg => hball _ ((localGaussian_displacement hγ hσ.le hbound hg).trans
      (mul_le_mul_of_nonneg_right hsmall (sqrt_nonneg _))))
    (localAction j σ J h) (localAction_continuous _ _ _ _).measurable
  have hexp (g : Field n) : vectorNorm g^2/2+localAction j σ J h (y+(σ • U)*ᵥg)=
      localExponent j σ J U h y g := by unfold localAction localExponent; ring
  simp_rw [hexp] at hvol
  change ENNReal.ofReal |U.det| *(∫⁻ g in B,ENNReal.ofReal (exp (localExponent j σ J U h y g)) ∂μ) ≤
    localVolume j σ J h E at hvol
  rw [← conditional_lintegral_identity (localGaussianBall_ne_zero hn)] at hvol
  have hscalar : (3/4:ℝ)*exp (-(n:ℝ)*(ε₁/2+2*η+
      (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ)) ≤
      |U.det| *((3/4:ℝ)*exp ((n:ℝ)*l)) := by
    rw [← exp_log (abs_pos.mpr hU)]
    calc
      _ ≤ (3/4:ℝ)*exp (log |U.det|+(n:ℝ)*l) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        rw [hlog]
        change log Q.det ≤ _ at hdet
        dsimp [l]
        linarith only [hdet]
      _ = _ := by rw [exp_add]; ring
  calc
    _ ≤ ENNReal.ofReal (|U.det| *((3/4:ℝ)*exp ((n:ℝ)*l))) := ENNReal.ofReal_le_ofReal hscalar
    _ = ENNReal.ofReal |U.det| *(ENNReal.ofReal (3/4:ℝ)*ENNReal.ofReal (exp ((n:ℝ)*l))) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal |U.det| *(μ B*(∫⁻ g,ENNReal.ofReal (exp (localExponent j σ J U h y g)) ∂cond μ B)) := by
      gcongr
    _ ≤ _ := hvol

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldIntegralReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal
attribute [local fun_prop] continuous_radialDensity

lemma continuous_fieldMollifier {n : ℕ} (j σ : ℝ) :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × (Fin n → ℝ))=>
      fieldMollifier j σ p.1 p.2.1 p.2.2) := by
  unfold fieldMollifier tapField onsager overlap magnetization
  exact ((continuous_radialDensity σ).comp (by fun_prop)).mul (by fun_prop)

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators ENNReal

lemma fieldMollifier_eq_localAction {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : fieldMollifier j σ J h y=
      ((sqrt (2*Real.pi)*σ)⁻¹)^n*exp (localAction j σ J h y) := by
  unfold fieldMollifier radialDensity localAction varianceAverage
  rw [Fintype.card_fin,vectorNorm_sq,mul_assoc,← exp_add]
  simp only [vectorSqNorm,dotProduct,pow_two]

lemma fieldIntegral_eq_localVolume {n : ℕ} {σ : ℝ} (hσ : 0 < σ) (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (E : Set (Field n)) :
    fieldIntegral j σ J h E=localVolume j σ J h E := by
  unfold fieldIntegral localVolume
  simp_rw [fieldMollifier_eq_localAction,ENNReal.ofReal_mul (by positivity : 0 ≤ ((sqrt (2*Real.pi)*σ)⁻¹)^n)]
  exact lintegral_const_mul _ (Real.measurable_exp.comp (localAction_continuous j σ J h).measurable |>.ennreal_ofReal)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldTonelli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma fieldIntegral_indicator {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    fieldIntegral j σ J h E=∫⁻ y, ENNReal.ofReal (fieldMollifier j σ J h y)*E.indicator (fun _=>1) y := by
  rw [fieldIntegral,← lintegral_indicator hE]
  apply lintegral_congr
  intro y
  by_cases hy : y∈E <;> simp [hy]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalVolumeFull
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set Filter
open scoped BigOperators ENNReal NNReal

lemma nonnegative_continuous_small {f : ℝ → ℝ} (hf : ContinuousAt f 0) (hzero : f 0=0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ,0 < δ ∧ ∀ x : ℝ,0 ≤ x → x < δ → f x < ε := by
  have hh : ∀ᶠ x in nhds (0:ℝ), f x < ε :=
    hf.tendsto.eventually_lt_const (by rw [hzero]; exact hε)
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨δ,hδ,fun x hx hxd => hnear ?_⟩
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hx] using hxd

lemma absorb_three_quarters_exp {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ,N ≤ n →
      exp (-ε*(n:ℝ)) ≤ (3/4:ℝ)*exp (-(3*ε/4)*(n:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (4/ε)
  refine ⟨max N 1,by omega,?_⟩
  intro n hn
  have hnn : 4/ε ≤ (n:ℝ) := hN.trans (by exact_mod_cast (le_trans (le_max_left N 1) hn))
  have hx : 1 ≤ ε*(n:ℝ)/4 := by
    have hh := (div_le_iff₀ hε).mp hnn
    nlinarith
  have he : exp (-(ε*(n:ℝ)/4)) ≤ 3/4 := by
    rw [exp_neg,inv_eq_one_div,div_le_iff₀ (exp_pos _)]
    have hh := add_one_le_exp (ε*(n:ℝ)/4)
    nlinarith only [hh,hx]
  have hsplit : -ε*(n:ℝ)=-(ε*(n:ℝ)/4)+(-(3*ε/4)*(n:ℝ)) := by ring
  rw [hsplit,exp_add]
  exact mul_le_mul_of_nonneg_right he (exp_pos _).le

theorem local_volume_uniform {j K r ε : ℝ} (hj : 0 ≤ j) (hK : 0 ≤ K)
    (hr : 0 < r) (hε : 0 < ε) :
    ∃ ε₁ : ℝ,0 < ε₁ ∧ ∀ γ : ℝ,0 < γ →
    ∃ σ₀ : ℝ,0 < σ₀ ∧ ∀ σ : ℝ,0 < σ → σ < σ₀ →
    ∃ ρ : ℝ,0 < ρ ∧ ∃ N : ℕ,0 < N ∧ ∀ n,N ≤ n →
    ∀ J : Matrix (Fin n) (Fin n) ℝ,
    (∀ z : Field n,vectorNorm (J*ᵥz) ≤ K*vectorNorm z) →
    ∀ h y : Field n,∀ E : Set (Field n),MeasurableSet E →
    (∀ d : Field n,vectorNorm d ≤ r*sqrt (n:ℝ) → y+d ∈ E) →
    log ((fieldJacobian j J y)ᵀ*(fieldJacobian j J y)+γ • 1).det ≤
      (n:ℝ)*(j*varianceAverage y^2+ε₁) →
    vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ) →
    ENNReal.ofReal (exp (-ε*(n:ℝ))) ≤ localVolume j σ J h E := by
  let η := ε/16
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨ε/4,by positivity,?_⟩
  intro γ hγ
  let noise : ℝ → ℝ := fun σ => (1+η⁻¹)*(6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ
  have hncont : ContinuousAt noise 0 := by dsimp [noise]; fun_prop
  have hnzero : noise 0=0 := by simp [noise]
  obtain ⟨a,ha,hasmall⟩ := nonnegative_continuous_small hncont hnzero (show 0 < ε/4 by positivity)
  refine ⟨min a (r*sqrt γ/2),lt_min ha (by positivity),?_⟩
  intro σ hσ hσ₀
  have hsnoise : noise σ < ε/4 := hasmall σ hσ.le (lt_of_lt_of_le hσ₀ (min_le_left _ _))
  have hsr : 2*σ/sqrt γ ≤ r := by
    apply (div_le_iff₀ (sqrt_pos.mpr hγ)).mpr
    have hh := lt_of_lt_of_le hσ₀ (min_le_right _ _)
    linarith
  let residual : ℝ → ℝ := fun ρ => (1+η⁻¹)*ρ^2/σ^2
  have hrcont : ContinuousAt residual 0 := by dsimp [residual]; fun_prop
  have hrzero : residual 0=0 := by simp [residual]
  obtain ⟨b,hb,hbsmall⟩ := nonnegative_continuous_small hrcont hrzero (show 0 < ε/4 by positivity)
  obtain ⟨N,hN,habsorb⟩ := absorb_three_quarters_exp hε
  refine ⟨b/2,by positivity,N,hN,?_⟩
  intro n hn J hJ h y E hE hball hdet hres
  have hresmall : residual (b/2) < ε/4 := hbsmall _ (by positivity) (by linarith)
  have hloss : (ε/4)/2+2*η+
      (1+η⁻¹)*((b/2)^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ ≤ 3*ε/4 := by
    dsimp [noise] at hsnoise
    dsimp [residual] at hresmall
    dsimp [η] at *
    ring_nf at hsnoise hresmall ⊢
    linarith only [hsnoise,hresmall]
  have hnn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ ENNReal.ofReal ((3/4:ℝ)*exp (-(3*ε/4)*(n:ℝ))) :=
      ENNReal.ofReal_le_ofReal (habsorb n hn)
    _ ≤ ENNReal.ofReal ((3/4:ℝ)*exp (-(n:ℝ)*((ε/4)/2+2*η+
      (1+η⁻¹)*((b/2)^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
      nlinarith only [mul_le_mul_of_nonneg_left hloss hnn]
    _ ≤ _ := local_volume_quantitative (hN.trans_le hn) hj hK hγ hσ hη (by positivity)
      J hJ h y hE hball hsr hdet hres

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldIntegralMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma measurable_fieldIntegral {n : ℕ} (j t σ : ℝ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (hE : MeasurableSet E) :
    Measurable (fun p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)=>
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
        (fun i=>t+p.2 i) {y | ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E}) := by
  let H : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ≥0∞ :=
    fun p=>ENNReal.ofReal (fieldMollifier j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1))
      (fun i=>t+p.1.2 i) p.2)* E.indicator (fun _=>1) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)
  have hsJ : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1)) :=
    ((goeMatrix_pi_lipschitz (j/(n:ℝ))).continuous.comp (continuous_fst.comp continuous_fst)).add continuous_const
  have htime : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (fun i=>t+p.1.2 i)) := by
    apply continuous_pi
    intro i
    exact continuous_const.add ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
  have hmap : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1),((fun i=>t+p.1.2 i),p.2))) :=
    hsJ.prodMk (htime.prodMk continuous_snd)
  have hφ := ((continuous_fieldMollifier j σ).comp hmap).measurable.ennreal_ofReal
  have hI : Measurable (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      E.indicator (fun _=>(1 : ℝ≥0∞)) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)) := by
    apply (measurable_const.indicator hE).comp
    unfold goeMatrix
    fun_prop
  have hH : Measurable H := hφ.mul hI
  have he (p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) :
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
        (fun i=>t+p.2 i) {y | ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E}=
      ∫⁻ y,H (p,y) := by
    have hs : MeasurableSet {y : Fin n → ℝ | ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E} := hE.preimage (by fun_prop)
    erw [fieldIntegral_indicator _ _ _ _ _ hs]
    apply lintegral_congr
    intro y
    dsimp [H]
    by_cases hy : ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E <;> simp [hy]
  simp_rw [he]
  exact hH.lintegral_prod_right'

lemma measurable_fieldIntegral_cylinder {n : ℕ} (j t σ : ℝ)
    (E : Set (Field n)) (hE : MeasurableSet E) :
    Measurable (fun p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)=>
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
        (fun i=>t+p.2 i) E) := by
  simpa only [mem_prod,mem_univ,true_and,ofPred_mem_eq] using
    measurable_fieldIntegral j t σ (Set.univ ×ˢ E) (MeasurableSet.univ.prod hE)

lemma measureReal_union_detector {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E D : Set Ω) (F : Ω → ℝ≥0∞)
    (b p q : ℝ) (hbD : μ.real D ≤ p)
    (hbF : μ.real {x | ENNReal.ofReal b ≤ F x} ≤ q)
    (hdet : ∀ x ∈ E, x∉D → ENNReal.ofReal b ≤ F x) : μ.real E ≤ p+q := by
  apply (measureReal_mono (s₂ := D ∪ {x | ENNReal.ofReal b ≤ F x}) ?_ (measure_ne_top _ _)).trans
  · exact (measureReal_union_le _ _).trans (add_le_add hbD hbF)
  · intro x hx
    by_cases hd : x∈D
    · exact Or.inl hd
    · exact Or.inr (hdet x hx hd)

lemma markov_exponential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F : Ω → ℝ≥0∞} (hF : Measurable F) {a b d : ℝ}
    (hb : ∫⁻ x,F x ∂μ ≤ ENNReal.ofReal (exp (-a*d))) :
    μ.real {x | ENNReal.ofReal (exp (-b*d)) ≤ F x} ≤ exp (-(a-b)*d) := by
  have hm := meas_ge_le_lintegral_div (μ := μ) (ε := ENNReal.ofReal (exp (-b*d))) hF.aemeasurable
    (ENNReal.ofReal_pos.mpr (exp_pos _)).ne' ENNReal.ofReal_ne_top
  have he : ENNReal.ofReal (exp (-a*d))/ENNReal.ofReal (exp (-b*d))=
      ENNReal.ofReal (exp (-(a-b)*d)) := by
    rw [← ENNReal.ofReal_div_of_pos (exp_pos _),← exp_sub]
    congr 2
    ring
  have hx := hm.trans ((ENNReal.div_le_div_right hb _).trans_eq he)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq (ENNReal.toReal_ofReal (exp_pos _).le)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SmallOverlap
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

lemma quadraticForm_le_mulvec_bound {n : ℕ} {K : ℝ} (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n,vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (x : Field n) :
    quadraticForm J x ≤ K*vectorSqNorm x := by
  have he : quadraticForm J x=∑ i,x i*(J*ᵥx) i := by
    simp only [quadraticForm,mulVec,dotProduct,Finset.mul_sum,mul_assoc]
  rw [he]
  calc
    _ ≤ |∑ i,x i*(J*ᵥx) i| := le_abs_self _
    _ ≤ vectorNorm x*vectorNorm (J*ᵥx) := vector_dot_abs_le _ _
    _ ≤ vectorNorm x*(K*vectorNorm x) := mul_le_mul_of_nonneg_left (hJ x) (vectorNorm_nonneg _)
    _ = _ := by rw [← vectorNorm_sq];ring

lemma badField_small_overlap_impossible {n : ℕ} (hn : 0 < n) {j A K q₀ ε c : ℝ}
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hK : 0 ≤ K-j)
    (hmargin : c < 1-A*(K-j+6*j*q₀))
    (W : Matrix (Fin n) (Fin n) ℝ) (y : Field n)
    (hJ : ∀ z : Field n,vectorNorm (plantedInteraction j W*ᵥz) ≤ K*vectorNorm z)
    (hy : (W,y)∈badFieldSet n j A ε c) : 2*q₀ < overlap y := by
  by_contra! hq
  obtain ⟨a,ha,_hclose,x,hx,hquad⟩ := hy
  have hv : vectorSqNorm x.ofLp=1 := by
    rw [← vectorNorm_sq]
    change ‖WithLp.toLp 2 x.ofLp‖^2=1
    simp only [WithLp.toLp_ofLp,hx,one_pow]
  have hcoef : 0 ≤ K-j+3*j*overlap y := add_nonneg hK (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hj) (overlap_nonneg y))
  have hh := hessian_lower_bound hn hj y a (fun i=>(ha i).1) (fun i=>(ha i).2)
    (quadraticForm_le_mulvec_bound _ hJ) hcoef x.ofLp
  rw [hv,mul_one] at hh
  have hc := mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hj) hA)
  nlinarith only [hh,hquad,hmargin,hc]

lemma overlap_neighborhood {n : ℕ} (hn : 0 < n) {q₀ r : ℝ} (hr : 2*r ≤ q₀)
    (y d : Field n) (hy : 2*q₀ < overlap y) (hd : vectorNorm d ≤ r*sqrt (n:ℝ)) :
    q₀ ≤ overlap (y+d) := by
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hh := varianceAverage_difference hn y d
  have hb := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2/sqrt (n:ℝ))
  have he : 2/sqrt (n:ℝ)*(r*sqrt (n:ℝ))=2*r := by field_simp
  rw [he] at hb
  unfold varianceAverage at hh
  linarith [le_abs_self ((1-overlap (y+d))-(1-overlap y))]

lemma high_temperature_small_margin {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
    ∃ A K q₀ c : ℝ,1 < A ∧ 2*sqrt j < K ∧ 0 < q₀ ∧ 0 < c ∧
      sqrt j*A < 1 ∧ 0 ≤ K-j ∧ c < 1-A*(K-j+6*j*q₀) := by
  have hs : 0 < sqrt j := sqrt_pos.mpr hj
  have hs1 : sqrt j < 1 := by simpa using sqrt_lt_sqrt hj.le hj1
  have hjroot : j < 2*sqrt j := by nlinarith [sq_sqrt hj.le]
  let f : ℝ → ℝ := fun δ=>1-(1+δ)*(2*sqrt j+2*δ-j+6*j*δ)
  let g : ℝ → ℝ := fun δ=>sqrt j*(1+δ)
  have hf0 : 0 < f 0 := by dsimp [f];nlinarith [sq_sqrt hj.le,sq_pos_of_pos (sub_pos.mpr hs1)]
  have hc : ContinuousAt f 0 := by dsimp [f];fun_prop
  have hg : ContinuousAt g 0 := by dsimp [g];fun_prop
  have he : ∀ᶠ δ in nhds (0:ℝ),0 < f δ ∧ g δ < 1 :=
    (hc.tendsto.eventually_const_lt hf0).and (hg.tendsto.eventually_lt_const (by simpa [g] using hs1))
  obtain ⟨r,hr,hrgood⟩ := Metric.eventually_nhds_iff.mp he
  have hd : dist (r/2) (0:ℝ) < r := by rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)];linarith
  obtain ⟨hf,hg⟩ := hrgood hd
  refine ⟨1+r/2,2*sqrt j+2*(r/2),r/2,f (r/2)/2,by linarith,by linarith,
    half_pos hr,half_pos hf,hg,by linarith,?_⟩
  change f (r/2)/2 < f (r/2)
  linarith
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_SmallRootStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem small_time_root_stability {j A K q₀ c : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hA : 1 ≤ A) (hK : 0 ≤ K) (hKj : 0 ≤ K-j) (hq₀ : 0 < q₀)
    (hmargin : c < 1-A*(K-j+6*j*q₀)) :
    ∃ t₀ ρ a : ℝ,0 < t₀ ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ,0 < N ∧
    ∀ (n : ℕ),N ≤ n → ∀ t ∈ Icc 0 t₀, ∀ ε : ℝ,
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
      {p | (∀ z : Field n,vectorNorm (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)*ᵥz) ≤ K*vectorNorm z) ∧
        ∃ y : Field n, vectorNorm (tapField j (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
          (fun i=>t+p.2 i) y) ≤ ρ*sqrt (n:ℝ) ∧
          (goeMatrix (j/(n:ℝ)) p.1,y)∈badFieldSet n j A ε c} ≤
        4*exp (-min 1 (1/(π^2*j))*(n:ℝ))+exp (-a*(n:ℝ)) := by
  obtain ⟨t₀,σb,a,ht₀,hσb,ha,Nb,hbad⟩ := smalltime_bad_integral hj hj1 hq₀
  let r := q₀/2
  have hr : 0 < r := half_pos hq₀
  have hrq : 2*r ≤ q₀ := by dsimp [r];linarith
  obtain ⟨ε₁,hε₁,hvol⟩ := local_volume_uniform hj.le hK hr (half_pos ha)
  obtain ⟨γ,hγ,Nd,hNd,hdet⟩ := field_logdet_uniform hj hj1 hε₁
  obtain ⟨σ₀,hσ₀,hσvol⟩ := hvol γ hγ
  let σ := min (σ₀/2) σb
  have hσ : 0 < σ := lt_min (by positivity) hσb
  have hσless : σ < σ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hσle : σ ≤ σb := min_le_right _ _
  obtain ⟨ρ,hρ,Nv,hNv,hv⟩ := hσvol σ hσ hσless
  refine ⟨t₀,ρ,a/2,ht₀,hρ,half_pos ha,
    max Nb (max Nd Nv),hNd.trans_le ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro n hn t ht ε
  have hnb : Nb ≤ n := (le_max_left _ _).trans hn
  have hnd : Nd ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnv : Nv ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn0 : 0 < n := hNv.trans_le hnv
  let : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let D : Set (MatrixCoordinates (Fin n) → ℝ) := {g | ∃ y : Field n,
    (n:ℝ)*(j*varianceAverage y^2+ε₁) <
      log ((fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y)ᵀ*
        fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y+γ • 1).det}
  let I : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) → ℝ≥0∞ := fun p=>
    fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)) (fun i=>t+p.2 i)
      {y | q₀ ≤ overlap y}
  have hE : MeasurableSet {y : Field n | q₀ ≤ overlap y} :=
    (isClosed_le continuous_const (by unfold overlap magnetization;fun_prop)).measurableSet
  have hI : Measurable I := measurable_fieldIntegral_cylinder j t σ _ hE
  have hInt : ∫⁻ p,I p ∂μ.prod ν ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
    rw [lintegral_prod _ hI.aemeasurable]
    exact hbad n hnb t ht σ ⟨hσ,hσle⟩
  have hMarkov := markov_exponential (μ.prod ν) hI (b := a/2) hInt
  have hrate : a-a/2=a/2 := by ring
  rw [hrate] at hMarkov
  have hDP : (μ.prod ν).real (D ×ˢ (Set.univ : Set (Fin n → ℝ))) ≤
      4*exp (-min 1 (1/(π^2*j))*(n:ℝ)) := by
    rw [measureReal_prod_prod]
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one]
    exact hdet n hnd
  apply measureReal_union_detector (μ.prod ν) _ (D ×ˢ Set.univ) I
    (exp (-(a/2)*(n:ℝ))) _ _ hDP hMarkov
  rintro p ⟨hJ,y,hres,hy⟩ hp
  have hp' : p.1∉D := fun hh=>hp ⟨hh,mem_univ _⟩
  dsimp [I]
  rw [fieldIntegral_eq_localVolume hσ]
  apply hv n hnv _ hJ _ y {z | q₀ ≤ overlap z} hE
  · intro d hd
    exact overlap_neighborhood hn0 hrq y d
      (badField_small_overlap_impossible hn0 hj.le (zero_le_one.trans hA) hKj hmargin _ y hJ hy) hd
  · exact not_lt.mp (fun hh=>hp' ⟨y,hh⟩)
  · exact hres
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PlantedFixedTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators ENNReal

lemma badFieldSet_mono_margin {n : ℕ} (j A ε : ℝ) {c c' : ℝ} (h : c ≤ c') :
    badFieldSet n j A ε c ⊆ badFieldSet n j A ε c' := by
  rintro p ⟨a,ha,hd,x,hx,hq⟩
  exact ⟨a,ha,hd,x,hx,hq.trans h⟩

lemma plantedRootBad_mono {n : ℕ} (j A K ε t : ℝ) {c c' ρ ρ' : ℝ}
    (hc : c ≤ c') (hρ : ρ ≤ ρ') :
    plantedRootBad n j A K ε c ρ t ⊆ plantedRootBad n j A K ε c' ρ' t := by
  rintro p ⟨hJ,y,hres,hy⟩
  exact ⟨hJ,y,hres.trans (mul_le_mul_of_nonneg_right hρ (sqrt_nonneg _)),
    badFieldSet_mono_margin j A ε hc hy⟩

lemma two_exponential_tails {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ r : ℝ,0 < r ∧ ∃ N : ℕ, ∀ n : ℕ,N ≤ n →
      4*exp (-a*(n:ℝ))+exp (-b*(n:ℝ)) ≤ exp (-r*(n:ℝ)) := by
  let r := min a b/2
  have hr : 0 < r := half_pos (lt_min ha hb)
  obtain ⟨N,hN⟩ := absorb_finite_exponential_factor 5 hr
  refine ⟨r,hr,N,fun n hn=>?_⟩
  have he₁ : exp (-a*(n:ℝ)) ≤ exp (-(2*r)*(n:ℝ)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [r];linarith [min_le_left a b]) (Nat.cast_nonneg _))
  have he₂ : exp (-b*(n:ℝ)) ≤ exp (-(2*r)*(n:ℝ)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [r];linarith [min_le_right a b]) (Nat.cast_nonneg _))
  have hh := hN n hn (-(2*r))
  calc
    _ ≤ 5*exp (-(2*r)*(n:ℝ)) := by linarith only [he₁,he₂]
    _ ≤ exp (-r*(n:ℝ)) := by
      convert hh using 1 <;> congr 1 <;> ring_nf

theorem planted_fixed_time_root_stability {j T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hT : 0 < T) :
    ∃ A K ε c ρ a : ℝ,1 < A ∧ 2*sqrt j < K ∧ sqrt j*A < 1 ∧
      0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ,0 < N ∧
    ∀ n : ℕ,N ≤ n → ∀ t ∈ Icc 0 T,
      ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
        (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
        (plantedRootBad n j A K ε c ρ t) ≤ exp (-a*(n:ℝ)) := by
  obtain ⟨A,K,q₀,cs,hA,hK,hq₀,hcs,hsub,hKj,hmargin⟩ := high_temperature_small_margin hj hj1
  have hK0 : 0 ≤ K := (mul_nonneg (by norm_num : (0:ℝ)≤2) (sqrt_nonneg _)).trans hK.le
  obtain ⟨ts,ρs,as,hts,hρs,has,Ns,hNs,hs⟩ := small_time_root_stability hj hj1 hA.le hK0 hKj hq₀ hmargin
  obtain ⟨ε,cp,ρp,ap,hε,hcp,hρp,hap,Np,hNp,hp⟩ := positive_time_root_stability hj hj1 hA.le hsub hK0
    (lt_min hts hT) (min_le_right ts T)
  have hd : 0 < min 1 (1/(π^2*j)) := lt_min zero_lt_one (by positivity)
  obtain ⟨a,ha,Na,hNa⟩ := two_exponential_tails hd (lt_min has hap)
  refine ⟨A,K,ε,min cs cp,min ρs ρp,a,hA,hK,hsub,hε,lt_min hcs hcp,
    lt_min hρs hρp,ha,max Na (max Ns Np),hNs.trans_le ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro n hn t ht
  have hns : Ns ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnp : Np ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hna : Na ≤ n := (le_max_left _ _).trans hn
  apply le_trans ?_ (hNa n hna)
  by_cases htt : t ≤ ts
  · have hh := hs n hns t ⟨ht.1,htt⟩ ε
    apply (measureReal_mono (plantedRootBad_mono j A K ε t (min_le_left _ _) (min_le_left _ _))
      (measure_ne_top _ _)).trans
    exact hh.trans (add_le_add le_rfl (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left as ap)) (Nat.cast_nonneg _))))
  · have hh := hp n hnp t ⟨(min_le_left ts T).trans (not_le.mp htt).le,ht.2⟩
    apply (measureReal_mono (plantedRootBad_mono j A K ε t (min_le_right _ _) (min_le_right _ _))
      (measure_ne_top _ _)).trans
    exact hh.trans (add_le_add le_rfl (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right as ap)) (Nat.cast_nonneg _))))
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

lemma tapField_add_diagonal {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y d : Field n) :
    tapField j (J+diagonal d) h y=tapField j J h y-(fun i=>d i*magnetization y i) := by
  ext i
  simp only [tapField,Matrix.add_apply,add_mul,Finset.sum_add_distrib,Pi.sub_apply]
  rw [show (∑ k,diagonal d i k*magnetization y k)=d i*magnetization y i by
    simp [Matrix.diagonal_apply]]
  ring

lemma tapField_diagonal_difference_bound {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h y d : Field n)
    (hd : ∀ i,|d i| ≤ δ) :
    vectorNorm (tapField j (J+diagonal d) h y-tapField j J h y) ≤ δ*sqrt (n:ℝ) := by
  rw [tapField_add_diagonal,sub_sub_cancel_left]
  change ‖-(WithLp.toLp 2 (fun i=>d i*magnetization y i))‖ ≤ _
  rw [norm_neg]
  exact (vectorNorm_diag_le hδ hd (magnetization y)).trans
    (mul_le_mul_of_nonneg_left (magnetization_norm_bound y) hδ)

lemma hessian_diagonal_difference {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y a d x : Field n) (ha : ∀ i,0 ≤ a i) :
    quadraticForm (fieldHessian j (J+diagonal d) y a) x-
      quadraticForm (fieldHessian j J y a) x = -(∑ i,a i*d i*x i^2) := by
  let v : Field n := fun i=>sqrt (a i)*x i
  have hq : quadraticForm (J+diagonal d) v-quadraticForm J v=∑ i,d i*v i^2 := by
    simp only [quadraticForm,Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib,add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diagonal_apply,ite_mul,mul_ite,mul_zero,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    ring
  rw [hessian_quadratic_formula,hessian_quadratic_formula]
  have hv : (∑ i,d i*v i^2)=∑ i,a i*d i*x i^2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v]
    rw [mul_pow,sq_sqrt (ha i)]
    ring
  change _-quadraticForm (J+diagonal d) v-_ - (_-quadraticForm J v-_) = _
  rw [← hv]
  linarith only [hq]

lemma hessian_diagonal_difference_bound {n : ℕ} {A δ : ℝ} (hA : 0 ≤ A) (_hδ : 0 ≤ δ)
    (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (y a d x : Field n)
    (ha0 : ∀ i,0 ≤ a i) (haA : ∀ i,a i ≤ A) (hd : ∀ i,|d i| ≤ δ) :
    |quadraticForm (fieldHessian j (J+diagonal d) y a) x-
      quadraticForm (fieldHessian j J y a) x| ≤ A*δ*vectorSqNorm x := by
  rw [hessian_diagonal_difference j J y a d x ha0,abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold vectorSqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [abs_mul, abs_of_nonneg (ha0 i),abs_of_nonneg (sq_nonneg (x i))]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (haA i) (hd i) (abs_nonneg _) hA) (sq_nonneg _)

lemma mulvec_add_diagonal_bound {n : ℕ} {K δ : ℝ} (hδ : 0 ≤ δ)
    (J : Matrix (Fin n) (Fin n) ℝ) (d : Field n)
    (hJ : ∀ z : Field n,vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (hd : ∀ i,|d i| ≤ δ) :
    ∀ z : Field n,vectorNorm ((J+diagonal d)*ᵥz) ≤ (K+δ)*vectorNorm z := by
  intro z
  have he : diagonal d*ᵥz=(fun i=>d i*z i) := by ext i; exact mulVec_diagonal d z i
  rw [add_mulVec,he]
  calc
    _ ≤ vectorNorm (J*ᵥz)+vectorNorm (fun i=>d i*z i) := vectorNorm_add_le _ _
    _ ≤ K*vectorNorm z+δ*vectorNorm z := add_le_add (hJ z) (vectorNorm_diag_le hδ hd z)
    _ = _ := by ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_RootDiagonalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

lemma rootBad_diagonal_transfer {n : ℕ} {j A ε c ρ δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h d : Field n) (hd : ∀ i,|d i| ≤ δ) :
    rootBad j A ε c ρ J h → rootBad j A ε (c+A*δ) (ρ+δ) (J+diagonal d) h := by
  rintro ⟨y,hy,a,ha,hdist,x,hx,hq⟩
  refine ⟨y,?_,a,ha,hdist,x,hx,?_⟩
  · have hdiff := tapField_diagonal_difference_bound hδ j J h y d hd
    have hh := vectorNorm_add_le (tapField j J h y)
      (tapField j (J+diagonal d) h y-tapField j J h y)
    rw [add_sub_cancel] at hh
    exact (hh.trans (add_le_add hy hdiff)).trans_eq (by ring)
  · have hdiff := hessian_diagonal_difference_bound hA hδ j J y a d x.ofLp
      (fun i=>(ha i).1) (fun i=>(ha i).2) hd
    have hv : vectorSqNorm x.ofLp=1 := by
      rw [← vectorNorm_sq]
      change ‖x‖^2=1
      rw [hx];norm_num
    rw [hv,mul_one] at hdiff
    linarith only [le_abs_self (quadraticForm (fieldHessian j (J+diagonal d) y a) x.ofLp-
      quadraticForm (fieldHessian j J y a) x.ofLp),hdiff,hq]

lemma rootBad_mono {n : ℕ} {j A ε c c' ρ ρ' : ℝ}
    (hc : c ≤ c') (hρ : ρ ≤ ρ') (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    rootBad j A ε c ρ J h → rootBad j A ε c' ρ' J h := by
  rintro ⟨y,hy,a,ha,hd,x,hx,hq⟩
  exact ⟨y,hy.trans (mul_le_mul_of_nonneg_right hρ (sqrt_nonneg _)),a,ha,hd,x,hx,hq.trans hc⟩

lemma eraseDiagonal_add {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) :
    eraseDiagonal J+diagonal (fun i=>J i i)=J := sub_add_cancel _ _

lemma erased_planted_witness {n : ℕ} {j A K ε c ρ δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδρ : δ ≤ ρ/2) (hδc : A*δ ≤ c/2)
    (t : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) (b : Field n)
    (hd : ∀ i,|plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i| ≤ δ)
    (hJ : ∀ z : Field n,vectorNorm ((eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)))*ᵥz) ≤
      (K-δ)*vectorNorm z)
    (hbad : rootBad j A ε (c/2) (ρ/2)
      (eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))) (fun i=>t+b i)) :
    (g,b)∈plantedRootBad n j A K ε c ρ t := by
  let J := plantedInteraction j (goeMatrix (j/(n:ℝ)) g)
  have hjnorm := mulvec_add_diagonal_bound hδ (eraseDiagonal J) (fun i=>J i i) hJ hd
  rw [eraseDiagonal_add] at hjnorm
  have hjnorm' : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z := by
    simpa only [sub_add_cancel] using hjnorm
  have hh := rootBad_diagonal_transfer hA hδ (eraseDiagonal J) (fun i=>t+b i) (fun i=>J i i) hd hbad
  rw [eraseDiagonal_add] at hh
  obtain ⟨y,hy,a,ha,hdist,x,hx,hq⟩ := rootBad_mono (by linarith : c/2+A*δ ≤ c)
    (by linarith : ρ/2+δ ≤ ρ) J (fun i=>t+b i) hh
  exact ⟨hjnorm',y,hy,a,ha,hdist,x,hx,hq⟩
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_RootBadMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {n : ℕ}
attribute [local instance] OAI.SKGap.matrixMeasurable
local instance matrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma continuous_joint_tapField (j : ℝ) :
    Continuous (fun p : (Matrix (Fin n) (Fin n) ℝ × Field n) × Field n=>tapField j p.1.1 p.1.2 p.2) := by
  unfold tapField onsager overlap magnetization
  fun_prop

lemma rootBad_iff_unplanted (j A ε c ρ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    rootBad j A ε c ρ J h ↔ ∃ y : Field n,vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ) ∧
      (J-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),y)∈badFieldSet n j A ε c := by
  simp only [rootBad,badFieldSet,mem_ofPred_eq,plantedInteraction,sub_add_cancel]

lemma isClosed_bounded_rootBad (j A ε c ρ : ℝ) (m : ℕ) :
    IsClosed {p : Matrix (Fin n) (Fin n) ℝ × Field n | ∃ y ∈ Metric.closedBall (0 : Field n) m,
      vectorNorm (tapField j p.1 p.2 y) ≤ ρ*sqrt (n:ℝ) ∧
      (p.1-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),y)∈badFieldSet n j A ε c} := by
  let X := ↥(Metric.closedBall (0 : Field n) m)
  let : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Field n) m)
  let S : Set (X × (Matrix (Fin n) (Fin n) ℝ × Field n)) :=
    {p | vectorNorm (tapField j p.2.1 p.2.2 p.1) ≤ ρ*sqrt (n:ℝ) ∧
      (p.2.1-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),(p.1:Field n))∈badFieldSet n j A ε c}
  have hy : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × Field n)=>(p.1:Field n)) :=
    continuous_subtype_val.comp continuous_fst
  have ht := (continuous_joint_tapField (n:=n) j).comp (continuous_snd.prodMk hy)
  have hS : IsClosed S := (isClosed_le ((continuous_vectorNorm n).comp ht) continuous_const).inter
    ((isClosed_badFieldSet n j A ε c).preimage
      (((continuous_fst.comp continuous_snd).sub continuous_const).prodMk hy))
  have hp := isClosedMap_snd_of_compactSpace S hS
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨y,hy,hr,hb⟩
    exact ⟨(⟨y,hy⟩,p),⟨hr,hb⟩,rfl⟩
  · rintro ⟨⟨y,p⟩,⟨hr,hb⟩,rfl⟩
    exact ⟨y,y.property,hr,hb⟩

theorem measurableSet_rootBad (j A ε c ρ : ℝ) :
    MeasurableSet {p : Matrix (Fin n) (Fin n) ℝ × Field n | rootBad j A ε c ρ p.1 p.2} := by
  have he : {p : Matrix (Fin n) (Fin n) ℝ × Field n | rootBad j A ε c ρ p.1 p.2}=
      ⋃ m : ℕ,{p : Matrix (Fin n) (Fin n) ℝ × Field n | ∃ y ∈ Metric.closedBall (0 : Field n) m,
        vectorNorm (tapField j p.1 p.2 y) ≤ ρ*sqrt (n:ℝ) ∧
        (p.1-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),y)∈badFieldSet n j A ε c} := by
    ext p
    rw [mem_ofPred_eq,rootBad_iff_unplanted]
    constructor
    · rintro ⟨y,hr,hb⟩
      obtain ⟨m,hm⟩ := exists_nat_ge ‖y‖
      exact mem_iUnion.mpr ⟨m,y,by simpa only [Metric.mem_closedBall,dist_zero_right] using hm,hr,hb⟩
    · intro hp
      obtain ⟨m,y,_,hr,hb⟩ := mem_iUnion.mp hp
      exact ⟨y,hr,hb⟩
  rw [he]
  exact MeasurableSet.iUnion (fun m=>(isClosed_bounded_rootBad j A ε c ρ m).measurableSet)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_SpinEnergy
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators

lemma sum_edges {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ e : Edge n,f e.1.1 e.1.2)=∑ i,∑ k,if i < k then f i k else 0 := by
  have he := Finset.sum_subtype (F:=inferInstance) (p:=fun p : Fin n×Fin n=>p.1 < p.2) (Finset.univ.filter (fun p : Fin n×Fin n=>p.1 < p.2))
    (by simp) (fun p=>f p.1 p.2)
  simpa only [Finset.sum_filter,Fintype.sum_prod_type] using he.symm

lemma edge_energy_formula {n : ℕ} (g : Disorder n) (x : Spin n) :
    hamiltonian g 0 x=∑ e : Edge n,g e*spinValue (x e.1.1)*spinValue (x e.1.2) := by
  let f : Fin n → Fin n → ℝ := fun i k=>spinValue (x i)*coupling g i k*spinValue (x k)
  have hsymm : ∀ i k,f i k=f k i := by intro i k; dsimp [f];rw [coupling_symm g i k];ring
  have hz : ∀ i,f i i=0 := by intro i;simp [f]
  have hf : (∑ i,∑ k,f i k)=2*∑ i,∑ k,if i < k then f i k else 0 := by
    have hh : ∀ i k,f i k=(if i < k then f i k else 0)+(if k < i then f k i else 0) := by
      intro i k
      rcases lt_trichotomy i k with h|rfl|h
      · simp [h,not_lt_of_gt h]
      · simp [hz]
      · simp only [ite_eq_right (not_lt_of_gt h),ite_eq_left h,zero_add];exact hsymm i k
    conv_lhs => arg 2; ext i; arg 2; ext k; rw [hh i k]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f:=fun i k=>if k < i then f k i else 0)]
    ring
  have he : (∑ e : Edge n,g e*spinValue (x e.1.1)*spinValue (x e.1.2))=
      ∑ i,∑ k,if i < k then f i k else 0 := by
    rw [← sum_edges f]
    apply Finset.sum_congr rfl
    intro e _
    simp only [f,coupling,dite_eq_left e.2]
    ring
  rw [he]
  change 1/2*(∑ i,∑ k,f i k)+ (∑ i,(0:Fin n→ℝ) i*spinValue (x i))=_
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
  rw [hf];ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianPartition
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussianSpinPartition_eq_partition {n : ℕ} (r : ℝ) (g : Disorder n) :
    gaussianSpinPartition n r g=partition (fun e=>sqrt r*g e) 0 := by
  unfold gaussianSpinPartition partition weight
  apply Finset.sum_congr rfl;intro x _
  rw [edge_energy_formula]
  congr 1
  apply Finset.sum_congr rfl;intro e _
  unfold edgeCoefficient;ring

lemma edgeCoefficient_sq_sum {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (x : Spin n) :
    (∑ e,edgeCoefficient r x e^2)= r*(Fintype.card (Edge n):ℝ) := by
  simp only [edgeCoefficient,mul_pow,spinValue_sq,sq_sqrt hr,mul_one,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

lemma gaussianSpinPartition_integral {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    (∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n))=
      (Fintype.card (Spin n):ℝ)*exp (r*(Fintype.card (Edge n):ℝ)/2) := by
  unfold gaussianSpinPartition
  rw [integral_finsetSum _ (fun x _=>linear_gaussian_exp_integrable (edgeCoefficient r x))]
  simp only [linear_gaussian_exp_integral,edgeCoefficient_sq_sum hr,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianSquareTail
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussian_square_exp_integral :
    (∫ x : ℝ,exp (x^2/4) ∂gaussianReal 0 1) ≤ 2 := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun y=>by simp [gaussianPDF]))]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul]
  have he : (fun x : ℝ=>gaussianPDFReal 0 1 x*exp (x^2/4))=
      (fun x : ℝ=>(1/sqrt (2*Real.pi))*exp (-(1/4:ℝ)*x^2)) := by
    funext x
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_assoc,← exp_add]
    congr 2 <;> ring
  rw [he,integral_const_mul,integral_gaussian]
  have hp := Real.pi_pos
  have h1 := sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have h2 := sq_sqrt (show 0 ≤ Real.pi/(1/4:ℝ) by positivity)
  have h3 := sqrt_nonneg (2*Real.pi)
  have h4 := sqrt_nonneg (Real.pi/(1/4:ℝ))
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ (sqrt_pos.mpr (by positivity))).mpr
  nlinarith

lemma gaussian_square_exp_integrable :
    Integrable (fun x : ℝ=>exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),integrable_withDensity_iff
    (measurable_gaussianPDF 0 1) (ae_of_all _ (fun y=>by simp [gaussianPDF]))]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  have hi := (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/4 by norm_num)).const_mul (1/sqrt (2*Real.pi))
  have he : (fun g : ℝ=>exp (g^2/4)*gaussianPDFReal 0 1 g)=
      (fun g : ℝ=>(1/sqrt (2*Real.pi))*exp (-(1/4:ℝ)*g^2)) := by
    funext g
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_left_comm,← exp_add]
    congr 2 <;> ring
  rw [he]
  exact hi

lemma product_gaussian_square_exp_integral {ι : Type*} [Fintype ι] :
    (∫ g : ι→ℝ,exp ((∑ i,g i^2)/4) ∂Measure.pi (fun _ : ι=>gaussianReal 0 1)) ≤
      exp ((Fintype.card ι:ℝ)*log 2) := by
  have he (g : ι→ℝ) : exp ((∑ i,g i^2)/4)=∏ i,exp (g i^2/4) := by
    rw [← exp_sum,Finset.sum_div]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f:=fun _ : ι=>fun x : ℝ=>exp (x^2/4))]
  calc
    _ ≤ ∏ _i : ι,(2:ℝ) := Finset.prod_le_prod
      (fun i _=>integral_nonneg (fun x=>(exp_pos _).le))
      (fun i _=>gaussian_square_exp_integral)
    _ = _ := by rw [Finset.prod_const,Finset.card_univ,exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]

lemma product_gaussian_square_exp_integrable {ι : Type*} [Fintype ι] :
    Integrable (fun g : ι→ℝ=>exp ((∑ i,g i^2)/4))
      (Measure.pi (fun _ : ι=>gaussianReal 0 1)) := by
  have hi := Integrable.fintype_prod (fun _ : ι=>gaussian_square_exp_integrable)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext g
  rw [← exp_sum,Finset.sum_div]

lemma product_gaussian_square_tail {ι : Type*} [Fintype ι] (t : ℝ) :
    (Measure.pi (fun _ : ι=>gaussianReal 0 1)).real {g | t < ∑ i,g i^2} ≤
      exp (-t/4+(Fintype.card ι:ℝ)*log 2) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (Measure.pi (fun _ : ι=>gaussianReal 0 1))
      (fun g=>(exp_pos ((∑ i,g i^2)/4)).le)) product_gaussian_square_exp_integrable (exp (t/4))
  have hs : {g : ι→ℝ| t < ∑ i,g i^2} ⊆ {g | exp (t/4) ≤ exp ((∑ i,g i^2)/4)} := by
    intro g hg
    exact exp_le_exp.mpr (by linarith only [show t < ∑ i,g i^2 from hg])
  have hb := (mul_le_mul_of_nonneg_left (measureReal_mono hs)
    (exp_pos (t/4)).le).trans (hm.trans product_gaussian_square_exp_integral)
  rw [show -t/4+(Fintype.card ι:ℝ)*log 2=(Fintype.card ι:ℝ)*log 2-t/4 by ring,exp_sub]
  apply (le_div_iff₀ (exp_pos _)).mpr
  simpa only [mul_comm] using hb
end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal
variable {κ : Type*} [Fintype κ]

lemma gaussian_scaled_coordinates_hasLaw {r : ℝ} (hr : 0 ≤ r) :
    HasLaw (fun g : κ→ℝ=>fun k=>sqrt r*g k)
      (Measure.pi (fun _ : κ=>gaussianReal 0 (Real.toNNReal r))) (gaussianCoordinates κ) := by
  have hl (k : κ) : HasLaw (fun g : κ→ℝ=>sqrt r*g k)
      (gaussianReal 0 (Real.toNNReal r)) (gaussianCoordinates κ) := by
    have h := gaussianReal_const_mul (coordinate_hasLaw (κ:=κ) k) (sqrt r)
    have hv : (⟨(sqrt r)^2,sq_nonneg _⟩:ℝ≥0)*1=Real.toNNReal r := by
      apply NNReal.eq
      change (sqrt r)^2*1=↑(Real.toNNReal r)
      rw [mul_one,sq_sqrt hr,Real.coe_toNNReal _ hr]
    rw [mul_zero] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg (gaussianReal 0) hv.symm
  exact iIndepFun.hasLaw_pi hl ((iIndepFun_pi (fun _ : κ=>aemeasurable_id)).comp
    (fun _=>fun x : ℝ=>sqrt r*x) (fun _=>by fun_prop))

lemma scaled_gaussian_square_tail {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 (Real.toNNReal r))).real {g | t < ∑ i,g i^2} ≤
      exp (-t/(4*r)+(Fintype.card κ:ℝ)*log 2) := by
  have hm : MeasurableSet {g : κ→ℝ | t < ∑ i,g i^2} := by measurability
  rw [← (gaussian_scaled_coordinates_hasLaw (κ:=κ) hr.le).measureReal_eq hm]
  have he : {g : κ→ℝ | t < ∑ i,(sqrt r*g i)^2}={g | t/r < ∑ i,g i^2} := by
    ext g
    simp only [Set.mem_ofPred_eq,mul_pow,sq_sqrt hr.le,← Finset.mul_sum]
    rw [div_lt_iff₀ hr,mul_comm]
  rw [he]
  simpa only [gaussianCoordinates,neg_div,div_div,mul_comm r (4:ℝ)] using
    product_gaussian_square_tail (ι:=κ) (t/r)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussian_real_square_tail {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (gaussianReal 0 (Real.toNNReal r)).real {x : ℝ | t < x^2} ≤ exp (-t/(4*r)+log 2) := by
  have h : HasLaw (fun v : Unit→ℝ=>v ()) (gaussianReal 0 (Real.toNNReal r))
      (Measure.pi (fun _ : Unit=>gaussianReal 0 (Real.toNNReal r))) :=
    ⟨(measurable_pi_apply ()).aemeasurable,(measurePreserving_eval (fun _ : Unit=>gaussianReal 0 (Real.toNNReal r)) ()).map_eq⟩
  rw [← h.measureReal_eq (by measurability : MeasurableSet {x : ℝ | t < x^2})]
  simpa using scaled_gaussian_square_tail (κ:=Unit) hr t

lemma gaussian_real_abs_tail {r : ℝ} (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
    (gaussianReal 0 (Real.toNNReal r)).real {x : ℝ | d < |x|} ≤ 2*exp (-d^2/(4*r)) := by
  have he : {x : ℝ | d < |x|}={x | d^2 < x^2} := by
    ext x
    simpa only [Set.mem_ofPred_eq,sq_abs] using (sq_lt_sq₀ hd (abs_nonneg x)).symm
  rw [he]
  apply (gaussian_real_square_tail hr (d^2)).trans_eq
  rw [exp_add,exp_log (by norm_num : (0:ℝ) < 2),mul_comm]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_PartitionSecondMoment
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussianSpinPartition_pos (n : ℕ) (r : ℝ) (g : Disorder n) :
    0 < gaussianSpinPartition n r g :=
  Finset.sum_pos (fun _ _=>exp_pos _) Finset.univ_nonempty

lemma gaussianSpinPartition_measurable (n : ℕ) (r : ℝ) : Measurable (gaussianSpinPartition n r) := by
  unfold gaussianSpinPartition
  exact Finset.measurable_sum _ (fun x _=>Real.measurable_exp.comp
    (Finset.measurable_sum _ (fun e _=>(measurable_pi_apply e).const_mul _)))

lemma gaussianSpinPartition_mean_pos {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    0 < ∫ g, gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n) := by
  rw [gaussianSpinPartition_integral hr]
  exact mul_pos (by exact_mod_cast Fintype.card_pos) (exp_pos _)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianTailScale
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators NNReal Topology

lemma gaussian_disorder_hasLaw (β : ℝ) (n : ℕ) :
    HasLaw (fun g : Disorder n=>fun e=>sqrt (β^2/(n:ℝ))*g e) (disorderLaw β n)
      (gaussianCoordinates (Edge n)) := by
  have hr : 0 ≤ β^2/(n:ℝ) := by positivity
  have hl (e : Edge n) : HasLaw (fun g : Disorder n=>sqrt (β^2/(n:ℝ))*g e)
      (gaussianReal 0 (Real.toNNReal (β^2/(n:ℝ)))) (gaussianCoordinates (Edge n)) := by
    have h := gaussianReal_const_mul (coordinate_hasLaw (κ:=Edge n) e) (sqrt (β^2/(n:ℝ)))
    have hv : (⟨(sqrt (β^2/(n:ℝ)))^2,sq_nonneg _⟩:ℝ≥0)*1=Real.toNNReal (β^2/(n:ℝ)) := by
      apply NNReal.eq
      change (sqrt (β^2/(n:ℝ)))^2*1=↑(Real.toNNReal (β^2/(n:ℝ)))
      rw [mul_one,sq_sqrt hr,Real.coe_toNNReal _ hr]
    rw [mul_zero] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg (gaussianReal 0) hv.symm
  exact iIndepFun.hasLaw_pi hl ((iIndepFun_pi (fun _ : Edge n=>aemeasurable_id)).comp
    (fun _=>fun x : ℝ=>sqrt (β^2/(n:ℝ))*x) (fun _=>by fun_prop))

lemma partition_zero_measurable (n : ℕ) : Measurable (fun g : Disorder n=>partition g 0) := by
  have he : (fun g : Disorder n=>partition g 0)=gaussianSpinPartition n 1 := by
    ext g
    rw [gaussianSpinPartition_eq_partition]
    simp only [sqrt_one,one_mul]
  rw [he]
  exact gaussianSpinPartition_measurable n 1

lemma disorder_partition_mean (β : ℝ) (n : ℕ) :
    (∫ g,partition g 0 ∂disorderLaw β n)=
      ∫ g,gaussianSpinPartition n (β^2/(n:ℝ)) g ∂gaussianCoordinates (Edge n) := by
  have h := (gaussian_disorder_hasLaw β n).integral_comp (partition_zero_measurable n).aestronglyMeasurable
  simpa only [Function.comp_def,gaussianSpinPartition_eq_partition] using h.symm

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianTiltIdentity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

lemma gaussianPDFReal_standard_tilt (a x : ℝ) :
    gaussianPDFReal a 1 x=gaussianPDFReal 0 1 x*exp (a*x-a^2/2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  have he : -(x-a)^2/2= -x^2/2+(a*x-a^2/2) := by ring
  rw [he,exp_add]
  ring

lemma gaussianCoordinates_tilt {κ : Type*} [Fintype κ] (a : κ→ℝ) :
    (gaussianCoordinates κ).withDensity
      (fun g=>ENNReal.ofReal (exp ((∑ i,a i*g i)-(∑ i,a i^2)/2))) =
      Measure.pi (fun i=>gaussianReal (a i) 1) := by
  have hp (g : κ→ℝ) : (∏ i,gaussianPDFReal (a i) 1 (g i))=
      (∏ i,gaussianPDFReal 0 1 (g i))*exp ((∑ i,a i*g i)-(∑ i,a i^2)/2) := by
    calc
      _ = ∏ i, (gaussianPDFReal 0 1 (g i)*exp (a i*g i-a i^2/2)) :=
        Finset.prod_congr rfl (fun i _=>gaussianPDFReal_standard_tilt _ _)
      _ = _ := by
        rw [Finset.prod_mul_distrib,← exp_sum]
        congr 2
        rw [Finset.sum_sub_distrib,Finset.sum_div]
  change (Measure.pi (fun _ : κ=>gaussianReal 0 1)).withDensity _=_
  rw [GaussianDensity.pi_gaussian_density (fun _ : κ=>0) (fun _=>1) (fun _=>one_ne_zero),
    GaussianDensity.pi_gaussian_density a (fun _=>1) (fun _=>one_ne_zero)]
  rw [← withDensity_mul _ (GaussianDensity.measurable_productPDF _ _) (by fun_prop)]
  congr 1
  ext g
  simp only [Pi.mul_apply,hp]
  exact (ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _=>gaussianPDFReal_nonneg 0 1 (g i)))).symm

lemma gaussianCoordinates_shift_hasLaw {κ : Type*} [Fintype κ] (a : κ→ℝ) :
    HasLaw (fun g : κ→ℝ => fun i=>g i+a i)
      (Measure.pi (fun i=>gaussianReal (a i) 1)) (gaussianCoordinates κ) := by
  have hl (i : κ) : HasLaw (fun g : κ→ℝ=>g i+a i)
      (gaussianReal (a i) 1) (gaussianCoordinates κ) := by
    simpa only [zero_add] using gaussianReal_add_const (coordinate_hasLaw i) (a i)
  exact iIndepFun.hasLaw_pi hl ((iIndepFun_pi (fun _ : κ=>aemeasurable_id)).comp
    (fun i=>fun x : ℝ=>x+a i) (fun _=>by fun_prop))

lemma gaussian_tilt_lintegral {κ : Type*} [Fintype κ] (a : κ→ℝ)
    (f : (κ→ℝ)→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g,ENNReal.ofReal (exp ((∑ i,a i*g i)-(∑ i,a i^2)/2))*f g ∂gaussianCoordinates κ)=
      ∫⁻ g,f (fun i=>g i+a i) ∂gaussianCoordinates κ := by
  have he := lintegral_withDensity_eq_lintegral_mul (gaussianCoordinates κ)
    (f:=fun g=>ENNReal.ofReal (exp ((∑ i,a i*g i)-(∑ i,a i^2)/2))) (by fun_prop) hf
  simp only [Pi.mul_apply] at he
  rw [← he,gaussianCoordinates_tilt]
  exact (gaussianCoordinates_shift_hasLaw a).lintegral_comp hf.aemeasurable |>.symm
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOESubmatrix
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_diagonal_hasLaw {r : ℝ} (hr : 0 ≤ r) (i : ι) :
    HasLaw (fun g : MatrixCoordinates ι→ℝ=>goeMatrix r g i i)
      (gaussianReal 0 (Real.toNNReal (2*r))) (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hg := (goe_matrix_gaussian (ι:=ι) r).eval (i,i)
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,goe_mean_zero,← covariance_self hg.aemeasurable,goe_entry_cov hr]
  simp only [ite_true,mul_one]
  congr 2
  ring

lemma goe_diagonal_tail {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ i : ι,d < |goeMatrix r g i i|} ≤
      2*(Fintype.card ι:ℝ)*exp (-d^2/(8*r)) := by
  have hsingle (i : ι) :
      (gaussianCoordinates (MatrixCoordinates ι)).real {g | d < |goeMatrix r g i i|} ≤
      2*exp (-d^2/(8*r)) := by
    rw [(goe_diagonal_hasLaw hr.le i).measureReal_eq
      (by measurability : MeasurableSet {x : ℝ | d < |x|})]
    convert gaussian_real_abs_tail (r:=2*r) (by positivity) hd using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have he : {g : MatrixCoordinates ι→ℝ | ∃ i : ι,d < |goeMatrix r g i i|}=
      ⋃ i : ι,{g | d < |goeMatrix r g i i|} := by ext g;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  apply (Finset.sum_le_sum (fun i _=>hsingle i)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_DiagonalStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

lemma absorb_linear_exponential {b : ℝ} (hb : 0 < b) :
    ∃ N : ℕ, ∀ n ≥ N,
      2*(n:ℝ)*exp (-b*(n:ℝ)) ≤ exp (-(b/2)*(n:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (16/b^2)
  refine ⟨N,fun n hn=>?_⟩
  have hnR : 16/b^2 ≤ (n:ℝ) := hN.trans (Nat.cast_le.mpr hn)
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hbn : 16 ≤ (n:ℝ)*b^2 := (div_le_iff₀ (sq_pos_of_pos hb)).mp hnR
  have hmul := mul_le_mul_of_nonneg_right hbn hn0
  have he := Real.pow_div_factorial_le_exp ((b/2)*(n:ℝ)) (by positivity) 2
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at he
  have hhead : 2*(n:ℝ) ≤ exp ((b/2)*(n:ℝ)) := by nlinarith
  calc
    _ ≤ exp ((b/2)*(n:ℝ))*exp (-b*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right hhead (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

lemma shifted_goe_diagonal_tail {j δ : ℝ} (hj : 0 < j) (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) (hmean : j/(n:ℝ) ≤ δ/2) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ i, δ < |plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i|} ≤
      2*(n:ℝ)*exp (-(δ^2/(32*j))*(n:ℝ)) := by
  have hr : 0 < j/(n:ℝ) := div_pos hj (Nat.cast_pos.mpr hn)
  have hs : {g : MatrixCoordinates (Fin n)→ℝ | ∃ i,
      δ < |plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i|} ⊆
      {g | ∃ i, δ/2 < |goeMatrix (j/(n:ℝ)) g i i|} := by
    rintro g ⟨i,hi⟩
    refine ⟨i,?_⟩
    have he : plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i =
        goeMatrix (j/(n:ℝ)) g i i+j/(n:ℝ) := by
      simp [plantedInteraction,Matrix.vecMulVec]
    rw [he] at hi
    have hh := abs_add_le (goeMatrix (j/(n:ℝ)) g i i) (j/(n:ℝ))
    rw [abs_of_pos hr] at hh
    linarith
  apply (measureReal_mono hs (measure_ne_top _ _)).trans
  have hh := goe_diagonal_tail (ι:=Fin n) hr (half_pos hδ).le
  have he : -(δ/2)^2/(8*(j/(n:ℝ))) = -(δ^2/(32*j))*(n:ℝ) := by
    field_simp
    ring
  simpa only [Fintype.card_fin,he] using hh

lemma erased_planted_probability {n : ℕ} {j A K ε c ρ δ a t : ℝ}
    (hj : 0 < j) (hA : 0 ≤ A) (hδ : 0 < δ) (hn : 0 < n)
    (hδρ : δ ≤ ρ/2) (hδc : A*δ ≤ c/2) (hmean : j/(n:ℝ) ≤ δ/2)
    (hp : ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
       (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
        (plantedRootBad n j A K ε c ρ t) ≤ exp (-a*(n:ℝ))) :
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
       (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
        (erasedPlantedRootBad n j A (K-δ) ε (c/2) (ρ/2) t) ≤
      exp (-a*(n:ℝ))+2*(n:ℝ)*exp (-(δ^2/(32*j))*(n:ℝ)) := by
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let D := {g : MatrixCoordinates (Fin n)→ℝ | ∃ i,
    δ < |plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i|}
  have hs : erasedPlantedRootBad n j A (K-δ) ε (c/2) (ρ/2) t ⊆
      plantedRootBad n j A K ε c ρ t ∪ (D ×ˢ (Set.univ : Set (Fin n→ℝ))) := by
    intro p hp
    by_cases hd : p.1∈D
    · exact Or.inr ⟨hd,mem_univ _⟩
    · apply Or.inl
      exact erased_planted_witness hA hδ.le hδρ hδc t p.1 p.2
        (fun i=>le_of_not_gt (fun hi=>hd ⟨i,hi⟩)) hp.1 hp.2
  have hD : (μ.prod ν).real (D ×ˢ (Set.univ : Set (Fin n→ℝ))) ≤
      2*(n:ℝ)*exp (-(δ^2/(32*j))*(n:ℝ)) := by
    rw [measureReal_prod_prod]
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one]
    exact shifted_goe_diagonal_tail hj hδ hn hmean
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add hp hD))

theorem zero_diagonal_fixed_time_root_stability {j T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hT : 0 < T) :
    ∃ A K ε c ρ a : ℝ, 1 < A ∧ 2*sqrt j < K ∧ sqrt j*A < 1 ∧
      0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ, 0 < N ∧
      ∀ n ≥ N, ∀ t∈Icc 0 T,
      ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
       (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
        (erasedPlantedRootBad n j A K ε c ρ t) ≤ exp (-a*(n:ℝ)) := by
  obtain ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,N,hN,hp⟩ :=
    planted_fixed_time_root_stability hj hj1 hT
  let δ := min ((K-2*sqrt j)/2) (min (ρ/2) (c/(2*A)))
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (half_pos hρ) (by positivity))
  have hδK : δ ≤ (K-2*sqrt j)/2 := min_le_left _ _
  have hδρ : δ ≤ ρ/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδc' : δ ≤ c/(2*A) := (min_le_right _ _).trans (min_le_right _ _)
  have hδc : A*δ ≤ c/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*A)).mp hδc'
    nlinarith
  let b := δ^2/(32*j)
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨Nd,hNd⟩ := absorb_linear_exponential hb
  obtain ⟨Nm,hNm⟩ := exists_nat_ge (2*j/δ)
  obtain ⟨r,hr,Nr,hNr⟩ := two_exponential_tails ha (half_pos hb)
  refine ⟨A,K-δ,ε,c/2,ρ/2,r,hA,by linarith,hsub,hε,half_pos hc,half_pos hρ,hr,
    max N (max Nd (max Nm Nr)),hN.trans_le (le_max_left _ _),?_⟩
  intro n hn t ht
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnD : Nd ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnM : Nm ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnR : Nr ≤ n := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn0 : 0 < n := hN.trans_le hnN
  have hmean : j/(n:ℝ) ≤ δ/2 := by
    have hh := (div_le_iff₀ hδ).mp (hNm.trans (Nat.cast_le.mpr hnM))
    apply (div_le_iff₀ (Nat.cast_pos.mpr hn0)).mpr
    nlinarith
  have hh := erased_planted_probability hj hA0.le hδ hn0 hδρ hδc hmean (hp n hnN t ht)
  apply hh.trans
  apply (add_le_add_right (hNd n hnD) _).trans
  exact (by nlinarith only [exp_pos (-a*(n:ℝ))] :
    exp (-a*(n:ℝ))+exp (-(b/2)*(n:ℝ)) ≤
      4*exp (-a*(n:ℝ))+exp (-(b/2)*(n:ℝ))).trans (hNr n hnR)
end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TAPGauge
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

lemma spinAct_involutive {n : ℕ} (s : Spin n) (y : Field n) : spinAct s (spinAct s y)=y := by
  ext i
  simp only [spinAct,← mul_assoc,← sq,spinValue_sq,one_mul]

lemma spinAct_tanh {n : ℕ} (s : Spin n) (y : Field n) :
    magnetization (spinAct s y)=spinAct s (magnetization y) := by
  ext i
  cases h : s i <;> simp [magnetization,spinAct,spinValue,h,tanh_neg]

lemma spinAct_overlap {n : ℕ} (s : Spin n) (y : Field n) : overlap (spinAct s y)=overlap y := by
  unfold overlap
  rw [spinAct_tanh]
  simp only [spinAct,mul_pow,spinValue_sq,one_mul]

lemma spinAct_variance {n : ℕ} (s : Spin n) (y : Field n) :
    spinVariance (spinAct s y)=spinVariance y := by
  ext i
  simp only [spinVariance,spinAct_tanh,spinAct,mul_pow,spinValue_sq,one_mul]

lemma spinAct_sqnorm {n : ℕ} (s : Spin n) (y : Field n) : vectorSqNorm (spinAct s y)=vectorSqNorm y := by
  simp only [vectorSqNorm,spinAct,mul_pow,spinValue_sq,one_mul]

lemma spinAct_norm {n : ℕ} (s : Spin n) (y : Field n) : vectorNorm (spinAct s y)=vectorNorm y := by
  have hh : vectorNorm (spinAct s y)^2=vectorNorm y^2 := by
    rw [vectorNorm_sq,vectorNorm_sq,spinAct_sqnorm]
  nlinarith only [hh,vectorNorm_nonneg (spinAct s y),vectorNorm_nonneg y]

lemma spinAct_quadratic {n : ℕ} (s : Spin n) (J : Matrix (Fin n) (Fin n) ℝ) (y : Field n) :
    quadraticForm (spinMatrixAct s J) (spinAct s y)=quadraticForm J y := by
  unfold quadraticForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [spinMatrixAct,spinAct]
  calc
    _ = spinValue (s i)^2*spinValue (s k)^2*(y i*J i k*y k) := by ring
    _ = _ := by rw [spinValue_sq,spinValue_sq,one_mul,one_mul]

lemma spinAct_tap {n : ℕ} (s : Spin n) (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    tapField j (spinMatrixAct s J) (spinAct s h) (spinAct s y)=spinAct s (tapField j J h y) := by
  ext i
  simp only [tapField,spinAct_tanh,onsager,spinAct_overlap,spinAct,spinMatrixAct]
  have hs : (∑ k, spinValue (s i)*J i k*spinValue (s k)*(spinValue (s k)*magnetization y k))=
      spinValue (s i)*∑ k,J i k*magnetization y k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    calc
      _ = spinValue (s i)*(J i k*magnetization y k)*spinValue (s k)^2 := by ring
      _ = _ := by rw [spinValue_sq,mul_one]
  rw [hs]
  ring

lemma spinAct_hessian {n : ℕ} (s : Spin n) (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (y a : Field n) :
    fieldHessian j (spinMatrixAct s J) (spinAct s y) a=spinMatrixAct s (fieldHessian j J y a) := by
  ext i k
  simp only [fieldHessian,hessianCore,onsager,spinAct_overlap,spinAct_tanh,spinAct,spinMatrixAct]
  by_cases hik : i=k
  · subst k
    cases hi : s i <;> simp [spinValue]
  · simp only [ite_eq_right hik]
    ring

lemma spinAct_bad {n : ℕ} (s : Spin n) (j A ε c ρ : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    rootBad j A ε c ρ J h → rootBad j A ε c ρ (spinMatrixAct s J) (spinAct s h) := by
  rintro ⟨y,hy,a,ha,hd,x,hx,hq⟩
  let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (spinAct s x.ofLp)
  have hz : ‖z‖=1 := by
    change vectorNorm (spinAct s x.ofLp)=1
    rw [spinAct_norm]
    exact hx
  refine ⟨spinAct s y,?_,a,ha,?_,z,hz,?_⟩
  · rw [spinAct_tap,spinAct_norm]
    exact hy
  · rw [spinAct_variance]
    exact hd
  · rw [spinAct_hessian]
    exact (spinAct_quadratic s (fieldHessian j J y a) x.ofLp).trans_le hq
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_GaugeStabilityLaw
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
attribute [local instance] OAI.SKGap.ObservationBridge.matrixMeasurable
local instance matrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma isClosed_operatorBound (K : ℝ) : IsClosed {J : Matrix (Fin n) (Fin n) ℝ | operatorBound K J} := by
  have he : {J : Matrix (Fin n) (Fin n) ℝ | operatorBound K J} =
      ⋂ z : Field n,{J | vectorNorm (J*ᵥz) ≤ K*vectorNorm z} := by ext J; simp [operatorBound]
  rw [he]
  apply isClosed_iInter
  intro z
  exact isClosed_le ((continuous_vectorNorm n).comp (by unfold Matrix.mulVec; fun_prop)) continuous_const

lemma measurableSet_literalBadPair (j A K ε c ρ : ℝ) :
    MeasurableSet (literalBadPair (n:=n) j A K ε c ρ) :=
  ((isClosed_operatorBound K).measurableSet.preimage measurable_fst).inter
    (measurableSet_rootBad j A ε c ρ)

lemma spinMatrixAct_involutive (s : Spin n) (J : Matrix (Fin n) (Fin n) ℝ) :
    spinMatrixAct s (spinMatrixAct s J)=J := by
  ext i k
  dsimp [spinMatrixAct]
  calc
    _ = (spinValue (s i))^2*(spinValue (s k))^2*J i k := by ring
    _ = _ := by rw [spinValue_sq,spinValue_sq,one_mul,one_mul]

lemma spinMatrixAct_mulVec (s : Spin n) (J : Matrix (Fin n) (Fin n) ℝ) (z : Field n) :
    spinMatrixAct s J*ᵥspinAct s z=spinAct s (J*ᵥz) := by
  ext i
  simp only [Matrix.mulVec,dotProduct,spinMatrixAct,spinAct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = spinValue (s i)*(J i k*z k)*(spinValue (s k))^2 := by ring
    _ = _ := by rw [spinValue_sq,mul_one]

lemma operatorBound_spin_iff (s : Spin n) (K : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) :
    operatorBound K (spinMatrixAct s J) ↔ operatorBound K J := by
  have htrans (J : Matrix (Fin n) (Fin n) ℝ) (hJ : operatorBound K J) :
      operatorBound K (spinMatrixAct s J) := by
    intro z
    have hh := hJ (spinAct s z)
    have he := spinMatrixAct_mulVec s J (spinAct s z)
    rw [spinAct_involutive] at he
    rw [he,spinAct_norm]
    simpa only [spinAct_norm] using hh
  exact ⟨fun h=>by simpa only [spinMatrixAct_involutive] using htrans _ h,htrans _⟩

lemma literalBadPair_spin_iff (s : Spin n) (j A K ε c ρ : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    (spinMatrixAct s J,spinAct s h)∈literalBadPair j A K ε c ρ ↔
      (J,h)∈literalBadPair j A K ε c ρ := by
  change (operatorBound K (spinMatrixAct s J) ∧ rootBad j A ε c ρ (spinMatrixAct s J) (spinAct s h)) ↔ _
  rw [operatorBound_spin_iff]
  refine and_congr_right (fun _=>⟨fun hh=>?_,spinAct_bad s j A ε c ρ J h⟩)
  simpa only [spinMatrixAct_involutive,spinAct_involutive] using
    spinAct_bad s j A ε c ρ (spinMatrixAct s J) (spinAct s h) hh

lemma gaussianSign_variance_preserving {κ : Type*} [Fintype κ]
    (q : κ→ℝ) (hq : ∀ i,q i^2=1) (v : ℝ≥0) :
    MeasurePreserving (gaussianSignEquiv q hq)
      (Measure.pi (fun _ : κ=>gaussianReal 0 v)) (Measure.pi (fun _ : κ=>gaussianReal 0 v)) := by
  refine ⟨(gaussianSignEquiv q hq).measurable,?_⟩
  have he (i : κ) : (gaussianReal 0 v).map (fun x=>q i*x)=gaussianReal 0 v := by
    rcases sq_eq_one_iff.mp (hq i) with h|h
    · simp [h]
    · simpa only [h,neg_one_mul,neg_zero] using (gaussianReal_map_neg (μ:=(0:ℝ)) (v:=v))
  change (Measure.pi (fun _ : κ=>gaussianReal 0 v)).map (fun g i=>q i*g i)=_
  rw [Measure.pi_map_pi (fun _=>by fun_prop)]
  simp only [he]

lemma coupling_planted_gauge (s : Spin n) (r : ℝ) (g : Disorder n) :
    spinMatrixAct s (coupling (plantedEdges r s g)) =
      coupling (plusPlantedEdges r (gaussianSignEquiv (edgeSpinSign s) (edgeSpinSign_sq s) g)) := by
  ext i k
  unfold spinMatrixAct coupling
  split_ifs with h h
  · dsimp [plantedEdges,plusPlantedEdges,gaussianSignEquiv,edgeSpinSign]
    calc
      _ = sqrt r*(spinValue (s i)*spinValue (s k)*g ⟨(i,k),h⟩)+r*(spinValue (s i))^2*(spinValue (s k))^2 := by ring
      _ = _ := by rw [spinValue_sq,spinValue_sq,mul_one,mul_one]; rfl
  · dsimp [plantedEdges,plusPlantedEdges,gaussianSignEquiv,edgeSpinSign]
    calc
      _ = sqrt r*(spinValue (s k)*spinValue (s i)*g ⟨(k,i),h⟩)+r*(spinValue (s i))^2*(spinValue (s k))^2 := by ring
      _ = _ := by rw [spinValue_sq,spinValue_sq,mul_one,mul_one]; rfl
  · simp

lemma spin_observation (s : Spin n) (t : ℝ) (b : Field n) :
    spinAct s (fun i=>t*spinValue (s i)+b i)=(fun i=>t+spinAct s b i) := by
  ext i
  dsimp [spinAct]
  calc
    _ = t*(spinValue (s i))^2+spinValue (s i)*b i := by ring
    _ = _ := by rw [spinValue_sq,mul_one]

lemma continuous_coupling : Continuous (coupling (n:=n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  unfold coupling
  split_ifs <;> fun_prop

theorem gauged_fixed_time_probability (s : Spin n) (r j A K ε c ρ t : ℝ) :
    ((gaussianCoordinates (Edge n)).prod (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      {p | (coupling (plantedEdges r s p.1),(fun i=>t*spinValue (s i)+p.2 i))∈literalBadPair j A K ε c ρ} =
    ((gaussianCoordinates (Edge n)).prod (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      {p | (coupling (plusPlantedEdges r p.1),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ} := by
  let V := gaussianSignEquiv (edgeSpinSign s) (edgeSpinSign_sq s)
  let W := gaussianSignEquiv (fun i=>spinValue (s i)) (fun i=>spinValue_sq (s i))
  have hV := gaussianSign_variance_preserving (edgeSpinSign s) (edgeSpinSign_sq s) 1
  have hW := gaussianSign_variance_preserving (fun i=>spinValue (s i)) (fun i=>spinValue_sq (s i)) t.toNNReal
  have hm := hV.prod hW
  let E := {p : Disorder n × Field n |
    (coupling (plusPlantedEdges r p.1),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ}
  have hmap : Continuous (fun p : Disorder n × Field n =>
      ((coupling (plusPlantedEdges r p.1)),(fun i=>t+p.2 i)) :
      Disorder n × Field n → Matrix (Fin n) (Fin n) ℝ × Field n) :=
    (continuous_coupling.comp (by unfold plusPlantedEdges;fun_prop)).prodMk (by fun_prop)
  have hmmap : Measurable (fun p : Disorder n × Field n =>
      ((coupling (plusPlantedEdges r p.1)),(fun i=>t+p.2 i)) :
      Disorder n × Field n → Matrix (Fin n) (Fin n) ℝ × Field n) := hmap.measurable
  have hE : MeasurableSet E := (measurableSet_literalBadPair j A K ε c ρ).preimage hmmap
  have he : {p : Disorder n × Field n |
    (coupling (plantedEdges r s p.1),(fun i=>t*spinValue (s i)+p.2 i))∈literalBadPair j A K ε c ρ} =
      (Prod.map V W) ⁻¹' E := by
    ext p
    change _ ↔ (coupling (plusPlantedEdges r (V p.1)),fun i=>t+W p.2 i)∈literalBadPair j A K ε c ρ
    have hh := literalBadPair_spin_iff s j A K ε c ρ
      (coupling (plantedEdges r s p.1)) (fun i=>t*spinValue (s i)+p.2 i)
    rw [coupling_planted_gauge,spin_observation] at hh
    exact hh.symm
  rw [he]
  exact hm.measure_preimage hE.nullMeasurableSet
end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PlantedMarginalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
attribute [local instance] OAI.SKGap.ObservationBridge.marginalMatrixMeasurable
local instance marginalMatrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma continuous_goeEdges (r : ℝ) : Continuous (goeEdges (n:=n) r) := by
  apply continuous_pi
  intro e
  unfold goeEdges goeMatrix
  fun_prop
lemma goeEdges_gaussian (r : ℝ) :
    HasGaussianLaw (goeEdges (n:=n) r) (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
  let L : ((Fin n×Fin n)→ℝ)→L[ℝ] Disorder n :=
    ContinuousLinearMap.pi (fun e=>ContinuousLinearMap.proj e.1)
  exact (goe_matrix_gaussian r).map L
lemma goeEdges_hasLaw {r : ℝ} (hr : 0 ≤ r) (e : Edge n) :
    HasLaw (fun g : MatrixCoordinates (Fin n)→ℝ=>goeEdges r g e)
      (gaussianReal 0 r.toNNReal) (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
  have hg := (goeEdges_gaussian (n:=n) r).eval e
  refine ⟨hg.aemeasurable,?_⟩
  have hm : (∫ g,goeEdges r g e ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=0 :=
    goe_mean_zero r e.1.1 e.1.2
  rw [hg.map_eq_gaussianReal,hm,← covariance_self hg.aemeasurable]
  change gaussianReal 0 (cov[fun g=>goeMatrix r g e.1.1 e.1.2,
      fun g=>goeMatrix r g e.1.1 e.1.2; gaussianCoordinates (MatrixCoordinates (Fin n))]).toNNReal = _
  rw [goe_entry_cov hr]
  have hne := ne_of_lt e.property
  simp [hne,hne.symm]
lemma goeEdges_independent {r : ℝ} (hr : 0 ≤ r) :
    iIndepFun (fun e : Edge n=>fun g=>goeEdges r g e)
      (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
  apply (goeEdges_gaussian (n:=n) r).iIndepFun_of_covariance_eq_zero
  intro e f hef
  change cov[fun g=>goeMatrix r g e.1.1 e.1.2,
    fun g=>goeMatrix r g f.1.1 f.1.2; gaussianCoordinates (MatrixCoordinates (Fin n))]=0
  rw [goe_entry_cov hr]
  have h1 : ¬(e.1.1=f.1.1 ∧ e.1.2=f.1.2) := by
    intro h; apply hef; exact Subtype.ext (Prod.ext h.1 h.2)
  have h2 : ¬(e.1.1=f.1.2 ∧ e.1.2=f.1.1) := by
    intro h
    have he := e.property
    have hf := f.property
    simp only [h.1,h.2] at he
    exact (not_lt_of_ge hf.le) he
  split_ifs <;> simp_all

theorem measurePreserving_goeEdges {r : ℝ} (hr : 0 ≤ r) :
    MeasurePreserving (goeEdges (n:=n) r)
      (gaussianCoordinates (MatrixCoordinates (Fin n)))
      (Measure.pi (fun _ : Edge n=>gaussianReal 0 r.toNNReal)) := by
  refine ⟨(continuous_goeEdges _).measurable,?_⟩
  rw [iIndepFun.map_fun_eq_pi_map (fun e=>(goeEdges_hasLaw hr e).aemeasurable)
    (goeEdges_independent hr)]
  exact congrArg Measure.pi (funext fun e=>(goeEdges_hasLaw hr e).map_eq)

lemma measurePreserving_scaled_edges {r : ℝ} (hr : 0 ≤ r) :
    MeasurePreserving (fun g : Disorder n=>fun e=>sqrt r*g e)
      (gaussianCoordinates (Edge n)) (Measure.pi (fun _ : Edge n=>gaussianReal 0 r.toNNReal)) := by
  refine ⟨by fun_prop,?_⟩
  change (Measure.pi (fun _ : Edge n=>gaussianReal 0 1)).map (fun g e=>sqrt r*g e)=_
  rw [Measure.pi_map_pi (fun _=>by fun_prop)]
  apply congrArg Measure.pi
  funext e
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    change (sqrt r)^2*1=↑r.toNNReal
    rw [mul_one,sq_sqrt hr,coe_toNNReal _ hr]

lemma coupling_shifted_goe (j : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) :
    coupling (fun e=>goeEdges (j/(n:ℝ)) g e+j/(n:ℝ)) =
      eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) := by
  ext i k
  by_cases hik : i < k
  · have hne := ne_of_lt hik
    simp [coupling,hik,goeEdges,eraseDiagonal,plantedInteraction,hne,Matrix.vecMulVec]
  · by_cases hki : k < i
    · have hne := ne_of_lt hki
      simp [coupling,hik,hki,goeEdges,eraseDiagonal,plantedInteraction,hne.symm,
        Matrix.vecMulVec,goeMatrix,add_comm]
    · have he : i=k := le_antisymm (le_of_not_gt hki) (le_of_not_gt hik)
      subst k
      simp [coupling,eraseDiagonal]

theorem plus_planted_marginal_probability {j : ℝ} (hj : 0≤j) (A K ε c ρ t : ℝ) :
    ((gaussianCoordinates (Edge n)).prod (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      {p | (coupling (plusPlantedEdges (j/(n:ℝ)) p.1),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ} =
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      (erasedPlantedRootBad n j A K ε c ρ t) := by
  let r := j/(n:ℝ)
  have hr : 0 ≤ r := div_nonneg hj (Nat.cast_nonneg _)
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let E := {p : Disorder n × Field n |
    (coupling (fun e=>p.1 e+r),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ}
  have hmap : Continuous (fun p : Disorder n × Field n=>
      (coupling (fun e=>p.1 e+r),(fun i=>t+p.2 i)) :
      Disorder n × Field n → Matrix (Fin n) (Fin n) ℝ × Field n) :=
    (continuous_coupling.comp (by fun_prop)).prodMk (by fun_prop)
  have hmmap : Measurable (fun p : Disorder n × Field n=>
      (coupling (fun e=>p.1 e+r),(fun i=>t+p.2 i)) :
      Disorder n × Field n → Matrix (Fin n) (Fin n) ℝ × Field n) := hmap.measurable
  have hE : MeasurableSet E := (measurableSet_literalBadPair j A K ε c ρ).preimage hmmap
  have h1 := ((measurePreserving_scaled_edges (n:=n) hr).prod (MeasurePreserving.id ν)).measure_preimage hE.nullMeasurableSet
  have h2 := ((measurePreserving_goeEdges (n:=n) hr).prod (MeasurePreserving.id ν)).measure_preimage hE.nullMeasurableSet
  calc
    _ = _ := h1
    _ = ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod ν)
        ((Prod.map (goeEdges r) id) ⁻¹' E) := h2.symm
    _ = _ := by
      congr 1
      ext p
      change (coupling (fun e=>goeEdges r p.1 e+r),fun i=>t+p.2 i)∈literalBadPair j A K ε c ρ ↔ _
      rw [coupling_shifted_goe]
      rfl
end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PlantedTilt
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal

lemma scaled_weight_eq {n : ℕ} (r : ℝ) (x : Spin n) (g : Disorder n) :
    weight (fun e=>sqrt r*g e) 0 x=exp (∑ e,edgeCoefficient r x e*g e) := by
  unfold weight
  rw [edge_energy_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  unfold edgeCoefficient
  ring

lemma scaled_spin_weight_measurable {n : ℕ} (r : ℝ) (x : Spin n) :
    Measurable (fun g : Disorder n=>weight (fun e=>sqrt r*g e) 0 x) := by
  simp_rw [scaled_weight_eq]
  fun_prop

lemma scaled_spin_mass_measurable {n : ℕ} (r : ℝ) (x : Spin n) :
    Measurable (fun g : Disorder n=>mass (fun e=>sqrt r*g e) 0 x) :=
  (scaled_spin_weight_measurable r x).div ((partition_zero_measurable n).comp (by fun_prop))

lemma partition_mass_normalized {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (g : Disorder n) (x : Spin n) :
    gaussianSpinPartition n r g/(∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n))*
      mass (fun e=>sqrt r*g e) 0 x =
      (1/(Fintype.card (Spin n):ℝ))*
      exp ((∑ e,edgeCoefficient r x e*g e)-(∑ e,edgeCoefficient r x e^2)/2) := by
  rw [gaussianSpinPartition_integral hr,edgeCoefficient_sq_sum hr]
  rw [mass,← gaussianSpinPartition_eq_partition,scaled_weight_eq,exp_sub]
  have hp := gaussianSpinPartition_pos n r g
  have hc : (Fintype.card (Spin n):ℝ) ≠ 0 := by positivity
  field_simp

theorem planted_joint_tilt {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (F : Spin n→Disorder n→ℝ≥0∞) (hF : ∀ x,Measurable (F x)) :
    (∫⁻ g, ENNReal.ofReal (gaussianSpinPartition n r g/
      (∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n)))*
      ∑ x,ENNReal.ofReal (mass (fun e=>sqrt r*g e) 0 x)*F x (fun e=>sqrt r*g e)
      ∂gaussianCoordinates (Edge n)) =
    ENNReal.ofReal (1/(Fintype.card (Spin n):ℝ))*∑ x : Spin n,
      ∫⁻ g,F x (fun e=>sqrt r*g e+r*spinValue (x e.1.1)*spinValue (x e.1.2))
        ∂gaussianCoordinates (Edge n) := by
  have hM : 0 < ∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n) :=
    gaussianSpinPartition_mean_pos hr
  simp_rw [Finset.mul_sum,← mul_assoc,← ENNReal.ofReal_mul (div_nonneg
    (gaussianSpinPartition_pos n r _).le hM.le),partition_mass_normalized hr,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/(Fintype.card (Spin n):ℝ)),mul_assoc]
  rw [lintegral_finsetSum _ (fun x _=>by fun_prop)]
  apply Finset.sum_congr rfl
  intro x _
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [gaussian_tilt_lintegral (edgeCoefficient r x) (fun g : Disorder n=>F x (fun e=>sqrt r*g e)) ((hF x).comp (by fun_prop))]
  apply lintegral_congr
  intro g
  congr 1
  ext e
  unfold edgeCoefficient
  calc
    _ = sqrt r*g e+(sqrt r)^2*(spinValue (x e.1.1)*spinValue (x e.1.2)) := by ring
    _ = _ := by rw [sq_sqrt hr]

theorem planted_disorder_joint_tilt {n : ℕ} (β : ℝ)
    (F : Spin n→Disorder n→ℝ≥0∞) (hF : ∀ x,Measurable (F x)) :
    (∫⁻ J,ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
      ∑ x,ENNReal.ofReal (mass J 0 x)*F x J ∂disorderLaw β n)=
    ENNReal.ofReal (1/(Fintype.card (Spin n):ℝ))*∑ x : Spin n,
      ∫⁻ g,F x (fun e=>sqrt (β^2/(n:ℝ))*g e+(β^2/(n:ℝ))*spinValue (x e.1.1)*spinValue (x e.1.2))
        ∂gaussianCoordinates (Edge n) := by
  have hmass (x : Spin n) : Measurable (fun J : Disorder n=>mass J 0 x) := by
    simpa only [sqrt_one,one_mul] using scaled_spin_mass_measurable 1 x
  have hi : Measurable (fun J : Disorder n=>
      ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
        ∑ x,ENNReal.ofReal (mass J 0 x)*F x J) :=
    ((partition_zero_measurable n).div_const _).ennreal_ofReal.mul
      (Finset.measurable_sum _ (fun x _=>(hmass x).ennreal_ofReal.mul (hF x)))
  rw [← (gaussian_disorder_hasLaw β n).lintegral_comp hi.aemeasurable]
  simpa only [disorder_partition_mean,← gaussianSpinPartition_eq_partition] using
    planted_joint_tilt (n:=n) (r:=β^2/(n:ℝ)) (by positivity) F hF
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FixedTimeAnnealed
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
attribute [local instance] OAI.SKGap.ObservationBridge.annealedMatrixMeasurable
local instance annealedMatrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma measurableSet_gibbsObservationBad (j A K ε c ρ t : ℝ) (s : Spin n) :
    MeasurableSet (gibbsObservationBad j A K ε c ρ t s) := by
  have hmap : Continuous (fun p : Disorder n × Field n=>
      (coupling p.1,(fun i=>t*spinValue (s i)+p.2 i)) :
      Disorder n × Field n→Matrix (Fin n) (Fin n) ℝ × Field n) :=
    (continuous_coupling.comp continuous_fst).prodMk (by fun_prop)
  have hmmap : Measurable (fun p : Disorder n × Field n=>
      (coupling p.1,(fun i=>t*spinValue (s i)+p.2 i)) :
      Disorder n × Field n→Matrix (Fin n) (Fin n) ℝ × Field n) := hmap.measurable
  exact (measurableSet_literalBadPair j A K ε c ρ).preimage hmmap

lemma measurable_conditionalSpinFailure (j A K ε c ρ t : ℝ) (s : Spin n) :
    Measurable (conditionalSpinFailure j A K ε c ρ t s) :=
  measurable_measure_prodMk_left (measurableSet_gibbsObservationBad j A K ε c ρ t s)

lemma planted_spin_failure_integral (s : Spin n) (r j A K ε c ρ t : ℝ) :
    (∫⁻ g : Disorder n,conditionalSpinFailure j A K ε c ρ t s (plantedEdges r s g)
      ∂gaussianCoordinates (Edge n)) =
    ((gaussianCoordinates (Edge n)).prod (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      {p | (coupling (plusPlantedEdges r p.1),(fun i=>t+p.2 i))∈literalBadPair j A K ε c ρ} := by
  let E := (Prod.map (plantedEdges r s) id) ⁻¹' gibbsObservationBad j A K ε c ρ t s
  have hE : MeasurableSet E := (measurableSet_gibbsObservationBad j A K ε c ρ t s).preimage
    ((show Measurable (plantedEdges r s) by unfold plantedEdges;fun_prop).prodMap measurable_id)
  have he := Measure.prod_apply (μ:=gaussianCoordinates (Edge n))
      (ν:=Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)) hE
  exact he.symm.trans (gauged_fixed_time_probability s r j A K ε c ρ t)

theorem fixed_time_size_bias_identity (β A K ε c ρ t : ℝ) :
    (∫⁻ J : Disorder n,
      ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
        fixedTimeFailureENN (β^2) A K ε c ρ t J ∂disorderLaw β n) =
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      (erasedPlantedRootBad n (β^2) A K ε c ρ t) := by
  rw [show fixedTimeFailureENN (n:=n) (β^2) A K ε c ρ t =
    (fun J=>∑ s,ENNReal.ofReal (mass J 0 s)*conditionalSpinFailure (β^2) A K ε c ρ t s J) from rfl]
  rw [planted_disorder_joint_tilt β _ (fun s=>measurable_conditionalSpinFailure (β^2) A K ε c ρ t s)]
  have he (s : Spin n) :
    (∫⁻ g : Disorder n,conditionalSpinFailure (β^2) A K ε c ρ t s
      (fun e=>sqrt (β^2/(n:ℝ))*g e+β^2/(n:ℝ)*spinValue (s e.1.1)*spinValue (s e.1.2))
      ∂gaussianCoordinates (Edge n)) =
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)))
      (erasedPlantedRootBad n (β^2) A K ε c ρ t) :=
    (planted_spin_failure_integral s _ _ _ _ _ _ _ _).trans
      (plus_planted_marginal_probability (sq_nonneg β) A K ε c ρ t)
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc]
  have hc : (Fintype.card (Spin n):ℝ) ≠ 0 := by positivity
  have hh : ENNReal.ofReal (1/(Fintype.card (Spin n):ℝ))*(Fintype.card (Spin n):ℝ≥0∞)=1 := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity : (0:ℝ)≤1/(Fintype.card (Spin n):ℝ))]
    simp
  rw [hh,one_mul]

theorem annealed_fixed_time_root_stability_oai {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
    ∃ A K ε c ρ a : ℝ, 1<A ∧ 2*β<K ∧ β*A<1 ∧
      0<ε ∧ 0 < c ∧ 0<ρ ∧ 0<a ∧ ∃ N : ℕ, 0<N ∧ ∀ n≥N, ∀ t∈Icc 0 T,
      (∫⁻ J : Disorder n,
        ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
          fixedTimeFailureENN (β^2) A K ε c ρ t J ∂disorderLaw β n) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,N,hN,hp⟩ :=
    zero_diagonal_fixed_time_root_stability (sq_pos_of_pos hβ) (by nlinarith : β^2<1) hT
  rw [sqrt_sq hβ.le] at hK hsub
  refine ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,N,hN,?_⟩
  intro n hn t ht
  rw [fixed_time_size_bias_identity,← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hp n hn t ht)
end SKGap.ObservationBridge

end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability_oai := @OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability_oai
