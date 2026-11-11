-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:05.27321+00:00
-- url     : https://prove2.me/submissions/85e6e808-84cd-492e-80f6-84c3f289e49c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc013
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalGauge_unitary
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryFrame
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame

lemma J_inner (u v : V) : ⟪J u, J v⟫ = ⟪u, v⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, J]
  ring

lemma inner_self_J (v : V) : ⟪v, J v⟫ = 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, J]
  ring

lemma wedge_inner (u v a b : V) :
    ⟪wedge u v, wedge a b⟫ = ⟪u, a⟫ * ⟪v, b⟫ - ⟪u, b⟫ * ⟪v, a⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, wedge]
  ring

lemma fundamental_norm_sq : ‖fundamental‖ ^ 2 = 2 := by
  first | (simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, fundamental]; all_goals first | (norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, fundamental]; done) | rfl | decide) | (norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, fundamental]; done) | norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, fundamental]

lemma line_selfDualPart (v : V) : selfDualPart (line v) =
    (‖v‖ ^ 2 / 2) • fundamental := by
  rw [EuclideanSpace.real_norm_sq_eq]
  ext i
  fin_cases i <;>
    simp [selfDualPart, line, wedge, J, star, fundamental,
      Fin.sum_univ_succ] <;> ring

lemma line_norm_sq (v : V) : ‖line v‖ ^ 2 = (‖v‖ ^ 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, line, wedge_inner, J_inner, inner_self_J,
    zero_mul, sub_zero, real_inner_self_eq_norm_sq]
  ring

lemma unit_line_norm {v : V} (hv : ‖v‖ = 1) : ‖line v‖ = 1 := by
  have hs := line_norm_sq v
  rw [hv] at hs
  nlinarith [norm_nonneg (line v)]

lemma unit_line_selfDualPart {v : V} (hv : ‖v‖ = 1) :
    selfDualPart (line v) = (1 / 2 : ℝ) • fundamental := by
  rw [line_selfDualPart, hv]
  norm_num

theorem angular_identity (a b F G : W)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hF : ‖F‖ ^ 2 = 2) (hG : ‖G‖ ^ 2 = 2)
    (haF : selfDualPart a = (1 / 2 : ℝ) • F)
    (hbG : selfDualPart b = (1 / 2 : ℝ) • G) :
    ⟪a, star b⟫ = (1 / 2 : ℝ) * ‖a - b‖ ^ 2 -
      (1 / 4 : ℝ) * ‖F - G‖ ^ 2 := by
  have hp : ⟪F, G⟫ = 2 * (⟪a, b⟫ + ⟪a, star b⟫) := by
    have h := congrArg₂ (fun x y : W => ⟪x, y⟫) haF hbG
    dsimp [selfDualPart] at h
    simp only [real_inner_smul_left, real_inner_smul_right,
      inner_add_left, inner_add_right, star_self_adjoint, star_square] at h
    linarith
  rw [norm_sub_sq_real, norm_sub_sq_real, ha, hb, hF, hG]
  linarith

end TamingCompatibility.UnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets

open Filter
open scoped ContDiff Topology
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma slice_fderiv_contDiffAt (F : P × V → W) {x : P × V}
    (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y : P × V => fderiv ℝ (fun z => F (y.1,z)) y.2) x := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
    ((hF.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)).mono
      fun y hy => hy.differentiableAt (by norm_num)
  apply (dpos_contDiffAt F x hF).congr_of_eventuallyEq
  filter_upwards [hd] with y hy
  exact (dpos_eq_at F y.1 y.2 hy).symm

end TamingCompatibility.GeometricHilbert.UniformJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus

section MatrixFamilies
open UniformJets
open scoped ContDiff
variable {P V W Q ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma firstMatrix_joint (e : ι → V) (a : ι → P × V → W →L[ℝ] Q)
    (b : P × V → W →L[ℝ] Q) (ρ : P × V → ℝ) {x : P × V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) (j : ι) :
    ContDiffAt ℝ ∞ (fun y : P × V => firstMatrix e (fun i z => a i (y.1,z))
      (fun z => b (y.1,z)) (fun z => ρ (y.1,z)) j y.2) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hp (i : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      principalMatrix (fun k z => a k (y.1,z)) (fun z => ρ (y.1,z)) i j y.2) x :=
    (S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp (ha j)
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    (slice_fderiv_contDiffAt _ (hp i)).clm_apply (contDiffAt_const (c := e i)))
  exact (((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp (ha j))).sub
      ((S.contDiff.contDiffAt.comp x (ha j)).clm_comp hb)

end MatrixFamilies
open UniformJets FirstJetGauge OrthogonalJets
open scoped ContDiff
variable {P V W ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gauge_joint (q : ι → V →L[ℝ] ℝ) (b : ι → P → W →L[ℝ] W)
    {x : P × V} (hb : ∀ i, ContDiffAt ℝ ∞ (b i) x.1) :
    ContDiffAt ℝ ∞ (fun y : P × V => gauge (halfJet q (fun i => b i y.1)) y.2) x := by
  have he : ContDiffAt ℝ ∞ (NormedSpace.exp : (W →L[ℝ] W) → (W →L[ℝ] W))
      (halfJet q (fun i => b i x.1) x.2) := (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  apply he.comp x
  simp only [halfJet, sum_apply, ContinuousLinearMap.smulRight_apply]
  exact ContDiffAt.sum fun i _ =>
    ((q i).contDiff.contDiffAt.comp x contDiffAt_snd).smul
      (((hb i).comp x contDiffAt_fst).const_smul (1/2 : ℝ))

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_complexLine (J : AlmostComplexStructure X) (β : TwoForm X) (p : X)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback β (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      eval β ((extChartAt Model p).symm y) (mfderiv Model Model (extChartAt Model p).symm y v)
        (J.endomorphism _ (mfderiv Model Model (extChartAt Model p).symm y v)) := by
  have hi := coordinateJ_intertwine J p hy v
  change (inverseChartEquiv p y hy).toContinuousLinearMap (coordinateJ J p y v) =
    J.endomorphism _ ((inverseChartEquiv p y hy).toContinuousLinearMap v) at hi
  rw [inverseChartEquiv_coe] at hi
  change β _ ((mfderiv Model Model (extChartAt Model p).symm y) ∘ ![v,coordinateJ J p y v]) = _
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact hi

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelGammaBounds
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open _root_.MeasureTheory Set

lemma rapidConstant_pos {c : ℝ} (hc : 0 < c) (N : ℕ) :
    0 < rapidConstant c N := by
  unfold rapidConstant
  positivity

lemma exp_neg_le_rapid {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (N : ℕ) :
    Real.exp (-c*a) ≤ rapidConstant c N / (1+a)^N := by
  have hpa : 0 < (1+a)^N := pow_pos (by linarith) _
  have hpc : 0 < c^N := pow_pos hc _
  have hf : 0 < (N.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (c*(1+a)) (by positivity) N)
  apply (le_div_iff₀ hpa).mpr
  apply (le_div_iff₀ hpc).mpr
  calc
    Real.exp (-c*a) * (1+a)^N * c^N = (c*(1+a))^N * Real.exp (-c*a) := by
      rw [mul_pow]; ring
    _ ≤ ((N.factorial : ℝ) * Real.exp (c*(1+a))) * Real.exp (-c*a) :=
      mul_le_mul_of_nonneg_right (by simpa only [mul_comm] using hp) (Real.exp_pos _).le
    _ = (N.factorial : ℝ) * Real.exp c := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

lemma moment_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s^n * Real.exp (-(b*s))) (Ioi 0) := by
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hb)

lemma moment_integral (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ s : ℝ in Ioi 0, s^n * Real.exp (-(b*s))) = moment n b := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1)
    (by positivity) hb
  simp_rw [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  have he : (n:ℝ)+1 = ((n+1:ℕ):ℝ) := by push_cast; rfl
  rw [he, Real.rpow_natCast] at h
  exact h

lemma moment_pos (n : ℕ) {b : ℝ} (hb : 0 < b) : 0 < moment n b := by
  unfold moment
  positivity

lemma profile_nonneg (n : ℕ) (c a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ profile n c a s := by
  unfold profile
  positivity

lemma gaussian_exponent_split {c a s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    -s - c*a^2/s ≤ -(s/2) - 2*(min (1/2) c)*a := by
  let k := min (1/2 : ℝ) c
  have hk : 0 ≤ k := le_of_lt (lt_min (by norm_num) hc)
  have hk₁ : k ≤ 1/2 := min_le_left _ _
  have hk₂ : k ≤ c := min_le_right _ _
  have hsq := mul_nonneg hk (sq_nonneg (s-a))
  have ht := mul_nonneg (sub_nonneg.mpr hk₁) (sq_nonneg s)
  have hu := mul_nonneg (sub_nonneg.mpr hk₂) (sq_nonneg a)
  have h : 2*k*a*s ≤ s^2/2+c*a^2 := by nlinarith
  have hd := (div_le_div_of_nonneg_right h hs.le)
  have he : (2*k*a*s)/s = 2*k*a := by field_simp
  have he' : (s^2/2+c*a^2)/s = s/2+c*a^2/s := by field_simp
  rw [he,he'] at hd
  change -s-c*a^2/s ≤ -(s/2)-2*k*a
  linarith

lemma profile_le_exp (n : ℕ) {c a s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    profile n c a s ≤
      (s^n * Real.exp (-((1/2)*s))) * Real.exp (-(2*min (1/2) c)*a) := by
  unfold profile
  have h := Real.exp_le_exp.mpr (gaussian_exponent_split (a := a) hc hs)
  have he : Real.exp (-s) * Real.exp (-c*a^2/s) = Real.exp (-s-c*a^2/s) := by
    rw [← Real.exp_add]; congr 1; ring
  have he' : Real.exp (-(s/2)-2*min (1/2) c*a) =
      Real.exp (-((1/2)*s)) * Real.exp (-(2*min (1/2) c)*a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← he,he'] at h
  have hp := mul_le_mul_of_nonneg_left h (pow_nonneg hs.le n)
  nlinarith only [hp]

lemma profile_integrable (n : ℕ) {c a : ℝ} (hc : 0 < c) :
    IntegrableOn (profile n c a) (Ioi 0) := by
  apply ((moment_integrable n (by norm_num : (0:ℝ)<1/2)).mul_const
    (Real.exp (-(2*min (1/2) c)*a))).mono' (by
      unfold profile
      exact (by fun_prop : Measurable _).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg _ _ _ hs.le)]
  exact profile_le_exp n hc hs

lemma profile_integral_le_exp (n : ℕ) {c a : ℝ} (hc : 0 < c) :
    (∫ s : ℝ in Ioi 0, profile n c a s) ≤
      moment n (1/2) * Real.exp (-(2*min (1/2) c)*a) := by
  calc
    _ ≤ ∫ s : ℝ in Ioi 0,
        (s^n * Real.exp (-((1/2)*s))) * Real.exp (-(2*min (1/2) c)*a) := by
      apply integral_mono_ae (profile_integrable n hc)
        ((moment_integrable n (by norm_num : (0:ℝ)<1/2)).mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact profile_le_exp n hc hs
    _ = _ := by rw [integral_mul_const, moment_integral n (by norm_num : (0:ℝ)<1/2)]

lemma profile_integral_le_rapid (n N : ℕ) {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) :
    (∫ s : ℝ in Ioi 0, profile n c a s) ≤
      (moment n (1/2) * rapidConstant (2*min (1/2) c) N) / (1+a)^N := by
  have hk : 0 < 2*min (1/2) c := mul_pos (by norm_num) (lt_min (by norm_num) hc)
  calc
    _ ≤ moment n (1/2) * Real.exp (-(2*min (1/2) c)*a) := profile_integral_le_exp n hc
    _ ≤ moment n (1/2) * (rapidConstant (2*min (1/2) c) N / (1+a)^N) :=
      mul_le_mul_of_nonneg_left (exp_neg_le_rapid hk ha N)
        (moment_pos n (by norm_num : (0:ℝ)<1/2)).le
    _ = _ := by ring

lemma truncatedProfile_nonneg (n : ℕ) (c a T : ℝ) :
    0 ≤ truncatedProfile n c a T := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact profile_nonneg n c a hs.1.le

lemma truncatedProfile_le (n : ℕ) {c a : ℝ} (hc : 0 < c) (T : ℝ) :
    truncatedProfile n c a T ≤ ∫ s : ℝ in Ioi 0, profile n c a s := by
  apply setIntegral_mono_set (profile_integrable n hc)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact profile_nonneg n c a hs.le
  · exact Filter.Eventually.of_forall (fun _ hs => hs.1)

lemma leadingConstant_pos (N : ℕ) : 0 < leadingConstant N := by
  unfold leadingConstant
  have := moment_pos 3 (by norm_num : (0:ℝ)<1/2)
  have := rapidConstant_pos (by norm_num : (0:ℝ)<1/2) N
  positivity

lemma leading_nonneg (r t₀ d : ℝ) : 0 ≤ leading r t₀ d := by
  unfold leading
  exact mul_nonneg (by positivity) (truncatedProfile_nonneg _ _ _ _)

lemma leading_upper (N : ℕ) {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (t₀ : ℝ) :
    leading r t₀ d ≤ leadingConstant N * (r⁻¹)^4 / (1+d/r)^N := by
  have h := (truncatedProfile_le 3 (a := d/r) (by norm_num : (0:ℝ)<1/4) (t₀/r^2)).trans
    (profile_integral_le_rapid 3 N (by norm_num : (0:ℝ)<1/4) (div_nonneg hd hr.le))
  norm_num only [show min (1/2 : ℝ) (1/4) = 1/4 by norm_num,
    show (2:ℝ)*(1/4) = 1/2 by norm_num] at h
  have hp := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (1 / (120*(4*Real.pi)^2)) * (r⁻¹)^4 by positivity)
  unfold leading leadingConstant
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4
lemma normalFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (normalFirst J α ht p D g B j) x :=
  firstMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2)) j

attribute [local irreducible] normalFirst

lemma normalGauge_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : (x.1,0) ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (normalGauge J α ht p D g B) x := by
  have hc : ContDiffAt ℝ ∞ (fun q : Space => (q,(0 : Space))) x.1 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf (i : Fin 4) : ContDiffAt ℝ ∞
      (fun q : Space => normalFirst J α ht p D g B i (q,0)) x.1 := by
    have hi : ContDiffAt ℝ ∞ (normalFirst J α ht p D g B i) (x.1,0) :=
      normalFirst_smooth J α ht p D g B hs hg hB hx i
    exact hi.comp x.1 hc
  exact gauge_joint (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
    (fun i q => normalFirst J α ht p D g B i (q,0)) (x := x) hf

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {E F W : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup W]
attribute [local instance] Classical.propDecidable

lemma push_apply (C : OpenPartialHomeomorph E F) (f : E → W) {x : E} (hx : x ∈ C.source) :
    push C f (C x) = f x := by
  simp [push,C.map_source hx,C.left_inv hx]

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPatch
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedSpace
lemma leadingPatch_apply (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source) :
    leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (x.1,normalMap g B x.1 x.2) =
      leadingCoordinate J α ht p D g B ψ χ t x :=
  KernelExtension.push_apply _ _ hx

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeApproximateIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff Topology
open Filter
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]

omit [Fintype ι] in
lemma adjoint_product_commutes (S : W →L[ℝ] W) (T : Q →L[ℝ] Q)
    (hS : S.adjoint = S) (hT : T.adjoint = T) (A B : W →L[ℝ] Q)
    (hA : A ∘L S = T ∘L A) (hB : B ∘L S = T ∘L B) :
    Commute (A.adjoint ∘L B) S := by
  have hAs := congrArg (fun L : W →L[ℝ] Q => L.adjoint) hA
  simp only [ContinuousLinearMap.adjoint_comp,hS,hT] at hAs
  change (A.adjoint ∘L B) ∘L S = S ∘L (A.adjoint ∘L B)
  rw [ContinuousLinearMap.comp_assoc,hB,←ContinuousLinearMap.comp_assoc,←hAs,
    ContinuousLinearMap.comp_assoc]

omit [Fintype ι] [CompleteSpace Q] [CompleteSpace W] in
lemma fderiv_commutes (S : W →L[ℝ] W) (F : V → W →L[ℝ] W) {x : V}
    (hF : DifferentiableAt ℝ F x) (hcomm : ∀ᶠ y in 𝓝 x, Commute (F y) S) (v : V) :
    Commute (fderiv ℝ F x v) S := by
  have he : (fun y => F y ∘L S) =ᶠ[𝓝 x] (fun y => S ∘L F y) := hcomm
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hleft := (hF.hasFDerivAt.clm_comp (hasFDerivAt_const (c := S) x)).fderiv
  have hright := ((hasFDerivAt_const (c := S) x).clm_comp hF.hasFDerivAt).fderiv
  rw [hleft,hright] at hd
  have hv := congrArg (fun L : V →L[ℝ] (W →L[ℝ] W) => L v) hd
  change (fderiv ℝ F x v) ∘L S = S ∘L (fderiv ℝ F x v)
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,zero_apply,ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero,add_zero,zero_add] using hv

lemma firstMatrix_commutes (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (S : W →L[ℝ] W) (T : Q →L[ℝ] Q)
    (hS : S.adjoint = S) (hT : T.adjoint = T) {x : V}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hρ : DifferentiableAt ℝ ρ x)
    (hea : ∀ i, ∀ᶠ y in 𝓝 x, a i y ∘L S = T ∘L a i y)
    (heb : b x ∘L S = T ∘L b x) (j : ι) : Commute (firstMatrix e a b ρ j x) S := by
  have hp (i : ι) : DifferentiableAt ℝ (principalMatrix a ρ i j) x :=
    ((ContinuousLinearMap.adjoint.toContinuousLinearEquiv.differentiableAt.comp x
      (hρ.smul (ha i))).clm_comp (ha j))
  have hc (i : ι) : ∀ᶠ y in 𝓝 x, Commute (principalMatrix a ρ i j y) S := by
    filter_upwards [hea i,hea j] with y hi hj
    apply adjoint_product_commutes S T hS hT (ρ y • a i y) (a j y) _ hj
    simpa only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul] using congrArg (ρ y • ·) hi
  have hder (i : ι) := fderiv_commutes S (principalMatrix a ρ i j) (hp i) (hc i) (e i)
  have hax := (hea j).self_of_nhds
  unfold firstMatrix
  exact (((Commute.sum_left _ _ _ fun i _ => hder i).smul_left _).add_left
    (adjoint_product_commutes S T hS hT (b x) (a j x) heb hax)).sub_left
      (adjoint_product_commutes S T hS hT (a j x) (b x) hax heb)

omit [CompleteSpace W] in
lemma gauge_commutes (q : ι → V →L[ℝ] ℝ) (b : ι → W →L[ℝ] W)
    (S : W →L[ℝ] W) (hb : ∀ i, Commute (b i) S) (z : V) :
    Commute (OrthogonalJets.gauge (FirstJetGauge.halfJet q b) z) S := by
  apply Commute.exp_left
  simp only [FirstJetGauge.halfJet,sum_apply,ContinuousLinearMap.smulRight_apply]
  exact Commute.sum_left _ _ _ fun i _ => ((hb i).smul_left (1/2 : ℝ)).smul_left _
end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeStarGeometry
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.HodgeStarGeometry
open HodgeNormalSymbol HodgeNormalOperator HodgeFrame MetricModel MetricForms MetricHodge
open scoped ContDiff Topology RealInnerProductSpace
open ContinuousAlternatingMap Filter
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma starMap_adjoint : starMap.adjoint = starMap := by
  apply Eq.symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr UnitaryFrame.star_self_adjoint

lemma swapMap_adjoint : swapMap.adjoint = swapMap := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ,swap]
  ring

lemma principal_intertwines (b : Fin 4 → EuclideanEnergy.V) (i : Fin 4) :
    HodgeFrozenEnergy.coefficient b i ∘L starMap = swapMap ∘L HodgeFrozenEnergy.coefficient b i := by
  ext u k
  simp only [ContinuousLinearMap.comp_apply,starMap_apply,swapMap_apply,
    HodgeFrozenEnergy.coefficient,normalSymbol_apply,symbol,UnitaryFrame.star_square]
  fin_cases k <;> rfl

lemma swap_join (u v : EuclideanEnergy.V) : swapMap (join u v) = join v u := by
  ext i
  fin_cases i <;> rfl
lemma swap_left (b : Fin 4 → EuclideanEnergy.V) (a : MetricForms.Form EuclideanEnergy.V 1) :
    swapMap (left b a) = right b a := by
  exact swap_join _ _
lemma swap_right (b : Fin 4 → EuclideanEnergy.V) (a : MetricForms.Form EuclideanEnergy.V 1) :
    swapMap (right b a) = left b a := by
  exact swap_join _ _

variable (g : Metric EuclideanEnergy.V) (J : EuclideanEnergy.V →L[ℝ] EuclideanEnergy.V)
  (F : MetricForms.Form EuclideanEnergy.V 2) (b : Fin 4 → EuclideanEnergy.V)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (h0 : J (b 0)=b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2)=b 3) (h3 : J (b 3) = -b 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
include hb horth h0 h1 h2 h3 hF
lemma combine_star_frame (u : W) :
    combine (fun j => starTwo g J F (basisForm g b j)) u = combine (basisForm g b) (starMap u) := by
  rw [combine_star_basis,combine_basis]
  apply coordinates_injective g (by simp [EuclideanEnergy.V]) b hb
  rw [coordinates_star g (by simp [EuclideanEnergy.V]) b hb J horth h0 h1 h2 h3 F hF,
    coordinates_reconstruct g b hb,coordinates_reconstruct g b hb]
  rfl

end TamingCompatibility.HodgeStarGeometry

end
end

section

noncomputable section
namespace TamingCompatibility.HodgeStarGeometry
open HodgeNormalSymbol HodgeNormalOperator HodgeFrame MetricModel MetricForms MetricHodge
open EuclideanEnergy ContinuousAlternatingMap Filter Set
open scoped ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma combineThree_extDeriv (ψ : Fin 6 → V → MetricForms.Form V 2) {x : V}
    (hψ : ∀ j, DifferentiableAt ℝ (ψ j) x) (u : W) :
    combineThree (fun j => extDeriv (ψ j) x) u =
      extDeriv (fun y => combine (fun j => ψ j y) u) x := by
  simp only [combine_apply,combineThree_apply]
  rw [HodgeFrame.extDeriv_sum (f := fun j y => u j • ψ j y)
    (fun j => (hψ j).const_smul (u j))]
  apply Finset.sum_congr rfl
  intro j _
  exact (extDeriv_fun_smul (u j) (ψ j)).symm

lemma combineThree_intertwines (ψ φ : Fin 6 → V → MetricForms.Form V 2) {x : V}
    (hψ : ∀ j, DifferentiableAt ℝ (ψ j) x) (hφ : ∀ j, DifferentiableAt ℝ (φ j) x)
    (hstar : ∀ᶠ y in 𝓝 x, ∀ u : W, combine (fun j => φ j y) u = combine (fun j => ψ j y) (starMap u))
    (u : W) : combineThree (fun j => extDeriv (φ j) x) u =
      combineThree (fun j => extDeriv (ψ j) x) (starMap u) := by
  rw [combineThree_extDeriv φ hφ,combineThree_extDeriv ψ hψ]
  have he : (fun y => combine (fun j => φ j y) u) =ᶠ[𝓝 x]
      (fun y => combine (fun j => ψ j y) (starMap u)) := hstar.mono fun _ h => h u
  unfold extDeriv
  rw [he.fderiv_eq (𝕜 := ℝ)]

lemma lower_intertwines (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (ψ φ : Fin 6 → V → MetricForms.Form V 2) {x : V}
    (hψ : ∀ j, DifferentiableAt ℝ (ψ j) x) (hφ : ∀ j, DifferentiableAt ℝ (φ j) x)
    (hstar : ∀ᶠ y in 𝓝 x, ∀ u : W, combine (fun j => φ j y) u = combine (fun j => ψ j y) (starMap u)) :
    HodgeNormalOperator.lower g F b ψ φ x ∘L starMap =
      swapMap ∘L HodgeNormalOperator.lower g F b ψ φ x := by
  have h1 (u : W) := combineThree_intertwines ψ φ hψ hφ hstar u
  have h2 (u : W) : combineThree (fun j => extDeriv (φ j) x) (starMap u) =
      combineThree (fun j => extDeriv (ψ j) x) u := by
    simpa only [starMap_apply,UnitaryFrame.star_square] using h1 (starMap u)
  apply ContinuousLinearMap.ext
  intro u
  simp only [HodgeNormalOperator.lower,ContinuousLinearMap.comp_apply,_root_.add_apply,
    map_add,swap_left,swap_right,h2,h1,add_comm]

end TamingCompatibility.HodgeStarGeometry

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus
open HodgeNormalSymbol HodgeStarGeometry HodgeGeometricCoefficients HodgeNormalOperator HodgeFrame
open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)

local instance starGeometryMetricTensorNormedAddCommGroup_r823872_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance starGeometryMetricTensorNormedSpace_r823872_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma geometric_lower_intertwines (hs : IsSmooth α) {x : Space} (hx : x ∈ D.domain) :
    HodgeGeometricCoefficients.lower (coordinateMetric J α ht p) (coordinateJ J p)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame x ∘L starMap =
    swapMap ∘L HodgeGeometricCoefficients.lower (coordinateMetric J α ht p) (coordinateJ J p)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame x := by
  let g := coordinateMetric J α ht p
  let j := coordinateJ J p
  let F := ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm
  have hg := (coordinateMetric_smooth J α hs ht p).mono D.domain_subset
  have hj := (coordinateJ_smooth J p).mono D.domain_subset
  have hF := (ManifoldForms.smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset
  have hψ := HodgeGeometricCoefficients.frame_smooth hg D.frame_smooth
  have hφ := HodgeGeometricCoefficients.starFrame_smooth g j F D.frame D.domain_open hg hj
    (fun y hy => coordinateJ_square J p (D.domain_subset hy))
    (fun y hy => coordinateMetric_hermitian J α ht p (D.domain_subset hy)) hF D.frame_smooth
  apply lower_intertwines
  · exact fun k => ((hψ k).contDiffAt (D.domain_open.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact fun k => ((hφ k).contDiffAt (D.domain_open.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · filter_upwards [D.domain_open.mem_nhds hx] with y hy
    intro u
    obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex y hy
    exact combine_star_frame (g y) (j y) (F y) (fun k => D.frame k y) (D.frame_gram y hy)
      (coordinateMetric_hermitian J α ht p (D.domain_subset hy)) h0 h1 h2 h3
      (ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hy)) u

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeStarNormalGauge
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol HodgeStarGeometry FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeStarNormalGaugeCommuteMetricNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeStarNormalGaugeCommuteMetricNormedSpace
lemma pullCoefficient_intertwines (a : Fin 4 → W →L[ℝ] Q) (C : Space →L[ℝ] Space)
    (h : ∀ k, a k ∘L starMap = swapMap ∘L a k) (i : Fin 4) :
    pullCoefficient a C i ∘L starMap = swapMap ∘L pullCoefficient a C i := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [pullCoefficient,ContinuousLinearMap.comp_apply,sum_apply,smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((C (EuclideanEnergy.e k) i) • ·)
    (congrArg (fun L : W →L[ℝ] Q => L u) (h k))

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma pulledA_intertwines (q z : Space) (i : Fin 4) :
    pulledA J α ht p D g B q i z ∘L starMap =
      swapMap ∘L pulledA J α ht p D g B q i z := by
  exact pullCoefficient_intertwines _ _ (fun k => principal_intertwines _ k) i

lemma pulledB_intertwines (hs : IsSmooth α) {q z : Space}
    (hz : normalMap g B q z ∈ D.domain) :
    pulledB J α ht p D g B q z ∘L starMap = swapMap ∘L pulledB J α ht p D g B q z :=
  geometric_lower_intertwines J α ht p D hs hz

lemma normalFirst_commutes (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    Commute (normalFirst J α ht p D g B j x) starMap := by
  apply firstMatrix_commutes _ _ _ _ starMap swapMap starMap_adjoint swapMap_adjoint
  · intro i
    exact ((pulledA_joint J α ht p D g B hg hB hx.1 i).comp x.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact ((normalDensity_smooth g B hg hB hx.2).comp x.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact fun i => Filter.Eventually.of_forall fun y => pulledA_intertwines J α ht p D g B x.1 y i
  · exact pulledB_intertwines J α ht p D g B hs hx.1.1

lemma normalGauge_commutes (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hq : (q,0) ∈ normalDomain J α ht p D g B) (z : Space) :
    Commute (normalGauge J α ht p D g B (q,z)) starMap := by
  unfold normalGauge
  exact gauge_commutes _ _ starMap (fun j => normalFirst_commutes J α ht p D g B hs hg hB hq j) z

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.UnitaryFrame
open HodgeStarGeometry
open scoped RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma unitary_star_angular (U : W →L[ℝ] W) (hU : U ∈ unitary (W →L[ℝ] W))
    (hstar : Commute U starMap) (v w : V) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ⟪line v, star (U (line w))⟫ =
      (1/2 : ℝ)*‖line v-U (line w)‖^2 - (1/4 : ℝ)*‖fundamental-U fundamental‖^2 := by
  have hcomm (u : W) : U (star u) = star (U u) :=
    congrArg (fun L : W →L[ℝ] W => L u) hstar
  have hdual : selfDualPart (U (line w)) = (1/2 : ℝ) • U fundamental := by
    rw [selfDualPart,← hcomm,← map_add,← map_smul]
    simpa only [selfDualPart,map_smul] using congrArg U (unit_line_selfDualPart hw)
  exact angular_identity _ _ _ _ (unit_line_norm hv)
    ((ContinuousLinearMap.norm_map_of_mem_unitary hU _).trans (unit_line_norm hw))
    fundamental_norm_sq
    (by rw [ContinuousLinearMap.norm_map_of_mem_unitary hU,fundamental_norm_sq])
    (unit_line_selfDualPart hv) hdual

end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol HodgeStarGeometry FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeStarNormalGaugeAngularMetricNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeStarNormalGaugeAngularMetricNormedSpace
lemma normalGauge_angular (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hactual : ActualData J α ht p D q g B) (z v w : Space)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ⟪UnitaryFrame.line v,UnitaryFrame.star (normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w))⟫ =
      (1/2 : ℝ)*‖UnitaryFrame.line v-normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w)‖^2 -
      (1/4 : ℝ)*‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖^2 := by
  exact UnitaryFrame.unitary_star_angular _
    (normalGauge_unitary J α ht p D g B hs hg hB hactual z)
    (normalGauge_commutes J α ht p D g B hs hg hB (hactual.center J α ht p D g B).1 z) v w hv hw

lemma compact_normalGauge_angular (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
      ∀ v w : Space, ‖v‖ = 1 → ‖w‖ = 1 →
        (1/2 : ℝ)*‖UnitaryFrame.line v-normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w)‖^2 - C*‖z‖^2 ≤
        ⟪UnitaryFrame.line v,UnitaryFrame.star (normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w))⟫ := by
  let F : Space × Space → W := fun x => normalGauge J α ht p D g B x UnitaryFrame.fundamental
  let Ω : Set (Space × Space) := (fun x : Space × Space => (x.1,(0 : Space))) ⁻¹' normalDomain J α ht p D g B
  have hΩ : IsOpen Ω := (normalDomain_open J α ht p D g B hg hB).preimage
    (continuous_fst.prodMk continuous_const)
  have hKΩ : K ×ˢ {(0 : Space)} ⊆ Ω := by
    rintro ⟨q,z⟩ ⟨hq,_⟩
    exact ((hactual q hq).center J α ht p D g B).1
  have hF : ∀ x ∈ Ω, ContDiffAt ℝ ∞ F x := fun x hx =>
    (normalGauge_smooth J α ht p D g B hs hg hB hx).clm_apply contDiffAt_const
  obtain ⟨C,hC,r,hr,_,hb⟩ := local_linear_bound F K hK Ω hΩ hKΩ hF
  refine ⟨C ^ 2,by positivity,r,hr,fun q hq z hz v w hv hw => ?_⟩
  rw [normalGauge_angular J α ht p D g B hs hg hB (hactual q hq) z v w hv hw]
  have hbound : ‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖ ≤ C*‖z‖ := by
    have hh := hb q hq z hz
    simpa only [F,normalGauge_zero,one_apply_eq_self,norm_sub_rev] using hh
  have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg z)) |>.mpr hbound
  nlinarith [sq_nonneg ‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set _root_.MeasureTheory

lemma flat_gamma_integrand {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : FlatHeat.V) :
    hodgeGammaWeight s * FlatHeat.heat (r^2*s) z =
      (4*Real.pi)⁻¹^2 * (r⁻¹)^4 * profile 3 (1/4) (‖z‖/r) s := by
  have hexp : -‖z‖^2/(4*(r^2*s)) = -(1/4 : ℝ)*(‖z‖/r)^2/s := by ring
  unfold hodgeGammaWeight FlatHeat.heat profile
  rw [hexp]
  have hcoef : s^5*(4*Real.pi*(r^2*s))⁻¹^2 = (4*Real.pi)⁻¹^2*(r⁻¹)^4*s^3 := by
    field_simp [Real.pi_ne_zero,hr.ne',hs.ne']
  calc
    _ = (s^5*(4*Real.pi*(r^2*s))⁻¹^2)*Real.exp (-s)*Real.exp (-(1/4 : ℝ)*(‖z‖/r)^2/s) := by ring
    _ = _ := by rw [hcoef]; ring

lemma flat_gamma_integral {r : ℝ} (hr : 0 < r) (T : ℝ) (z : FlatHeat.V) :
    (1/120 : ℝ) * (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s * FlatHeat.heat (r^2*s) z) =
      leading r T ‖z‖ := by
  have he : (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s * FlatHeat.heat (r^2*s) z) =
      ((4*Real.pi)⁻¹^2*(r⁻¹)^4) * truncatedProfile 3 (1/4) (‖z‖/r) (T/r^2) := by
    unfold truncatedProfile
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact flat_gamma_integrand hr hs.1 z
  rw [he]
  unfold leading
  ring

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge HodgeNormalSymbol NormalJets NormalMetricCalculus Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma leadingCoordinate_gamma {r : ℝ} (hr : 0 < r) (T : ℝ) (ψ χ : Space → ℝ) (q z : Space) :
    (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s •
      leadingCoordinate J α ht p D g B ψ χ (r^2*s) (q,z)) =
      (ψ q*χ z*HodgeKernelBounds.leading r T ‖z‖) • normalGauge J α ht p D g B (q,z) := by
  have operatorComplete (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] : CompleteSpace (E →L[ℝ] E) := inferInstance
  let : CompleteSpace (W →L[ℝ] W) := operatorComplete W
  simp only [leadingCoordinate,smul_smul]
  have he (s : ℝ) : hodgeGammaWeight s*(ψ q*χ z*FlatHeat.heat (r^2*s) z) =
      (ψ q*χ z)*(hodgeGammaWeight s*FlatHeat.heat (r^2*s) z) := by ring
  simp_rw [he]
  rw [integral_smul_const,integral_const_mul,smul_smul]
  rw [show (1/120 : ℝ)*((ψ q*χ z)*(∫ s : ℝ in Ioc 0 (T/r^2),
      hodgeGammaWeight s*FlatHeat.heat (r^2*s) z)) =
      (ψ q*χ z)*((1/120 : ℝ)*(∫ s : ℝ in Ioc 0 (T/r^2),
      hodgeGammaWeight s*FlatHeat.heat (r^2*s) z)) by ring]
  rw [HodgeKernelBounds.flat_gamma_integral hr]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds

lemma leading_quadratic_upper (N : ℕ) {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (T : ℝ) :
    d^2 * leading r T d ≤ leadingConstant (N+2)*(r⁻¹)^2/(1+d/r)^N := by
  have hb : 0 < 1+d/r := by positivity
  have hsq : d^2*(r⁻¹)^4 ≤ (1+d/r)^2*(r⁻¹)^2 := by
    have h : (d/r)^2 ≤ (1+d/r)^2 := by nlinarith [div_nonneg hd hr.le]
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg r⁻¹)
    calc
      d^2*(r⁻¹)^4 = (d/r)^2*(r⁻¹)^2 := by ring
      _ ≤ _ := hm
  have hc := (leadingConstant_pos (N+2)).le
  calc
    _ ≤ d^2*(leadingConstant (N+2)*(r⁻¹)^4/(1+d/r)^(N+2)) :=
      mul_le_mul_of_nonneg_left (leading_upper (N+2) hr hd T) (sq_nonneg d)
    _ = leadingConstant (N+2)*(d^2*(r⁻¹)^4)/(1+d/r)^(N+2) := by ring
    _ ≤ leadingConstant (N+2)*((1+d/r)^2*(r⁻¹)^2)/(1+d/r)^(N+2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc) (pow_nonneg hb.le _)
    _ = _ := by rw [pow_add]; field_simp [hb.ne']

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPartition
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldLocalization
open Set ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X)
attribute [local instance] Classical.propDecidable

omit [T2Space X] [CompactSpace X] in
lemma coordinatePartition_bounds (p : A.centers) (q : Space) :
    0 ≤ coordinatePartition A p q ∧ coordinatePartition A p q ≤ 1 := by
  by_cases hq : q ∈ (extChartAt Model p.val).target
  · simp only [coordinatePartition,Set.indicator_of_mem hq]
    exact ⟨A.partition.nonneg _ _,A.partition.le_one _ _⟩
  · simp only [coordinatePartition,Set.indicator_of_notMem hq,le_refl,zero_le_one,and_self]

end TamingCompatibility.ManifoldLocalization

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedSpace
lemma actual {q : Space} (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) :
    ActualData J α ht p D.chart q D.metricExtension D.frameExtension :=
  ⟨D.actualDomain,D.actual_open,D.centers_actual hq,D.actual_subset,
    D.metric_actual,D.frame_actual,D.metric_symmetric⟩

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCoordinateRetraction
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma coordinateEncode_rawVector (p : A.centers) (a : TwoForm X) {q : Space}
    (hq : q ∈ (D p).chart.domain) :
    coordinateEncode J α ht A D p q (HodgeChart.rawVector J α ht p.val (D p).chart a q) =
      frameEncode J α ht A D ((extChartAt Model p.val).symm q) (a ((extChartAt Model p.val).symm q)) := by
  ext i
  change ⟪HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q,
    HodgeChart.rawVector J α ht p.val (D p).chart a q⟫ = _
  rw [real_inner_comm]
  unfold HodgeChart.rawVector
  rw [coordinates_pairing _ (by simp [Space]) _ ((D p).chart.frame_gram q hq),
    GeometricAdjoint.pairing_two_chart J α ht p.val a (globalFrame J α ht A D i.1 i.2)
      ((D p).chart.domain_subset hq)]
  rfl

omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_apply (p : A.centers) (q : Space) (v : FrameSpace A) :
    coordinateDecode J α ht A D p q v = (squareMass A ((extChartAt Model p.val).symm q))⁻¹ •
      ∑ i : A.centers × Fin 6, v i •
        HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q := by
  change (squareMass A ((extChartAt Model p.val).symm q))⁻¹ • ((∑ i : A.centers × Fin 6,
    (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
      (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q)) v) = _
  simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_rawVector (p : A.centers) (q : Space) (v : FrameSpace A) :
    coordinateDecode J α ht A D p q v = HodgeChart.rawVector J α ht p.val (D p).chart
      (fun x => frameDecode J α ht A D x v) q := by
  rw [coordinateDecode_apply,Fintype.sum_prod_type]
  let L : MetricForms.Form Space 2 →L[ℝ] W :=
    HodgeFrame.coordinates (fun i => (D p).chart.frame i q) ∘L
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (mfderiv Model Model (extChartAt Model p.val).symm q)
  change (squareMass A ((extChartAt Model p.val).symm q))⁻¹ •
    (∑ i : A.centers, ∑ j : Fin 6, v (i,j) • L (globalFrame J α ht A D i j ((extChartAt Model p.val).symm q))) = _
  simp only [HodgeChart.rawVector,ManifoldForms.pullback,frameDecode_apply]
  change _ = L _
  simp only [Finset.smul_sum,smul_smul]
  have he (g : A.centers → Fin 6 → MetricForms.Form Space 2) (c : A.centers → Fin 6 → ℝ) :
      L (∑ i : A.centers, ∑ j : Fin 6, c i j • g i j) = ∑ i : A.centers, ∑ j : Fin 6, c i j • L (g i j) := by
    simp only [map_sum,map_smul]
  exact (he (fun i j => globalFrame J α ht A D i j ((extChartAt Model p.val).symm q))
    (fun i j => (squareMass A ((extChartAt Model p.val).symm q))⁻¹*v (i,j))).symm

include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_encode_raw (p : A.centers) (a : TwoForm X) {q : Space}
    (hq : q ∈ (D p).chart.domain) :
    coordinateDecode J α ht A D p q
      (coordinateEncode J α ht A D p q (HodgeChart.rawVector J α ht p.val (D p).chart a q)) =
      HodgeChart.rawVector J α ht p.val (D p).chart a q := by
  rw [coordinateEncode_rawVector J α ht A D p a hq,coordinateDecode_rawVector]
  change HodgeFrame.coordinates _ ((frameDecode J α ht A D ((extChartAt Model p.val).symm q)
    (frameEncode J α ht A D ((extChartAt Model p.val).symm q) (a ((extChartAt Model p.val).symm q)))).compContinuousLinearMap _) = _
  erw [frameDecode_encode J α ht A D hD]
  rfl

include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_encode (p : A.centers) {q : Space} (hq : q ∈ (D p).chart.domain) (v : W) :
    coordinateDecode J α ht A D p q (coordinateEncode J α ht A D p q v) = v := by
  let a := HodgeChart.manifoldTest J α ht p.val (D p).chart (fun _ => v)
  have ha : HodgeChart.rawVector J α ht p.val (D p).chart a q = v := by
    unfold HodgeChart.rawVector a
    rw [HodgeChart.pullback_manifoldTest J α ht p.val (D p).chart _ ((D p).chart.domain_subset hq)]
    exact coordinates_reconstruct _ _ ((D p).chart.frame_gram q hq) v
  rw [← ha]
  exact coordinateDecode_encode_raw J α ht A D hD p a hq

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaLinearTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.MeasureTheory Set
open scoped Manifold

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

omit [CompactSpace X] [T2Space X] in
lemma gammaPartitionLeading_apply {r : ℝ} (hr : 0 < r) (T : ℝ)
    (p : A.centers) {z : Space × Space} (hz : z ∈ (E p).normalCompact) :
    gammaPartitionLeading J α ht A E T r p
      (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) =
      (coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖) •
        normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z := by
  unfold gammaPartitionLeading
  have he : (fun s : ℝ => hodgeGammaWeight s • partitionLeading J α ht A E p (r^2*s)
      (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)) =
      (fun s : ℝ => hodgeGammaWeight s • leadingCoordinate J α ht p.val (E p).chart
        (E p).metricExtension (E p).frameExtension (coordinatePartition A p) (E p).normalCutoff
        (r^2*s) z) := by
    funext s
    congr 1
    exact leadingPatch_apply J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq (coordinatePartition A p) (E p).normalCutoff
      (r^2*s) ((E p).normalCompact_source hz)
  rw [he]
  exact leadingCoordinate_gamma J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    hr T (coordinatePartition A p) (E p).normalCutoff z.1 z.2

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeDirectionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma alternating_swap (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u v : E) :
    a ![v,u] = -a ![u,v] := by
  have hv : ![u,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,u] := by
    ext i
    fin_cases i <;> simp
  simpa only [hv, ContinuousAlternatingMap.coe_toAlternatingMap] using
    a.map_swap ![u,v] (by decide : (0 : Fin 2) ≠ 1)

lemma alternating_sum_left {ι : Type*} (a : E [⋀^Fin 2]→L[ℝ] ℝ)
    (s : Finset ι) (f : ι → E) (v : E) :
    a ![∑ i ∈ s, f i, v] = ∑ i ∈ s, a ![f i,v] := by
  have hu (w : E) : Function.update ![0,v] (0 : Fin 2) w = ![w,v] := by
    ext i
    fin_cases i <;> simp
  simpa only [hu,ContinuousAlternatingMap.coe_toAlternatingMap] using
    a.toAlternatingMap.map_update_sum s 0 f ![0,v]

lemma alternating_smul_left (a : E [⋀^Fin 2]→L[ℝ] ℝ) (c : ℝ) (u v : E) :
    a ![c • u,v] = c * a ![u,v] := by
  simpa only [smul_eq_mul] using a.vecCons_smul ![v] c u

lemma alternating_sum_right {ι : Type*} (a : E [⋀^Fin 2]→L[ℝ] ℝ)
    (s : Finset ι) (f : ι → E) (u : E) :
    a ![u, ∑ i ∈ s, f i] = ∑ i ∈ s, a ![u,f i] := by
  rw [alternating_swap,alternating_sum_left,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [alternating_swap,neg_neg]

lemma alternating_smul_right (a : E [⋀^Fin 2]→L[ℝ] ℝ) (c : ℝ) (u v : E) :
    a ![u,c • v] = c * a ![u,v] := by
  rw [alternating_swap,alternating_smul_left,alternating_swap]
  ring

lemma alternating_self (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u : E) : a ![u,u] = 0 :=
  a.map_eq_zero_of_eq ![u,u] (i := 0) (j := 1) rfl (by decide : (0 : Fin 2) ≠ 1)

lemma alternating_frame_eval (a : E [⋀^Fin 2]→L[ℝ] ℝ) (b : Fin 4 → E) (v w : V) :
    a ![∑ i : Fin 4, v i • b i, ∑ i : Fin 4, w i • b i] =
      ⟪WithLp.toLp 2 ![a ![b 0,b 1],a ![b 0,b 2],a ![b 0,b 3],
        a ![b 1,b 2],a ![b 1,b 3],a ![b 2,b 3]], wedge v w⟫ := by
  rw [alternating_sum_left]
  simp_rw [alternating_sum_right,alternating_smul_left,alternating_smul_right]
  simp [Fin.sum_univ_succ,alternating_self,wedge,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct]
  rw [alternating_swap a (b 0) (b 1),alternating_swap a (b 0) (b 2),
    alternating_swap a (b 0) (b 3),alternating_swap a (b 1) (b 2),
    alternating_swap a (b 1) (b 3),alternating_swap a (b 2) (b 3)]
  ring

end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma sum_directionCoordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) (u : E) :
    ∑ i : Fin 4, directionCoordinates g hdim b hb u i • b i = u := by
  have h := congrArg (equiv g) ((basisOfFrame g hdim b hb).sum_repr (ofOriginal g u))
  have he (x : E) : equiv g (ofOriginal g x) = x := rfl
  simpa only [map_sum,map_smul,basisOfFrame_apply,he,directionCoordinates] using h

lemma norm_directionCoordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) (u : E)
    (hu : g.bilinear u u = 1) : ‖directionCoordinates g hdim b hb u‖ = 1 := by
  rw [directionCoordinates,LinearIsometryEquiv.norm_map]
  have h : ‖ofOriginal g u‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hu
  nlinarith [norm_nonneg (ofOriginal g u)]

omit [FiniteDimensional ℝ E] in
lemma complex_frame_sum (b : Fin 4 → E) (j : E →L[ℝ] E)
    (h0 : j (b 0) = b 1) (h1 : j (b 1) = -b 0)
    (h2 : j (b 2) = b 3) (h3 : j (b 3) = -b 2) (v : UnitaryFrame.V) :
    j (∑ i : Fin 4, v i • b i) = ∑ i : Fin 4, UnitaryFrame.J v i • b i := by
  simp [Fin.sum_univ_succ,UnitaryFrame.J,h0,h1,h2,h3]
  abel

lemma directionCoordinates_eval (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (j : E →L[ℝ] E) (h0 : j (b 0) = b 1) (h1 : j (b 1) = -b 0)
    (h2 : j (b 2) = b 3) (h3 : j (b 3) = -b 2)
    (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u : E) :
    a ![u,j u] =
      ⟪WithLp.toLp 2 ![a ![b 0,b 1],a ![b 0,b 2],a ![b 0,b 3],
        a ![b 1,b 2],a ![b 1,b 3],a ![b 2,b 3]],
        UnitaryFrame.line (directionCoordinates g hdim b hb u)⟫ := by
  let v := directionCoordinates g hdim b hb u
  have hv : ∑ i : Fin 4, v i • b i = u := sum_directionCoordinates g hdim b hb u
  have hw : ∑ i : Fin 4, UnitaryFrame.J v i • b i = j u := by
    rw [← complex_frame_sum b j h0 h1 h2 h3,hv]
  calc
    _ = a ![∑ i : Fin 4, v i • b i, ∑ i : Fin 4, UnitaryFrame.J v i • b i] := by rw [hv,hw]
    _ = _ := UnitaryFrame.alternating_frame_eval a b v (UnitaryFrame.J v)

end TamingCompatibility.HodgeFrame

namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma coordinates_eq_six (b : Fin 4 → E) (a : MetricForms.Form E 2) :
    coordinates b a = WithLp.toLp 2 ![a ![b 0,b 1],a ![b 0,b 2],a ![b 0,b 3],
      a ![b 1,b 2],a ![b 1,b 3],a ![b 2,b 3]] := by
  ext i
  fin_cases i <;> rfl

variable [FiniteDimensional ℝ E]
lemma coordinates_direction_eval (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (j : E →L[ℝ] E) (h0 : j (b 0) = b 1) (h1 : j (b 1) = -b 0)
    (h2 : j (b 2) = b 3) (h3 : j (b 3) = -b 2)
    (a : MetricForms.Form E 2) (u : E) :
    a ![u,j u] = ⟪coordinates b a,UnitaryFrame.line (directionCoordinates g hdim b hb u)⟫ := by
  rw [coordinates_eq_six]
  exact directionCoordinates_eval g hdim b hb j h0 h1 h2 h3 a u
end TamingCompatibility.HodgeFrame

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

attribute [local irreducible] frameDecode unitFrameDirection

include hE in
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_direction (a : TwoForm X) (u : MetricUnit g) :
    framePairing A J α ht E a u.val.proj (unitFrameDirection A J α ht E g u) =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  have he := globalFrame_full_resolution J α ht A E hE a u.val.proj
  have hh := congrArg (fun b : MetricForms.Form Space 2 =>
    b ![u.val.2,J.endomorphism u.val.proj u.val.2]) he
  let v : A.centers → Fin 6 → MetricForms.Form Space 2 := fun p j =>
    globalFrame J α ht A E p j u.val.proj
  let c : A.centers → Fin 6 → ℝ := fun p j => (squareMass A u.val.proj)⁻¹ *
    GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) u.val.proj
  change (∑ p : A.centers, ∑ j : Fin 6, c p j • v p j)
    ![u.val.2,J.endomorphism u.val.proj u.val.2] =
    a u.val.proj ![u.val.2,J.endomorphism u.val.proj u.val.2] at hh
  simp only [ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul] at hh
  calc
    _ = ∑ p : A.centers, ∑ j : Fin 6,
        ((squareMass A u.val.proj)⁻¹ * GeometricAdjoint.pairing J α ht a
          (globalFrame J α ht A E p j) u.val.proj) *
          eval (globalFrame J α ht A E p j) u.val.proj u.val.2
            (J.endomorphism u.val.proj u.val.2) := by
      simp only [framePairing,_root_.sum_apply,_root_.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul,Finset.mul_sum,unitFrameDirection,mul_assoc]
    _ = _ := hh

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitDual_pairing (a : TwoForm X) (u : MetricUnit g) :
    GeometricAdjoint.pairing J α ht (unitDual A J α hs ht E hE g u).val a u.val.proj =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  rw [← framePairing_direction A J α ht E hE g a u,framePairing_apply]
  exact MetricForms.pairing_symm _ _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma unitFrameFunctional_eq (u : MetricUnit g) :
    unitFrameFunctional A J α ht E g u =
      framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj := by
  unfold unitFrameFunctional framePairing
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  rw [unitDual_pairing A J α hs ht E hE g (globalFrame J α ht A E p j) u]
  rfl

lemma unitDual_encode (u : MetricUnit g) :
    frameEncode J α ht A E u.val.proj ((unitDual A J α hs ht E hE g u).val u.val.proj) =
      unitFrameDirection A J α ht E g u := by
  ext i
  rw [frameEncode_apply]
  exact unitDual_pairing A J α hs ht E hE g (globalFrame J α ht A E i.1 i.2) u

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeIntrinsicUnitLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] in
lemma exists_intrinsic_unit_line (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hx : (extChartAt Model p).symm q = u.val.proj) :
    ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧ ∀ a : TwoForm X,
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) =
        ⟪HodgeChart.rawVector J α ht p D a q,UnitaryFrame.line v⟫ := by
  have hqt := D.domain_subset hq
  have hall : ∀ w : TangentSpace Model ((extChartAt Model p).symm q),
      (hermitianMetric J α hs ht).inner _ w w = 1 →
      ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧ ∀ a : TwoForm X,
        eval a ((extChartAt Model p).symm q) w (J.endomorphism _ w) =
          ⟪HodgeChart.rawVector J α ht p D a q,UnitaryFrame.line v⟫ := by
    intro w hw
    let L := inverseChartEquiv p q hqt
    let c : Space := L.symm w
    let v := directionCoordinates (coordinateMetric J α ht p q)
      (by simp [Space]) (fun i => D.frame i q) (D.frame_gram q hq) c
    have he : L c = w := L.apply_symm_apply w
    have hc : (coordinateMetric J α ht p q).bilinear c c = 1 := by
      rw [coordinateMetric_bilinear J α ht p hqt,chartMetric_derivative J α p hqt]
      have he' : mfderiv Model Model (extChartAt Model p).symm q c = w := by
        rw [← inverseChartEquiv_coe p q hqt]
        exact he
      rw [he']
      exact hw
    refine ⟨v,norm_directionCoordinates _ _ _ _ c hc,?_⟩
    intro a
    obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex q hq
    calc
      _ = ManifoldForms.pullback a (extChartAt Model p).symm q ![c,coordinateJ J p q c] := by
        rw [GeometricChart.pullback_complexLine J a p hqt,← inverseChartEquiv_coe p q hqt]
        exact congrArg (fun z => eval a ((extChartAt Model p).symm q) z (J.endomorphism _ z)) he.symm
      _ = _ := coordinates_direction_eval _ _ _ (D.frame_gram q hq)
        (coordinateJ J p q) h0 h1 h2 h3 _ c
  rw [hx] at hall
  exact hall u.val.2 u.property

omit [CompactSpace X] [T2Space X] in
lemma rawVector_pairing (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) (a b : TwoForm X) :
    ⟪HodgeChart.rawVector J α ht p D a q,HodgeChart.rawVector J α ht p D b q⟫ =
      GeometricAdjoint.pairing J α ht a b ((extChartAt Model p).symm q) := by
  unfold HodgeChart.rawVector
  rw [coordinates_pairing _ (by simp [Space]) _ (D.frame_gram q hq),
    GeometricAdjoint.pairing_two_chart J α ht p a b (D.domain_subset hq)]

omit [CompactSpace X] [T2Space X] in
lemma rawVector_constant_test (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) (v : UnitaryFrame.W) :
    HodgeChart.rawVector J α ht p D (HodgeChart.manifoldTest J α ht p D (fun _ => v)) q = v := by
  unfold HodgeChart.rawVector
  rw [HodgeChart.pullback_manifoldTest J α ht p D _ (D.domain_subset hq)]
  exact coordinates_reconstruct _ _ (D.frame_gram q hq) v

omit [CompactSpace X] [T2Space X] in
lemma rawVector_star (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) (a : TwoForm X) :
    HodgeChart.rawVector J α ht p D (starTwo J α ht a) q =
      UnitaryFrame.star (HodgeChart.rawVector J α ht p D a q) := by
  unfold HodgeChart.rawVector
  rw [pullback_starTwo J α ht a p (D.domain_subset hq)]
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex q hq
  exact coordinates_star _ (by simp [Space]) _ (D.frame_gram q hq)
    (coordinateJ J p q) (coordinateMetric_hermitian J α ht p (D.domain_subset hq))
    h0 h1 h2 h3 _ (ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hq)) _

include hE in
omit [CompactSpace X] [T2Space X] in
lemma framePairing_coordinateEncode (p : A.centers) {q : Space}
    (hq : q ∈ (E p).chart.domain) (a : TwoForm X) (v : UnitaryFrame.W) :
    framePairing A J α ht E a ((extChartAt Model p.val).symm q)
      (coordinateEncode J α ht A E p q v) =
        ⟪HodgeChart.rawVector J α ht p.val (E p).chart a q,v⟫ := by
  rw [framePairing_apply]
  erw [← rawVector_pairing J α ht p.val (E p).chart hq,
    ← coordinateDecode_rawVector J α ht A E p q,
    coordinateDecode_encode J α ht A E hE p hq]

lemma exists_unitDual_raw_line (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hx : (extChartAt Model p.val).symm q = u.val.proj) :
    ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧
      HodgeChart.rawVector J α ht p.val (E p).chart
        (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val q = UnitaryFrame.line v := by
  obtain ⟨v,hv,heval⟩ := exists_intrinsic_unit_line J α hs ht p.val (E p).chart hq u hx
  refine ⟨v,hv,?_⟩
  apply ext_inner_right ℝ
  intro w
  let a := HodgeChart.manifoldTest J α ht p.val (E p).chart (fun _ => w)
  have ha : HodgeChart.rawVector J α ht p.val (E p).chart a q = w :=
    rawVector_constant_test J α ht p.val (E p).chart hq w
  rw [← ha,rawVector_pairing J α ht p.val (E p).chart hq,hx,
    unitDual_pairing A J α hs ht E hE (hermitianMetric J α hs ht) a u,heval a,real_inner_comm]

lemma exists_unitDual_coordinate_line (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hx : (extChartAt Model p.val).symm q = u.val.proj) :
    ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧
      coordinateDecode J α ht A E p q
        (frameEncode J α ht A E u.val.proj
          ((unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val u.val.proj)) =
          UnitaryFrame.line v ∧
      coordinateDecode J α ht A E p q
        (frameEncode J α ht A E u.val.proj
          ((starTwo J α ht (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val) u.val.proj)) =
          UnitaryFrame.star (UnitaryFrame.line v) ∧
      ∀ w : UnitaryFrame.W,
        framePairing A J α ht E (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val
          u.val.proj (coordinateEncode J α ht A E p q w) = ⟪UnitaryFrame.line v,w⟫ := by
  obtain ⟨v,hv,he⟩ := exists_unitDual_raw_line A J α hs ht E hE p hq u hx
  refine ⟨v,hv,?_,?_,?_⟩
  · rw [← hx,← coordinateEncode_rawVector J α ht A E p _ hq,
      coordinateDecode_encode J α ht A E hE p hq,he]
  · rw [← hx,← coordinateEncode_rawVector J α ht A E p _ hq,
      coordinateDecode_encode J α ht A E hE p hq,rawVector_star J α ht p.val (E p).chart hq,he]
  · intro w
    rw [← hx,framePairing_coordinateEncode A J α ht E hE p hq,he]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

lemma unitDual_starDirection (u : MetricUnit (hermitianMetric J α hs ht)) :
    frameEncode J α ht A E u.val.proj
      ((starTwo J α ht (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val) u.val.proj) =
      unitStarDirection A J α ht E (hermitianMetric J α hs ht) u := by
  ext i
  rw [frameEncode_apply]
  rw [hodgeStar_pairing]
  exact unitDual_pairing A J α hs ht E hE (hermitianMetric J α hs ht)
    (starTwo J α ht (globalFrame J α ht A E i.1 i.2)) u

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge HodgeNormalSymbol NormalJets NormalMetricCalculus Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma compact_normalGauge_angular_global (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : Space,
      ∀ v w : Space, ‖v‖ = 1 → ‖w‖ = 1 →
        (1/2 : ℝ)*‖UnitaryFrame.line v-normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w)‖^2 - C*‖z‖^2 ≤
        ⟪UnitaryFrame.line v,UnitaryFrame.star (normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w))⟫ := by
  obtain ⟨C,hC,ρ,hρ,hsmall⟩ := compact_normalGauge_angular J α ht p D g B hs hg hB K hK hactual
  refine ⟨max C (2/ρ^2),le_trans hC (le_max_left _ _),?_⟩
  intro q hq z v w hv hw
  by_cases hz : ‖z‖ ≤ ρ
  · have hh := hsmall q hq z hz v w hv hw
    have hm := mul_le_mul_of_nonneg_right (le_max_left C (2/ρ^2)) (sq_nonneg ‖z‖)
    linarith
  · rw [normalGauge_angular J α ht p D g B hs hg hB (hactual q hq) z v w hv hw]
    have hn := ContinuousLinearMap.norm_map_of_mem_unitary
      (normalGauge_unitary J α ht p D g B hs hg hB (hactual q hq) z) UnitaryFrame.fundamental
    have hb := norm_sub_le UnitaryFrame.fundamental
      (normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental)
    rw [hn] at hb
    have hF := UnitaryFrame.fundamental_norm_sq
    have hsq : ‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖^2 ≤ 8 := by
      have hnonneg : 0 ≤ 2*‖UnitaryFrame.fundamental‖ := by positivity
      have hm := sq_le_sq₀ (norm_nonneg _) hnonneg |>.mpr (by linarith :
        ‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖ ≤
          2*‖UnitaryFrame.fundamental‖)
      nlinarith
    have hzρ : ρ^2 ≤ ‖z‖^2 := by nlinarith [lt_of_not_ge hz]
    have h2 : 2 ≤ (2/ρ^2)*‖z‖^2 := by
      calc
        2 = (2/ρ^2)*ρ^2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hzρ (by positivity)
    have hm := mul_le_mul_of_nonneg_right (le_max_right C (2/ρ^2)) (sq_nonneg ‖z‖)
    linarith

lemma leadingCoordinate_gamma_angular_global (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K) (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, ∀ r : ℝ, 0 < r → ∀ T : ℝ, ∀ ψ χ : Space → ℝ,
      ∀ q ∈ K, ∀ z : Space,
      0 ≤ ψ q*χ z → ψ q*χ z ≤ 1 →
      ∀ v w : Space, ‖v‖ = 1 → ‖w‖ = 1 →
      (1/2 : ℝ)*(ψ q*χ z*HodgeKernelBounds.leading r T ‖z‖)*
        ‖UnitaryFrame.line v-normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w)‖^2 -
          (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z‖/r)^N ≤
        ⟪UnitaryFrame.line v,UnitaryFrame.star
          (((1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s •
            leadingCoordinate J α ht p D g B ψ χ (r^2*s) (q,z))) (UnitaryFrame.line w))⟫ := by
  obtain ⟨C,hC,hangular⟩ := compact_normalGauge_angular_global J α ht p D g B hs hg hB K hK hactual
  refine ⟨C,hC,?_⟩
  intro N r hr T ψ χ q hq z hp hp1 v w hv hw
  rw [leadingCoordinate_gamma J α ht p D g B hr]
  simp only [smul_apply,UnitaryFrame.star_smul,inner_smul_right]
  have hl := HodgeKernelBounds.leading_nonneg r T ‖z‖
  have ha := mul_le_mul_of_nonneg_left (hangular q hq z v w hv hw) (mul_nonneg hp hl)
  have he : (ψ q*χ z*HodgeKernelBounds.leading r T ‖z‖)*(C*‖z‖^2) ≤
      (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z‖/r)^N := by
    calc
      _ = C*((ψ q*χ z)*(‖z‖^2*HodgeKernelBounds.leading r T ‖z‖)) := by ring
      _ ≤ C*(‖z‖^2*HodgeKernelBounds.leading r T ‖z‖) :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) hl) hp1) hC
      _ ≤ C*(HodgeKernelBounds.leadingConstant (N+2)*(r⁻¹)^2/(1+‖z‖/r)^N) :=
        mul_le_mul_of_nonneg_left (HodgeKernelBounds.leading_quadratic_upper N hr (norm_nonneg z) T) hC
      _ = _ := by ring
  nlinarith

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeActualAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma unitCoordinate_line (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht)) (hu : (extChartAt Model p.val).symm q = u.val.proj) :
    ∃ a : UnitaryFrame.V, ‖a‖ = 1 ∧ unitCoordinate A J α hs ht E p q u = UnitaryFrame.line a := by
  obtain ⟨a,ha,he,-,-⟩ := exists_unitDual_coordinate_line A J α hs ht E hE p hq u hu
  refine ⟨a,ha,?_⟩
  unfold unitCoordinate
  rw [← unitDual_encode A J α hs ht E hE]
  exact he

include hE in
lemma coordinateWedge_actual (p : A.centers) {q y : Space}
    (hq : q ∈ (E p).chart.domain) (hy : y ∈ (E p).chart.domain)
    (u v : MetricUnit (hermitianMetric J α hs ht))
    (hu : (extChartAt Model p.val).symm y = u.val.proj)
    (hv : (extChartAt Model p.val).symm q = v.val.proj)
    (K : Space × Space → UnitaryFrame.W →L[ℝ] UnitaryFrame.W) :
    unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
      (coordinateMatrix J α ht A E p K (q,y)
        (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) =
      ⟪unitCoordinate A J α hs ht E p y u,
        K (q,y) (UnitaryFrame.star (unitCoordinate A J α hs ht E p q v))⟫ := by
  obtain ⟨a,-,hea,-,hpa⟩ := exists_unitDual_coordinate_line A J α hs ht E hE p hy u hu
  obtain ⟨b,-,heb,hdb,-⟩ := exists_unitDual_coordinate_line A J α hs ht E hE p hq v hv
  have ha : unitCoordinate A J α hs ht E p y u = UnitaryFrame.line a := by
    unfold unitCoordinate
    rw [← unitDual_encode A J α hs ht E hE]
    exact hea
  have hb : unitCoordinate A J α hs ht E p q v = UnitaryFrame.line b := by
    unfold unitCoordinate
    rw [← unitDual_encode A J α hs ht E hE]
    exact heb
  rw [ha,hb,unitFrameFunctional_eq A J α hs ht E hE,← unitDual_starDirection A J α hs ht E hE]
  change framePairing A J α ht E (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val
    u.val.proj (coordinateEncode J α ht A E p y (K (q,y)
      (coordinateDecode J α ht A E p q _))) = _
  rw [hdb,hpa]

include hE in
lemma gammaNormalWedge_actual_angular_oai (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ z ∈ (E p).normalCompact,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
      (extChartAt Model p.val).symm z.1 = v.val.proj →
      (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
        (normalAngular A J α hs ht E p z u v)^2 -
        (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z.2‖/r)^N ≤
        unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
          (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
            (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
            (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by
  obtain ⟨C,hC,hbound⟩ := leadingCoordinate_gamma_angular_global J α ht p.val (E p).chart
    (E p).metricExtension (E p).frameExtension hs (E p).metric_smooth (E p).frame_smooth
    (Metric.closedBall (extChartAt Model p.val p.val) (E p).radius) (isCompact_closedBall _ _)
    (fun _ hq => (E p).actual hq)
  refine ⟨C,hC,fun N r hr T z hz u v hu hv => ?_⟩
  have hd := (E p).physicalCompact_domain ⟨z,hz,rfl⟩
  change z.1 ∈ (E p).chart.domain ∧
    normalMap (E p).metricExtension (E p).frameExtension z.1 z.2 ∈ (E p).chart.domain at hd
  obtain ⟨a,ha,hea⟩ := unitCoordinate_line A J α hs ht E hE p hd.2 u hu
  obtain ⟨b,hb,heb⟩ := unitCoordinate_line A J α hs ht E hE p hd.1 v hv
  rw [coordinateWedge_actual A J α hs ht E hE p hd.1 hd.2 u v hu hv,
    gammaPartitionLeading_apply J α ht A E hr T p hz,smul_apply,hea,heb]
  have hstar := normalGauge_commutes J α ht p.val (E p).chart (E p).metricExtension
    (E p).frameExtension hs (E p).metric_smooth (E p).frame_smooth
    (((E p).actual hz.1).center J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension).1 z.2
  have hstar' := congrArg (fun L : UnitaryFrame.W →L[ℝ] UnitaryFrame.W => L (UnitaryFrame.line b)) hstar
  change normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
    (UnitaryFrame.star (UnitaryFrame.line b)) =
      UnitaryFrame.star (normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
        (UnitaryFrame.line b)) at hstar'
  rw [hstar',inner_smul_right]
  have hp := coordinatePartition_bounds A p z.1
  have hχ := (E p).normalCutoff.nonneg (x := z.2)
  have h := hbound N r hr T (coordinatePartition A p) (E p).normalCutoff z.1 hz.1 z.2
    (mul_nonneg hp.1 hχ)
    ((mul_le_mul_of_nonneg_right hp.2 hχ).trans
      (by simpa only [one_mul] using (E p).normalCutoff.le_one (x := z.2))) a b ha hb
  rw [leadingCoordinate_gamma J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension hr] at h
  simpa only [normalAngular,hea,heb,smul_apply,UnitaryFrame.star_smul,inner_smul_right] using h

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular_oai.{u_1}
