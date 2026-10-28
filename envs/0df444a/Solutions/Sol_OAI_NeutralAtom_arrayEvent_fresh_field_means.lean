-- Prove2me | solution 1 for OAI.NeutralAtom.arrayEvent_fresh_field_means
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:32:16.001946+00:00
-- url     : https://prove2.me/submissions/79a7df8d-b04b-498f-bbf1-6c6e80d0f837

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfFunctionalUniformBound
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma tfBregman_nonneg {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    0 ≤ tfBregman f g := by
  rw [tfBregman_formula hf hg]
  apply integral_nonneg_of_ae
  filter_upwards [hf,hg] with x hx hy
  exact tf_power_tangent hx hy
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
lemma tfEnergy_minimizer_expansion {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω))
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ h, TFNonneg h → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W h) :
    tfEnergy hΩ c W g-tfEnergy hΩ c W f =
      tfCoulomb Ω (g-f) (g-f)/2+c*tfBregman f g+
        ∫ x in Ω, max (tfPotential f x-W x) 0*g x := by
  rw [tfEnergy_expansion hΩ c W hf,map_sub,tfGradientField_self hΩ c W hf hm,sub_zero,
    tfFieldContinuous_apply]
  congr 1
  apply integral_congr_ae
  filter_upwards [tfEuler_equation hΩ hc W hf hm] with x hx
  rw [hx.2]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_BallCloudDuality
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ

lemma raw_coulomb_cauchy {f g : Space → ℝ}
    (hf : MemLp f TFExponent (volume.restrict Ω))
    (hg : MemLp g TFExponent (volume.restrict Ω))
    (hfs : ∀ x∉Ω, f x=0) (hgs : ∀ x∉Ω, g x=0) :
    (coulombBilinear f g)^2 ≤ coulombBilinear f f*coulombBilinear g g := by
  have he := tfExtend_toLp hΩ hf hfs
  have he' := tfExtend_toLp hΩ hg hgs
  have hh := tfCoulomb_cauchy hΩ (hf.toLp f) (hg.toLp g)
  change (coulombBilinear (tfExtend Ω (hf.toLp f)) (tfExtend Ω (hg.toLp g)))^2≤
    coulombBilinear (tfExtend Ω (hf.toLp f)) (tfExtend Ω (hf.toLp f))*
      coulombBilinear (tfExtend Ω (hg.toLp g)) (tfExtend Ω (hg.toLp g)) at hh
  rwa [coulombBilinear_congr_ae he he',coulombBilinear_congr_ae he he,
    coulombBilinear_congr_ae he' he'] at hh

lemma raw_coulomb_ballCloud_duality {f : Space → ℝ}
    (hf : MemLp f TFExponent (volume.restrict Ω)) (hfs : ∀ x∉Ω, f x=0)
    (y : Space) {a : ℝ} (ha : 0<a) (hb : Metric.ball y a⊆Ω) :
    (coulombBilinear f (ballCloud y a 1))^2≤(5/(2*a))*coulombBilinear f f := by
  have hg : MemLp (ballCloud y a 1) TFExponent (volume.restrict Ω) :=
    MemLp.of_bound (ballCloud_measurable a 1 y).aestronglyMeasurable
      (1/(4*Real.pi/3*a^3)) (Eventually.of_forall (fun z => by
        change ‖uniformBall a 1 (z-y)‖≤_
        rw [Real.norm_of_nonneg (uniformBall_nonneg ha zero_le_one (z-y))]
        exact uniformBall_le ha zero_le_one _))
  have hgs : ∀ x∉Ω, ballCloud y a 1 x=0 := by
    intro x hx
    change (Metric.ball (0:Space) a).indicator (fun _ => 1/(4*Real.pi/3*a^3)) (x-y)=0
    apply indicator_of_notMem
    intro hh
    apply hx
    apply hb
    simpa only [Metric.mem_ball,dist_zero_right,dist_eq_norm,sub_zero] using hh
  have H := raw_coulomb_cauchy hΩ hf hg hfs hgs
  have hq := raw_coulomb_nonneg hΩ hf hfs
  have HG := mul_le_mul_of_nonneg_left (ballCloud_coulombBilinear_bound ha zero_le_one y) hq
  apply H.trans
  convert HG using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_HarmonicInterior
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom
theorem dirPartial_mul {f g : Position → ℝ} {x v : Position}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dirPartial (fun y => f y*g y) v x = f x*dirPartial g v x+g x*dirPartial f v x := by
  change fderiv ℝ (f*g) x v = _
  rw [fderiv_mul hf hg]
  simp [dirPartial]

theorem dirPartial_add {f g : Position → ℝ} {x v : Position}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dirPartial (fun y => f y+g y) v x = dirPartial f v x+dirPartial g v x := by
  change fderiv ℝ (f+g) x v = _
  rw [fderiv_add hf hg]
  rfl

theorem coordinateLaplacian_mul {f g : Position → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Position) :
    coordinateLaplacian (fun y => f y*g y) x =
      f x*coordinateLaplacian g x+g x*coordinateLaplacian f x+
        2*∑ a : Fin 3, dirPartial f (axis a) x*dirPartial g (axis a) x := by
  have hf1 := hf.differentiable (by norm_num)
  have hg1 := hg.differentiable (by norm_num)
  have hpf (a) : Differentiable ℝ (dirPartial f (axis a)) :=
    (contDiff_partial (n := 1) hf (axis a)).differentiable (by norm_num)
  have hpg (a) : Differentiable ℝ (dirPartial g (axis a)) :=
    (contDiff_partial (n := 1) hg (axis a)).differentiable (by norm_num)
  rw [coordinateLaplacian_eq_partials (hf.mul hg).contDiffAt,
    coordinateLaplacian_eq_partials hg.contDiffAt,
    coordinateLaplacian_eq_partials hf.contDiffAt]
  have hh (a : Fin 3) : dirPartial (dirPartial (fun y => f y*g y) (axis a)) (axis a) x =
      f x*dirPartial (dirPartial g (axis a)) (axis a) x+
      g x*dirPartial (dirPartial f (axis a)) (axis a) x+
      2*(dirPartial f (axis a) x*dirPartial g (axis a) x) := by
    have heq : dirPartial (fun y => f y*g y) (axis a) =
        fun y => f y*dirPartial g (axis a) y+g y*dirPartial f (axis a) y :=
      funext (fun y => dirPartial_mul (hf1 y) (hg1 y))
    rw [heq, dirPartial_add
      (f := fun y => f y*dirPartial g (axis a) y)
      (g := fun y => g y*dirPartial f (axis a) y)
      (by simpa only [Pi.mul_def] using (hf1 x).mul (hpg a x))
      (by simpa only [Pi.mul_def] using (hg1 x).mul (hpf a x)),
      dirPartial_mul (hf1 x) (hpg a x), dirPartial_mul (hg1 x) (hpf a x)]
    ring
  simp_rw [hh, Finset.sum_add_distrib, Finset.mul_sum]

theorem regularizedPartial_tendsto {ε : ℕ → ℝ} (hε : ∀ n, ε n ≠ 0)
    (hlim : Tendsto ε atTop (𝓝 0)) (a : Fin 3) {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => dirPartial (regularizedKernel (ε n)) (axis a) x)
      atTop (𝓝 (coulombPartial a x)) := by
  simp only [dirPartial_regularizedKernel (hε _)]
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  exact tendsto_const_nhds.mul (hh.rpow_const (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))))

theorem dirPartial_regularizedKernel_bound {ε : ℝ} (hε : ε ≠ 0)
    (a : Fin 3) {x : Position} (hx : x ≠ 0) :
    ‖dirPartial (regularizedKernel ε) (axis a) x‖ ≤ (coulombKernel x)^2 := by
  rw [dirPartial_regularizedKernel hε]
  simp only [norm_mul, norm_neg, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg ε)) (-3/2 : ℝ))]
  have hnorm : |x a| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x a
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr : (‖x‖^2+ε^2)^(-3/2 : ℝ) ≤ (‖x‖^2)^(-3/2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by norm_num)
  have he : ‖x‖*(‖x‖^2)^(-3/2 : ℝ) = (coulombKernel x)^2 := by
    rw [← Real.rpow_natCast_mul (norm_nonneg x)]
    norm_num [Real.rpow_neg hpos.le, coulombKernel]
    field_simp
  exact (mul_le_mul hnorm hr (by positivity) (norm_nonneg x)).trans_eq he

theorem locallyIntegrable_coulombKernel_sq :
    LocallyIntegrable (fun x => (coulombKernel x)^2) volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_sq_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

theorem regularizedPartial_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (a : Fin 3) {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, dirPartial (regularizedKernel (ε n)) (axis a) x*φ x)
      atTop (𝓝 (∫ x, coulombPartial a x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => (coulombKernel x)^2*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel_sq.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => (coulombKernel x)^2*‖φ x‖)
  · intro n
    exact ((contDiff_partial (n := ∞) (by simpa using contDiff_regularizedKernel (hε n).ne')
      (axis a)).continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (dirPartial_regularizedKernel_bound (hε n).ne' a hx)
      (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedPartial_tendsto (fun n => (hε n).ne') hlim a hx).mul_const (φ x)

theorem weak_harmonic_reproduction {h χ : Position → ℝ} {U : Set Position}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    (∫ x, coulombKernel x*(h x*coordinateLaplacian χ x)) +
      2*∑ a : Fin 3, ∫ x, coulombPartial a x*(h x*dirPartial χ (axis a) x) =
      4*Real.pi*(h 0*χ 0) := by
  let ε : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hcdelta : Continuous (coordinateLaplacian χ) := continuous_coordinateLaplacian hχ2
  have hcsdelta : HasCompactSupport (coordinateLaplacian χ) :=
    hasCompactSupport_coordinateLaplacian hχc
  have hcp (a : Fin 3) : ContDiff ℝ ∞ (dirPartial χ (axis a)) :=
    contDiff_partial (by simpa using hχ) (axis a)
  have hcsp (a : Fin 3) := hasCompactSupport_partial hχc (axis a)
  have hn (n : ℕ) :
      (∫ x, regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)) +
        2*∑ a : Fin 3, ∫ x, dirPartial (regularizedKernel (ε n)) (axis a) x*
          (h x*dirPartial χ (axis a) x) =
        ∫ x, regularizedCharge (ε n) x*(h x*χ x) := by
    have hK := contDiff_regularizedKernel (hε n).ne'
    have hK2 : ContDiff ℝ 2 (regularizedKernel (ε n)) :=
      hK.of_le (by exact WithTop.coe_le_coe.mpr le_top)
    have hpK (a : Fin 3) : Continuous (dirPartial (regularizedKernel (ε n)) (axis a)) :=
      (contDiff_partial (n := ∞) (by simpa using hK) (axis a)).continuous
    have hq : Continuous (regularizedCharge (ε n)) := by
      have heq : regularizedCharge (ε n) = fun x => -coordinateLaplacian (regularizedKernel (ε n)) x := by
        ext x
        rw [laplacian_regularizedKernel (hε n).ne']
        ring
      rw [heq]
      exact (continuous_coordinateLaplacian hK2).neg
    have hiK : Integrable (fun x => regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)) :=
      (hK.continuous.mul (hh.mul hcdelta)).integrable_of_hasCompactSupport
        (hcsdelta.mul_left.mul_left)
    have hiq : Integrable (fun x => regularizedCharge (ε n) x*(h x*χ x)) :=
      (hq.mul (hh.mul hχ.continuous)).integrable_of_hasCompactSupport (hχc.mul_left.mul_left)
    have hip (a : Fin 3) : Integrable (fun x => dirPartial (regularizedKernel (ε n)) (axis a) x*
        (h x*dirPartial χ (axis a) x)) :=
      ((hpK a).mul (hh.mul (hcp a).continuous)).integrable_of_hasCompactSupport
        ((hcsp a).mul_left.mul_left)
    have he := hharm (fun x => χ x*regularizedKernel (ε n) x) (hχ.mul hK)
      hχc.mul_right (by exact (closure_mono (Function.support_mul_subset_left _ _)).trans hχU)
    have heq : (fun x => h x*coordinateLaplacian (fun y => χ y*regularizedKernel (ε n) y) x) =
        fun x => (regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)-
          regularizedCharge (ε n) x*(h x*χ x)) +
          2*∑ a : Fin 3, dirPartial (regularizedKernel (ε n)) (axis a) x*
              (h x*dirPartial χ (axis a) x) := by
      ext x
      rw [coordinateLaplacian_mul hχ2 hK2, laplacian_regularizedKernel (hε n).ne']
      simp only [Fin.sum_univ_three]
      ring
    have hisub : Integrable (fun x => regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)-
        regularizedCharge (ε n) x*(h x*χ x)) := by
      simpa only [Pi.sub_def] using hiK.sub hiq
    have hisum : Integrable (fun x => 2*∑ a : Fin 3,
        dirPartial (regularizedKernel (ε n)) (axis a) x*(h x*dirPartial χ (axis a) x)) :=
      (integrable_finsetSum Finset.univ (fun a _ => hip a)).const_mul 2
    rw [heq, integral_add hisub hisum,
      integral_sub hiK hiq, integral_const_mul, integral_finsetSum _ (fun a _ => hip a)] at he
    simp only [zero_mul, integral_zero] at he
    linarith
  have h1 := regularizedKernel_integral_tendsto hε hεlim (hh.mul hcdelta) hcsdelta.mul_left
  have h2 := tendsto_finsetSum Finset.univ (fun a _ =>
    regularizedPartial_integral_tendsto hε hεlim a (hh.mul (hcp a).continuous) (hcsp a).mul_left)
  have h3 := regularizedCharge_tendsto_dirac hε hεlim (hh.mul hχ.continuous) hχc.mul_left
  exact tendsto_nhds_unique ((h1.add (h2.const_mul 2)).congr' (Filter.Eventually.of_forall hn)) h3

theorem contDiffAt_coulombKernel {x : Position} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ coulombKernel x := by
  have he : coulombKernel = fun x : Position => (‖x‖^2)^(-1/2 : ℝ) :=
    funext coulombKernel_eq_rpow
  rw [he]
  exact (contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

theorem contDiffAt_coulombPartial (a : Fin 3) {x : Position} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (coulombPartial a) x := by
  exact (EuclideanSpace.proj a).contDiff.contDiffAt.neg.mul
    ((contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))

theorem cutoffHarmonicKernel_eq_zero_of_eventually_const {χ : Position → ℝ} {x : Position}
    {c : ℝ} (hχ : χ =ᶠ[𝓝 x] fun _ => c) : cutoffHarmonicKernel χ x = 0 := by
  have hdelta : coordinateLaplacian χ x = 0 := by
    rw [coordinateLaplacian_congr_nhds hχ]
    simp [coordinateLaplacian]
  have hp (a : Fin 3) : dirPartial χ (axis a) x = 0 := by
    unfold dirPartial
    rw [hχ.fderiv_eq]
    simp
  simp [cutoffHarmonicKernel, hdelta, hp]

theorem hasCompactSupport_cutoffHarmonicKernel {χ : Position → ℝ}
    (hχc : HasCompactSupport χ) : HasCompactSupport (cutoffHarmonicKernel χ) := by
  apply hχc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra h
  exact hx (cutoffHarmonicKernel_eq_zero_of_eventually_const
    (notMem_tsupport_iff_eventuallyEq.mp h))

theorem contDiff_cutoffHarmonicKernel {χ : Position → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : Position)] fun _ => (1 : ℝ)) :
    ContDiff ℝ ∞ (cutoffHarmonicKernel χ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have he : cutoffHarmonicKernel χ =ᶠ[𝓝 (0 : Position)] fun _ => (0 : ℝ) := by
      filter_upwards [hχ0.eventually_nhds] with x hx
      exact cutoffHarmonicKernel_eq_zero_of_eventually_const hx
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hp (a : Fin 3) : ContDiffAt ℝ ∞ (dirPartial χ (axis a)) x :=
      (contDiff_partial (n := ∞) (by simpa using hχ) (axis a)).contDiffAt
    apply ContDiffAt.div_const
    apply ContDiffAt.add
    · exact (contDiffAt_coulombKernel hx).mul (contDiff_coordinateLaplacian hχ).contDiffAt
    · apply contDiffAt_const.mul
      apply ContDiffAt.sum
      intro a _
      exact (contDiffAt_coulombPartial a hx).mul (hp a)

theorem coulombPartial_bound (a : Fin 3) (x : Position) :
    ‖coulombPartial a x‖ ≤ (coulombKernel x)^2 := by
  by_cases hx : x = 0
  · subst x
    simp [coulombPartial, coulombKernel]
  · have hε : ∀ n : ℕ, ((n:ℝ)+1)⁻¹ ≠ 0 := fun n => by positivity
    have hlim : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact le_of_tendsto (regularizedPartial_tendsto hε hlim a hx).norm
      (Filter.Eventually.of_forall (fun n => dirPartial_regularizedKernel_bound (hε n) a hx))

theorem measurable_coulombPartial (a : Fin 3) : Measurable (coulombPartial a) := by
  exact (EuclideanSpace.proj a).continuous.measurable.neg.mul
    ((continuous_norm.measurable.pow_const (2 : ℕ)).pow_const (-3/2 : ℝ))

theorem coulombPartial_integrable_mul_compact (a : Fin 3) {φ : Position → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => coulombPartial a x*φ x) := by
  have hb : Integrable (fun x => (coulombKernel x)^2*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel_sq.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply hb.mono' ((measurable_coulombPartial a).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖coulombPartial a x*φ x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (coulombPartial_bound a x) (norm_nonneg _))

theorem weak_harmonic_reproduction_kernel {h χ : Position → ℝ} {U : Set Position}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hχone : χ 0 = 1) :
    (∫ x, cutoffHarmonicKernel χ x*h x) = h 0 := by
  have hcdelta := (contDiff_coordinateLaplacian hχ).continuous
  have hcsdelta := hasCompactSupport_coordinateLaplacian hχc
  have hcp (a : Fin 3) : Continuous (dirPartial χ (axis a)) :=
    (contDiff_partial (n := ∞) (by simpa using hχ) (axis a)).continuous
  have hcsp (a : Fin 3) := hasCompactSupport_partial hχc (axis a)
  have hiK : Integrable (fun x => coulombKernel x*(h x*coordinateLaplacian χ x)) := by
    simpa only [smul_eq_mul, Pi.mul_apply] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport
        (hh.mul hcdelta) hcsdelta.mul_left
  have hip (a : Fin 3) : Integrable (fun x => coulombPartial a x*(h x*dirPartial χ (axis a) x)) :=
    coulombPartial_integrable_mul_compact a (hh.mul (hcp a)) (hcsp a).mul_left
  have hisum : Integrable (fun x => 2*∑ a : Fin 3, coulombPartial a x*(h x*dirPartial χ (axis a) x)) :=
    (integrable_finsetSum Finset.univ (fun a _ => hip a)).const_mul 2
  have heq : (fun x => cutoffHarmonicKernel χ x*h x) = fun x =>
      (4*Real.pi)⁻¹*((coulombKernel x*(h x*coordinateLaplacian χ x))+
      2*∑ a : Fin 3, coulombPartial a x*(h x*dirPartial χ (axis a) x)) := by
    ext x
    simp only [cutoffHarmonicKernel, Fin.sum_univ_three]
    ring
  rw [heq, integral_const_mul, integral_add hiK hisum, integral_const_mul,
    integral_finsetSum _ (fun a _ => hip a), weak_harmonic_reproduction hh hharm hχ hχc hχU, hχone]
  field_simp

theorem coordinateLaplacian_sub_right (φ : Position → ℝ) (x z : Position) :
    coordinateLaplacian (fun y => φ (y-z)) x = coordinateLaplacian φ (x-z) := by
  unfold coordinateLaplacian
  apply Finset.sum_congr rfl
  intro a _
  have he : (fun t : ℝ => φ ((x+t • axis a)-z)) = fun t => φ ((x-z)+t • axis a) := by
    ext t
    congr 1
    abel
  rw [he]

theorem HasWeakLaplacian.translate {h q : Position → ℝ} {U : Set Position}
    (hh : HasWeakLaplacian h U q) (z : Position) :
    HasWeakLaplacian (fun x => h (z+x)) {x | z+x ∈ U} (fun x => q (z+x)) := by
  intro φ hφ hφc hφU
  have hc : ContDiff ℝ ∞ (fun y => φ (y-z)) := hφ.comp (contDiff_id.sub contDiff_const)
  have hcs : HasCompactSupport (fun y => φ (y-z)) :=
    hφc.comp_homeomorph (Homeomorph.subRight z)
  have hs : tsupport (fun y => φ (y-z)) ⊆ U := by
    have hsub := tsupport_comp_subset_preimage φ (show Continuous (fun y : Position => y-z) by fun_prop)
    intro y hy
    have hy' : y-z ∈ tsupport φ := hsub hy
    have hh' := hφU hy'
    change z+(y-z) ∈ U at hh'
    rw [show z+(y-z) = y by abel] at hh'
    exact hh'
  have he := hh (fun y => φ (y-z)) hc hcs hs
  simp_rw [coordinateLaplacian_sub_right] at he
  have hl := integral_add_left_eq_self (μ := volume) (fun y => h y*coordinateLaplacian φ (y-z)) z
  have hr := integral_add_left_eq_self (μ := volume) (fun y => q y*φ (y-z)) z
  simpa only [add_sub_cancel_left] using hl.trans (he.trans hr.symm)

theorem weak_harmonic_reproduction_at {h χ : Position → ℝ} {U : Set Position}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχone : χ 0 = 1)
    {z : Position} (hχU : ∀ x ∈ tsupport χ, z+x ∈ U) :
    (∫ x, cutoffHarmonicKernel χ (x-z)*h x) = h z := by
  have he := weak_harmonic_reproduction_kernel
    (hh.comp (show Continuous (fun x : Position => z+x) by fun_prop))
    (hharm.translate z) hχ hχc hχU hχone
  have hl := integral_add_left_eq_self (μ := volume) (fun x => cutoffHarmonicKernel χ (x-z)*h x) z
  simp only [add_sub_cancel_left] at hl
  simpa only [Function.comp_apply, add_zero] using hl.symm.trans he

theorem harmonic_value_bound {h χ : Position → ℝ} {U W : Set Position} {M : ℝ}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχone : χ 0 = 1)
    (hW : IsCompact W) (hM : ∀ x, ‖cutoffHarmonicKernel χ x‖ ≤ M)
    {z : Position} (hχU : ∀ x ∈ tsupport χ, z+x ∈ U)
    (hχW : ∀ x ∈ tsupport χ, z+x ∈ W) :
    ‖h z‖ ≤ M*(∫ x in W, ‖h x‖) := by
  have hzero : ∀ x, x ∉ W → cutoffHarmonicKernel χ (x-z)*h x = 0 := by
    intro x hx
    have hh' : x-z ∉ tsupport χ := by
      intro hm
      have he := hχW (x-z) hm
      rw [show z+(x-z)=x by abel] at he
      exact hx he
    rw [cutoffHarmonicKernel_eq_zero_of_eventually_const
      (notMem_tsupport_iff_eventuallyEq.mp hh'), zero_mul]
  rw [← weak_harmonic_reproduction_at hh hharm hχ hχc hχone hχU,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hi : IntegrableOn (fun x => M * ‖h x‖) W volume :=
    (hh.norm.continuousOn.integrableOn_compact hW).const_mul M
  have hb := norm_integral_le_of_norm_le
    (f := fun x => cutoffHarmonicKernel χ (x-z)*h x) hi
    (Filter.Eventually.of_forall (fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM (x-z)) (norm_nonneg _)))
  simpa only [integral_const_mul] using hb

theorem harmonic_difference_bound {h χ : Position → ℝ} {U W : Set Position} {L : NNReal}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0 : Position)] fun _ => (1 : ℝ)) (hW : IsCompact W)
    (hL : LipschitzWith L (cutoffHarmonicKernel χ))
    {z z' : Position} (hχU : ∀ x ∈ tsupport χ, z+x ∈ U)
    (hχU' : ∀ x ∈ tsupport χ, z'+x ∈ U)
    (hχW : ∀ x ∈ tsupport χ, z+x ∈ W)
    (hχW' : ∀ x ∈ tsupport χ, z'+x ∈ W) :
    ‖h z-h z'‖ ≤ (L:ℝ)*(∫ x in W, ‖h x‖)*‖z-z'‖ := by
  have hcQ := (contDiff_cutoffHarmonicKernel hχ hχ0).continuous
  have hi (v : Position) : IntegrableOn (fun x => cutoffHarmonicKernel χ (x-v)*h x) W :=
    ((hcQ.comp (show Continuous (fun x : Position => x-v) by fun_prop)).mul hh).continuousOn.integrableOn_compact hW
  have hrepro (v : Position) (hvU : ∀ x ∈ tsupport χ, v+x ∈ U)
      (hvW : ∀ x ∈ tsupport χ, v+x ∈ W) :
      (∫ x in W, cutoffHarmonicKernel χ (x-v)*h x) = h v := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact weak_harmonic_reproduction_at hh hharm hχ hχc hχ0.eq_of_nhds hvU
    · intro x hx
      have hh' : x-v ∉ tsupport χ := by
        intro hm
        have he := hvW (x-v) hm
        rw [show v+(x-v)=x by abel] at he
        exact hx he
      rw [cutoffHarmonicKernel_eq_zero_of_eventually_const
        (notMem_tsupport_iff_eventuallyEq.mp hh'), zero_mul]
  rw [← hrepro z hχU hχW, ← hrepro z' hχU' hχW', ← integral_sub (hi z) (hi z')]
  have hb : ∀ x, ‖cutoffHarmonicKernel χ (x-z)*h x-cutoffHarmonicKernel χ (x-z')*h x‖ ≤
      ((L:ℝ)*‖z-z'‖)*‖h x‖ := by
    intro x
    rw [← sub_mul, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have he := hL.norm_sub_le (x-z) (x-z')
    simpa only [show (x-z)-(x-z')=z'-z by abel, norm_sub_rev z' z] using he
  have hibound : IntegrableOn (fun x => ((L:ℝ)*‖z-z'‖)*‖h x‖) W volume :=
    (hh.norm.continuousOn.integrableOn_compact hW).const_mul _
  have hbound := norm_integral_le_of_norm_le hibound
    (Filter.Eventually.of_forall hb)
  rw [integral_const_mul] at hbound
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem harmonic_interior_estimates {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Position) (h : Position → ℝ), Continuous h →
      HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) →
      (∀ z ∈ Metric.closedBall c r, ‖h z‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖h z-h z'‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)*‖z-z'‖) := by
  let χ : ContDiffBump (0 : Position) := ⟨r/4, r/2, by linarith, by linarith⟩
  have hχ0 : (χ : Position → ℝ) =ᶠ[𝓝 (0 : Position)] fun _ => (1 : ℝ) :=
    χ.eventuallyEq_one
  have hQ := contDiff_cutoffHarmonicKernel χ.contDiff hχ0
  have hQc := hasCompactSupport_cutoffHarmonicKernel χ.hasCompactSupport
  obtain ⟨M, hM⟩ := hQc.exists_bound_of_continuous hQ.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hQc hQ (by simp)
  let C : ℝ := max M L+1
  have hLC : (L : ℝ) ≤ C := by
    dsimp [C]
    linarith [le_max_right M (L : ℝ)]
  have hMC : M ≤ C := by
    dsimp [C]
    linarith [le_max_left M (L : ℝ)]
  have hC : 0 < C := by
    dsimp [C]
    linarith [le_max_right M (L : ℝ), L.coe_nonneg]
  refine ⟨C, hC, ?_⟩
  intro c h hh hharm
  have hs {z : Position} (hz : z ∈ Metric.closedBall c r) :
      ∀ x ∈ tsupport (χ : Position → ℝ), z+x ∈ Metric.ball c (2*r) := by
    intro x hx
    rw [χ.tsupport_eq] at hx
    have hx' : ‖x‖ ≤ r/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hz' : ‖z-c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [Metric.mem_ball, dist_eq_norm, show z+x-c = (z-c)+x by abel]
    exact lt_of_le_of_lt ((norm_add_le _ _).trans (add_le_add hz' hx')) (by linarith)
  have hsW {z : Position} (hz : z ∈ Metric.closedBall c r) :
      ∀ x ∈ tsupport (χ : Position → ℝ), z+x ∈ Metric.closedBall c (2*r) :=
    fun x hx => Metric.ball_subset_closedBall (hs hz x hx)
  have hI : 0 ≤ ∫ x in Metric.closedBall c (2*r), ‖h x‖ := integral_nonneg (fun _ => norm_nonneg _)
  constructor
  · intro z hz
    exact (harmonic_value_bound hh hharm χ.contDiff χ.hasCompactSupport hχ0.eq_of_nhds
      (isCompact_closedBall c (2*r)) hM (hs hz) (hsW hz)).trans (mul_le_mul_of_nonneg_right hMC hI)
  · intro z hz z' hz'
    exact (harmonic_difference_bound hh hharm χ.contDiff χ.hasCompactSupport hχ0
      (isCompact_closedBall c (2*r)) hL (hs hz) (hs hz') (hsW hz) (hsW hz')).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLC hI) (norm_nonneg _))

theorem HasWeakLaplacian.congrOn {h g q : Position → ℝ} {U : Set Position}
    (hh : HasWeakLaplacian h U q) (he : Set.EqOn h g U) : HasWeakLaplacian g U q := by
  intro φ hφ hφc hφU
  calc
    (∫ x, g x*coordinateLaplacian φ x) = ∫ x, h x*coordinateLaplacian φ x := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change g x*coordinateLaplacian φ x = h x*coordinateLaplacian φ x
      by_cases hx : x ∈ tsupport φ
      · rw [he (hφU hx)]
      · simp only [coordinateLaplacian_eq_zero_of_notMem_tsupport hx, mul_zero]
    _ = _ := hh φ hφ hφc hφU

theorem harmonic_interior_estimates_local {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Position) (h : Position → ℝ),
      ContinuousOn h (Metric.ball c (3*r)) →
      HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) →
      (∀ z ∈ Metric.closedBall c r, ‖h z‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖h z-h z'‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)*‖z-z'‖) := by
  obtain ⟨C, hC, hest⟩ := harmonic_interior_estimates hr
  refine ⟨C, hC, ?_⟩
  intro c h hh hharm
  let η : ContDiffBump c := ⟨2*r, 5*r/2, by positivity, by linarith⟩
  let g : Position → ℝ := fun x => η x*h x
  have hgOn : ContinuousOn g (Metric.ball c (3*r)) := η.continuous.continuousOn.mul hh
  have hg : Continuous g := hgOn.continuous_of_tsupport_subset Metric.isOpen_ball (by
    intro x hx
    have hx' : x ∈ tsupport (η : Position → ℝ) :=
      closure_mono (Function.support_mul_subset_left _ _) hx
    rw [η.tsupport_eq] at hx'
    have hd : dist x c ≤ 5*r/2 := hx'
    exact lt_of_le_of_lt hd (by linarith))
  have he : Set.EqOn g h (Metric.closedBall c (2*r)) := by
    intro x hx
    dsimp [g]
    rw [η.one_of_mem_closedBall hx, one_mul]
  have hgarm : HasWeakLaplacian g (Metric.ball c (2*r)) (fun _ => 0) :=
    hharm.congrOn (fun x hx => (he (Metric.ball_subset_closedBall hx)).symm)
  have hI : (∫ x in Metric.closedBall c (2*r), ‖g x‖) =
      ∫ x in Metric.closedBall c (2*r), ‖h x‖ := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    change ‖g x‖ = ‖h x‖
    rw [he hx]
  have hes {z : Position} (hz : z ∈ Metric.closedBall c r) : g z = h z :=
    he (Metric.closedBall_subset_closedBall (by linarith) hz)
  obtain ⟨hval, hdiff⟩ := hest c g hg hgarm
  constructor
  · intro z hz
    simpa only [hes hz, hI] using hval z hz
  · intro z hz z' hz'
    simpa only [hes hz, hes hz', hI] using hdiff z hz z' hz'

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_HarmonicScale
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom

theorem local_harmonic_part {F σ ρ : Position → ℝ} {U : Set Position} {A : ℝ}
    (hU : IsOpen U) (hF : ContinuousOn F U)
    (hpoisson : HasWeakLaplacian F U (fun x => 4*Real.pi*σ x))
    (hρ : Integrable ρ) (hρpos : ∀ x, 0 ≤ ρ x) (hρbd : ∀ x, ρ x ≤ A)
    (he : Set.EqOn σ ρ U) :
    HasWeakLaplacian (fun x => F x+potentialOf ρ x) U (fun _ => 0) := by
  intro φ hφ hφc hφU
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hiF : Integrable (fun x => F x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx =>
      hU.continuousOn_iff.mp hF (hφU (tsupport_coordinateLaplacian_subset φ hx)))
      (continuous_coordinateLaplacian hφ2) (hasCompactSupport_coordinateLaplacian hφc)
  have hiP : Integrable (fun x => potentialOf ρ x*coordinateLaplacian φ x) :=
    ((potentialOf_continuous hρ hρpos hρbd).mul (continuous_coordinateLaplacian hφ2)).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateLaplacian hφc).mul_left
  have heq : (fun x => (F x+potentialOf ρ x)*coordinateLaplacian φ x) =
      fun x => F x*coordinateLaplacian φ x+potentialOf ρ x*coordinateLaplacian φ x := by
    ext x
    ring
  have hrho : (fun x => -(4*Real.pi)*ρ x*φ x) = fun x => -(4*Real.pi*σ x*φ x) := by
    ext x
    by_cases hx : x ∈ tsupport φ
    · rw [he (hφU hx)]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, neg_zero]
  rw [heq, integral_add hiF hiP, hpoisson φ hφ hφc hφU,
    potentialOf_weakLaplacian hρ φ hφ hφc (Set.subset_univ _), hrho, integral_neg]
  simp only [add_neg_cancel, zero_mul, integral_zero]

theorem HasWeakLaplacian.dilate {F q : Position → ℝ} {U : Set Position}
    {D : ℝ} (hD : 0 < D) (hw : HasWeakLaplacian F U q) :
    HasWeakLaplacian (fun x => D^4*F (D • x)) ((fun x => D • x) ⁻¹' U)
      (fun x => D^6*q (D • x)) := by
  intro φ hφ hc ht
  let e : Position ≃ₜ Position := Homeomorph.smul (Units.mk0 D⁻¹ (inv_ne_zero hD.ne'))
  let ψ : Position → ℝ := fun x => φ (D⁻¹ • x)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.const_smul D⁻¹)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e
  have hψt : tsupport ψ ⊆ U := by
    intro x hx
    have hx' : e x ∈ tsupport φ := by
      simpa only [ψ, show (fun x : Position => D⁻¹ • x) = e from rfl,
        ← Function.comp_def, tsupport_comp_eq_preimage, Set.mem_preimage] using hx
    have := ht hx'
    simpa only [Set.mem_preimage, e, Homeomorph.smul_apply, Units.smul_def,
      Units.val_mk0, smul_smul, mul_inv_cancel₀ hD.ne', one_smul] using this
  have hid (x : Position) : D⁻¹ • (D • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hD.ne', one_smul]
  have hLap (x : Position) : coordinateLaplacian ψ (D • x) =
      (D⁻¹)^2*coordinateLaplacian φ x := by
    change coordinateLaplacian (fun y => φ (D⁻¹ • y)) (D • x) = _
    rw [coordinateLaplacian_comp_smul, hid]
  have hleft := Measure.integral_comp_smul_of_nonneg volume
    (fun x => F x*coordinateLaplacian ψ x) D (hR := hD.le)
  have hright := Measure.integral_comp_smul_of_nonneg volume
    (fun x => q x*ψ x) D (hR := hD.le)
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul] at hleft hright
  simp_rw [hLap, show ∀ x, F (D • x)*((D⁻¹)^2*coordinateLaplacian φ x) =
    (D⁻¹)^2*(F (D • x)*coordinateLaplacian φ x) by intro x; ring,
    integral_const_mul] at hleft
  simp only [ψ, hid] at hright
  have hwe := hw ψ hψ hψc hψt
  have hEq : (∫ x, F (D • x)*coordinateLaplacian φ x) = D^2*(∫ x, q (D • x)*φ x) := by
    rw [hwe, ← hright] at hleft
    field_simp [hD.ne'] at hleft
    nlinarith [hleft]
  simp_rw [mul_assoc, integral_const_mul]
  rw [hEq]
  ring

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PoissonInterior
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
theorem poisson_interior_estimates (c : Position) {r A M : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F σ : Position → ℝ),
      ContinuousOn F (Metric.ball c (3*r)) →
      HasWeakLaplacian F (Metric.ball c (2*r)) (fun x => 4*Real.pi*σ x) →
      Integrable σ → (∀ x, 0 ≤ σ x) →
      (∀ x ∈ Metric.closedBall c (3*r), σ x ≤ A) →
      (∫ x in Metric.closedBall c (2*r), ‖F x‖) ≤ M →
      (∀ z ∈ Metric.closedBall c r, ‖F z‖ ≤ C) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖F z-F z'‖ ≤ C*‖z-z'‖) := by
  obtain ⟨HC, hHC, hest⟩ := harmonic_interior_estimates_local hr
  let W := Metric.closedBall c (3*r)
  let W' := Metric.closedBall c (2*r)
  let V := (volume W).toReal
  let V' := (volume W').toReal
  let PB := A*(∫ y in Metric.ball (0 : Position) 1, coulombKernel y)+A*V
  let LB := A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+A*V
  have hPB : 0 ≤ PB := add_nonneg (mul_nonneg hA (integral_nonneg coulombKernel_nonneg))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  have hLB : 0 ≤ LB := add_nonneg (mul_nonneg hA (integral_nonneg (fun y => sq_nonneg _)))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  let H := M+PB*V'
  have hH : 0 ≤ H := add_nonneg hM (mul_nonneg hPB ENNReal.toReal_nonneg)
  let C := HC*H+PB+LB+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro F σ hF hpoisson hσ hσpos hσbd hIF
  let ρ := W.indicator σ
  have hρ : Integrable ρ := hσ.indicator measurableSet_closedBall
  have hρpos : ∀ x, 0 ≤ ρ x := fun x => Set.indicator_nonneg (fun y _ => hσpos y) x
  have hρbd : ∀ x, ρ x ≤ A := by
    intro x
    by_cases hx : x ∈ W
    · simpa only [ρ, Set.indicator_of_mem hx] using hσbd x hx
    · simpa only [ρ, Set.indicator_of_notMem hx] using hA
  have hmass : (∫ x, ρ x) ≤ A*V := by
    rw [show ρ = W.indicator σ from rfl, integral_indicator measurableSet_closedBall]
    calc
      (∫ x in W, σ x) ≤ ∫ _ in W, A := integral_mono_ae hσ.integrableOn
        (integrableOn_const (isCompact_closedBall c (3*r)).measure_ne_top)
        ((ae_restrict_mem measurableSet_closedBall).mono (fun x hx => hσbd x hx))
      _ = A*V := by simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, V,
          measureReal_def, mul_comm]
  let P := potentialOf ρ
  have hPcont : Continuous P := potentialOf_continuous hρ hρpos hρbd
  have hPbd (x : Position) : ‖P x‖ ≤ PB := by
    have hp : 0 ≤ P x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρpos y))
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ => coulombKernel_le_one)
      hρ hρpos hρbd x).2.trans (by dsimp only [PB]; linarith)
  have hPlip (x y : Position) : ‖P x-P y‖ ≤ LB*‖x-y‖ :=
    (potentialOf_lipschitz_bound hρ hρpos hρbd x y).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [LB]; linarith) (norm_nonneg _))
  have hW' : W' ⊆ Metric.ball c (3*r) := by
    intro x hx
    change dist x c ≤ 2*r at hx
    change dist x c < 3*r
    linarith
  have hball : Metric.ball c (2*r) ⊆ Metric.ball c (3*r) :=
    Metric.ball_subset_ball (by linarith)
  let h : Position → ℝ := fun x => F x+P x
  have hhcont : ContinuousOn h (Metric.ball c (3*r)) := hF.add hPcont.continuousOn
  have hharm : HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) :=
    local_harmonic_part Metric.isOpen_ball (hF.mono hball) hpoisson hρ hρpos hρbd (by
      intro x hx
      have hxW : x ∈ W := by
        change dist x c ≤ 3*r
        exact (hball hx).le
      exact (Set.indicator_of_mem hxW σ).symm)
  have hiF : IntegrableOn (fun x => ‖F x‖) W' :=
    ((hF.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hih : IntegrableOn (fun x => ‖h x‖) W' :=
    ((hhcont.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hiPB : IntegrableOn (fun _ : Position => PB) W' :=
    integrableOn_const (isCompact_closedBall c (2*r)).measure_ne_top
  have hIh : (∫ x in W', ‖h x‖) ≤ H := by
    calc
      (∫ x in W', ‖h x‖) ≤ ∫ x in W', ‖F x‖+PB := integral_mono_ae hih (hiF.add hiPB)
        (Filter.Eventually.of_forall (fun x => (norm_add_le (F x) (P x)).trans
          (add_le_add le_rfl (hPbd x))))
      _ = (∫ x in W', ‖F x‖)+PB*V' := by
        rw [integral_add hiF hiPB, integral_const]
        simp only [Measure.restrict_apply_univ, smul_eq_mul, V', measureReal_def, mul_comm]
      _ ≤ H := by dsimp only [H]; linarith
  obtain ⟨hval, hdiff⟩ := hest c h hhcont hharm
  have hCval : HC*H+PB ≤ C := by dsimp [C]; linarith
  have hClip : HC*H+LB ≤ C := by dsimp [C]; linarith
  constructor
  · intro z hz
    calc
      ‖F z‖ = ‖h z-P z‖ := by dsimp [h]; rw [add_sub_cancel_right]
      _ ≤ ‖h z‖+‖P z‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)+PB := add_le_add (hval z hz) (hPbd z)
      _ ≤ HC*H+PB := by linarith [mul_le_mul_of_nonneg_left hIh hHC.le]
      _ ≤ C := hCval
  · intro z hz z' hz'
    calc
      ‖F z-F z'‖ = ‖(h z-h z')-(P z-P z')‖ := by congr 1; dsimp [h]; ring
      _ ≤ ‖h z-h z'‖+‖P z-P z'‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)*‖z-z'‖+LB*‖z-z'‖ :=
        add_le_add (hdiff z hz z' hz') (hPlip z z')
      _ ≤ (HC*H+LB)*‖z-z'‖ := by
        have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIh hHC.le)
          (norm_nonneg (z-z'))
        nlinarith
      _ ≤ C*‖z-z'‖ := mul_le_mul_of_nonneg_right hClip (norm_nonneg _)

end NeutralAtom

end
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff
namespace NeutralAtom

lemma HasWeakLaplacian.const_mul {F q : Position → ℝ} {U : Set Position}
    (h : HasWeakLaplacian F U q) (b : ℝ) :
    HasWeakLaplacian (fun x => b*F x) U (fun x => b*q x) := by
  intro φ hφ hφc ht
  simp_rw [mul_assoc, integral_const_mul]
  rw [h φ hφ hφc ht]

theorem poisson_unit_negative_oscillation {A M : ℝ} (hA : 0≤A) (hM : 0≤M) :
    ∃ C : ℝ, 0<C ∧ ∀ (F σ : Position → ℝ),
      ContinuousOn F (Metric.ball 0 3) →
      HasWeakLaplacian F (Metric.ball 0 2) (fun x => 4*Real.pi*σ x) →
      Integrable σ → (∀ x, 0≤σ x) →
      (∀ x ∈ Metric.closedBall 0 3, σ x≤A) →
      (∀ x ∈ Metric.closedBall 0 2, F x≤M) →
      volume.real (Metric.closedBall (0:Position) 2)*F 0 ≤
        (∫ x in Metric.closedBall 0 2, F x) →
      ∀ z ∈ Metric.closedBall (0:Position) 1,
        ‖F z-F 0‖ ≤ C*(1+max (-F 0) 0)*‖z‖ := by
  let V := volume.real (Metric.closedBall (0:Position) 2)
  have hV : 0≤V := ENNReal.toReal_nonneg
  obtain ⟨C,hC,H⟩ := poisson_interior_estimates (0:Position)
    (r:=1) (A:=A) (M:=V*(2*M+1)) (by norm_num) hA (by positivity)
  refine ⟨C,hC,?_⟩
  intro F σ hF hLap hσ hp hb hFM hmean z hz
  let T := 1+max (-F 0) 0
  have hT : 0<T := by dsimp [T]; positivity
  have hT1 : 1≤T := by dsimp [T]; linarith [le_max_right (-F 0) 0]
  have h2sub : Metric.closedBall (0:Position) 2⊆Metric.ball 0 3 := by
    intro x hx
    change dist x 0≤2 at hx
    change dist x 0<3
    linarith
  have hiF : IntegrableOn F (Metric.closedBall 0 2) :=
    (hF.mono h2sub).integrableOn_compact (isCompact_closedBall _ _)
  have hiabs := hiF.norm
  have hic : IntegrableOn (fun _ : Position => 2*M) (Metric.closedBall 0 2) :=
    integrableOn_const (isCompact_closedBall (0:Position) 2).measure_ne_top
  have hIF : (∫ x in Metric.closedBall 0 2, ‖F x‖) ≤ V*(2*M+max (-F 0) 0) := by
    calc
      (∫ x in Metric.closedBall 0 2, ‖F x‖) ≤
          ∫ x in Metric.closedBall 0 2, 2*M-F x := by
        apply integral_mono_ae hiabs (hic.sub hiF)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
        change ‖F x‖ ≤ 2*M-F x
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hFM x hx], by linarith [hFM x hx]⟩
      _ = V*(2*M)-(∫ x in Metric.closedBall 0 2, F x) := by
        rw [integral_sub hic hiF,integral_const]
        simp only [measureReal_restrict_apply_univ,smul_eq_mul,V]
      _ ≤ V*(2*M+max (-F 0) 0) := by
        change V*F 0 ≤ _ at hmean
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left (-F 0) 0) hV]
  have hIscaled : (∫ x in Metric.closedBall 0 2, ‖T⁻¹*F x‖) ≤ V*(2*M+1) := by
    simp_rw [norm_mul,Real.norm_eq_abs T⁻¹,abs_of_pos (inv_pos.mpr hT),integral_const_mul]
    have hnum : V*(2*M+max (-F 0) 0) ≤ T*(V*(2*M+1)) := by
      dsimp [T]
      nlinarith [mul_nonneg (mul_nonneg hV hM) (le_max_right (-F 0) 0)]
    calc
      _ ≤ T⁻¹*(T*(V*(2*M+1))) :=
        mul_le_mul_of_nonneg_left (hIF.trans hnum) (inv_nonneg.mpr hT.le)
      _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ hT.ne',one_mul]
  have hLap' : HasWeakLaplacian (fun x => T⁻¹*F x) (Metric.ball 0 2)
      (fun x => 4*Real.pi*(T⁻¹*σ x)) := by
    convert hLap.const_mul T⁻¹ using 1
    all_goals try with_reducible_and_instances rfl
    funext point
    ring
  obtain ⟨_,hdiff⟩ := H (fun x => T⁻¹*F x) (fun x => T⁻¹*σ x)
    (by simpa only [mul_one] using hF.const_mul T⁻¹) (by simpa using hLap')
    (hσ.const_mul _) (fun x => mul_nonneg (inv_nonneg.mpr hT.le) (hp x))
    (by
      intro x hx
      have hh : σ x≤A := hb x (by simpa using hx)
      have hinv : T⁻¹≤1 := inv_le_one_of_one_le₀ hT1
      exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hT.le)).trans
        (by simpa using mul_le_mul_of_nonneg_right hinv hA)) (by simpa using hIscaled)
  have hh := hdiff z (by simpa using hz) 0 (by simp)
  simp only [←mul_sub,norm_mul,Real.norm_eq_abs T⁻¹,abs_of_pos (inv_pos.mpr hT),sub_zero] at hh
  have hm := mul_le_mul_of_nonneg_left hh hT.le
  simpa only [←mul_assoc,mul_inv_cancel₀ hT.ne',one_mul,mul_comm T C,T] using hm

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_NegativeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace NeutralAtom

lemma negative_center_of_oscillation {v w θ B : ℝ} (hθ : 0 ≤ θ) (hθh : θ ≤ 1/2)
    (hB : 0 ≤ B) (hosc : ‖w-v‖ ≤ θ*(B+max (-v) 0)) :
    max (-v) 0 ≤ 2*max (-w) 0+2*θ*B := by
  have hz := (abs_le.mp (Real.norm_eq_abs (w-v) ▸ hosc)).2
  have hm : max (-v) 0 ≤ max (-w) 0+θ*(B+max (-v) 0) :=
    max_le (by linarith [le_max_left (-w) 0]) (by positivity)
  have hhalf := mul_le_mul_of_nonneg_right hθh (le_max_right (-v) 0)
  nlinarith

theorem negative_center_of_test_mass {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (W σ χ : X → ℝ) (v θ B K m : ℝ)
    (hθ : 0 ≤ θ) (hθh : θ ≤ 1/2) (hB : 0 ≤ B) (hK : 0 ≤ K) (hm : 0 < m)
    (hσ : ∀ᵐ x ∂μ, 0 ≤ σ x) (hχ : ∀ᵐ x ∂μ, 0 ≤ χ x ∧ χ x ≤ K)
    (hi : Integrable (fun x => σ x*χ x) μ)
    (hc : Integrable (fun x => max (-W x) 0*σ x) μ)
    (hmass : m ≤ ∫ x, σ x*χ x ∂μ)
    (hosc : ∀ᵐ x ∂μ, χ x≠0 → ‖W x-v‖ ≤ θ*(B+max (-v) 0)) :
    max (-v) 0 ≤ (2*K/m)*(∫ x, max (-W x) 0*σ x ∂μ)+2*θ*B := by
  let Y := max (-v) 0
  let d := 2*θ*B
  let I := ∫ x, max (-W x) 0*σ x ∂μ
  let q := ∫ x, σ x*χ x ∂μ
  have hI : 0 ≤ I := integral_nonneg_of_ae (hσ.mono fun x hx => mul_nonneg (le_max_right _ _) hx)
  have H : Y*q ≤ 2*K*I+d*q := by
    calc
      Y*q = ∫ x, Y*(σ x*χ x) ∂μ := (integral_const_mul _ _).symm
      _  ≤  ∫ x, (2*K)*(max (-W x) 0*σ x)+d*(σ x*χ x) ∂μ := by
        apply integral_mono_ae (hi.const_mul _) ((hc.const_mul _).add (hi.const_mul _))
        filter_upwards [hσ,hχ,hosc] with x hs hx ho
        change Y*(σ x*χ x) ≤ (2*K)*(max (-W x) 0*σ x)+d*(σ x*χ x)
        by_cases hz : χ x=0
        · simp only [hz,mul_zero,add_zero]
          positivity
        · have hy := negative_center_of_oscillation hθ hθh hB (ho hz)
          have hy' := mul_le_mul_of_nonneg_right hy (mul_nonneg hs hx.1)
          have hk := mul_le_mul_of_nonneg_left hx.2 (mul_nonneg (le_max_right (-W x) 0) hs)
          dsimp only [Y,d]
          nlinarith
      _ = 2*K*I+d*q := by rw [integral_add (hc.const_mul _) (hi.const_mul _),integral_const_mul,integral_const_mul]
  have hnon : 0 ≤ 2*K*I/m := div_nonneg (by positivity) hm.le
  have H' : Y ≤ 2*K*I/m+d := by
    by_cases hd : Y ≤ d
    · linarith
    · have hl : (Y-d)*m ≤ (Y-d)*q := mul_le_mul_of_nonneg_left hmass (by linarith)
      have hb : Y-d ≤ 2*K*I/m := (le_div_iff₀ hm).mpr (by nlinarith)
      linarith
  dsimp only [Y,d,I] at H'
  simpa only [div_mul_eq_mul_div] using H'

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFNegativeGap
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology
noncomputable section
namespace Coulomb

lemma rawTFNegativeError_congr_ae (Φ : Space → ℝ) {ρ σ ρ' σ' : Space → ℝ}
    (hρ : ρ =ᵐ[volume] ρ') (hσ : σ =ᵐ[volume] σ') :
    rawTFNegativeError Φ ρ σ=rawTFNegativeError Φ ρ' σ' := by
  have hp (x : Space) : (∫ z, coulombKernel (x-z)*ρ z)=∫ z, coulombKernel (x-z)*ρ' z :=
    integral_congr_ae (hρ.mono fun z hz => by simp only [hz])
  unfold rawTFNegativeError
  apply integral_congr_ae
  filter_upwards [hσ] with x hx
  rw [hp,hx]

lemma rawTFNegativeError_tfDensity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (hg : TFNonneg g) :
    rawTFNegativeError Φ (tfDensity Ω f) (tfDensity Ω g)=
      ∫ x in Ω, max (tfPotential f x-W x) 0*g x := by
  rw [rawTFNegativeError_congr_ae Φ (tfDensity_ae_tfExtend hΩ hf) (tfDensity_ae_tfExtend hΩ hg)]
  unfold rawTFNegativeError
  change (∫ x, max (tfPotential f x-Φ x) 0*tfExtend Ω g x)=_
  calc
    _ = ∫ x in Ω, max (tfPotential f x-Φ x) 0*g x := by
      rw [←integral_indicator hΩ]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈Ω <;> simp [tfExtend,hx]
    _ = _ := integral_congr_ae (hW.mono fun x hx => by rw [hx])

lemma raw_localTF_gap_identity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    coulombBilinear (fun x => tfDensity Ω f x-localTFDensity hΩ W x)
      (fun x => tfDensity Ω f x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) (tfDensity Ω f)+
      rawTFNegativeError Φ (localTFDensity hΩ W) (tfDensity Ω f)=
    rawThomasFermiEnergy Φ (tfDensity Ω f)-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  unfold localTFDensity
  rw [coulombBilinear_tfDensity_sub hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawTFBregman_tfDensity hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawTFNegativeError_tfDensity hΩ Φ W hW (localTFMinimizer_nonneg hΩ W) hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW (localTFMinimizer_nonneg hΩ W)]
  exact (tfEnergy_minimizer_expansion hΩ thomasFermiKineticConstant_pos W
    (localTFMinimizer_nonneg hΩ W) (fun _ hf => localTFMinimizer_minimizes hΩ W hf)).symm

lemma raw_localTF_gap_identity_density {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) σ+
      rawTFNegativeError Φ (localTFDensity hΩ W) σ=
    rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  have he := tfDensity_rawToTFLp hΩ hσ hp hs
  have hd : (fun x => tfDensity Ω (rawToTFLp σ hσ) x-localTFDensity hΩ W x) =ᵐ[volume]
      (fun x => σ x-localTFDensity hΩ W x) := he.sub EventuallyEq.rfl
  have H := raw_localTF_gap_identity hΩ Φ W hW (rawToTFLp_nonneg hσ hp)
  rwa [coulombBilinear_congr_ae hd hd,rawTFBregman_congr_ae EventuallyEq.rfl he,
    rawTFNegativeError_congr_ae Φ EventuallyEq.rfl he,rawThomasFermiEnergy_congr_ae Φ he] at H

lemma raw_localTF_refined_gap_density {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x)/2+
      rawTFNegativeError Φ (localTFDensity hΩ W) σ ≤
    rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  rw [←raw_localTF_gap_identity_density hΩ Φ W hW hσ hp hs]
  have he := tfDensity_rawToTFLp hΩ hσ hp hs
  have hb : 0 ≤ rawTFBregman (localTFDensity hΩ W) σ := by
    rw [←rawTFBregman_congr_ae EventuallyEq.rfl he]
    unfold localTFDensity
    rw [rawTFBregman_tfDensity hΩ (localTFMinimizer_nonneg hΩ W) (rawToTFLp_nonneg hσ hp)]
    exact mul_nonneg thomasFermiKineticConstant_pos.le
      (tfBregman_nonneg (localTFMinimizer_nonneg hΩ W) (rawToTFLp_nonneg hσ hp))
  linarith
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NewtonSubmean
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma ballCloud_coulomb_le {a M : ℝ} (ha : 0<a) (hM : 0≤M) (y x : Space) (hxy : x≠y) :
    (∫ z, coulombKernel (x-z)*ballCloud y a M z) ≤ M*coulombKernel (x-y) := by
  have he : (∫ z, coulombKernel (x-z)*ballCloud y a M z) =
      ∫ z, coulombKernel ((x-y)-z)*uniformBall a M z := by
    rw [← integral_sub_right_eq_self (fun z => coulombKernel ((x-y)-z)*uniformBall a M z) y]
    apply integral_congr_ae
    filter_upwards [] with z
    change coulombKernel (x-z)*uniformBall a M (z-y) = _
    rw [show (x-y)-(z-y)=x-z by abel]
  rw [he]
  have H := radial_coulomb_integral_le (uniformBall_integrable a M) (uniformBall_measurable a M)
    (uniformBall_nonneg ha hM) (uniformBall_le ha hM) (uniformBall_radial a M) (sub_ne_zero.mpr hxy)
  simpa only [uniformBall_mass ha,mul_comm M] using H

lemma potentialOf_ballCloud_integrable {ρ : Space → ℝ} (hi : Integrable ρ) (hm : Measurable ρ)
    {a : ℝ} (ha : 0<a) (y : Space) :
    Integrable (fun z => NeutralAtom.potentialOf ρ z*ballCloud y a 1 z) := by
  have H := (coulomb_pair_integrable hi hm (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y)
    (fun z => by
      change ‖uniformBall a 1 (z-y)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (uniformBall_nonneg ha zero_le_one (z-y))]
      exact uniformBall_le ha zero_le_one (z-y))).integral_prod_right
  apply H.congr
  filter_upwards [] with z
  simp only [NeutralAtom.potentialOf,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  change ρ x*ballCloud y a 1 z*coulombKernel (x-z) = coulombKernel (z-x)*ρ x*ballCloud y a 1 z
  rw [coulombKernel_sub_comm x z]
  ring

lemma potentialOf_ballCloud_le {ρ : Space → ℝ} (hi : Integrable ρ) (hm : Measurable ρ)
    (hp : ∀ x, 0≤ρ x) {a : ℝ} (ha : 0<a) (y : Space)
    (hK : Integrable (fun x => coulombKernel (y-x)*ρ x)) :
    (∫ z, NeutralAtom.potentialOf ρ z*ballCloud y a 1 z) ≤ NeutralAtom.potentialOf ρ y := by
  have H := coulomb_pair_integrable hi hm (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y)
    (fun z => by
      change ‖uniformBall a 1 (z-y)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (uniformBall_nonneg ha zero_le_one (z-y))]
      exact uniformBall_le ha zero_le_one (z-y))
  have he : (∫ z, NeutralAtom.potentialOf ρ z*ballCloud y a 1 z) =
      ∫ x, ∫ z, ρ x*ballCloud y a 1 z*coulombKernel (x-z) := by
    rw [integral_integral_swap H]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [NeutralAtom.potentialOf,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    change coulombKernel (z-x)*ρ x*ballCloud y a 1 z = ρ x*ballCloud y a 1 z*coulombKernel (x-z)
    rw [coulombKernel_sub_comm z x]
    ring
  rw [he]
  apply integral_mono_ae H.integral_prod_left hK
  filter_upwards [volume.ae_ne y] with x hxy
  have hh := mul_le_mul_of_nonneg_left (ballCloud_coulomb_le ha zero_le_one y x hxy) (hp x)
  simpa only [←integral_const_mul,one_mul,coulombKernel_sub_comm y x,mul_left_comm,mul_comm,mul_assoc] using hh

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma closedBall_ae_ball (y : Space) (a : ℝ) :
    Metric.closedBall y a =ᵐ[volume] Metric.ball y a := by
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume y a)] with x hx
  apply propext
  simp only [Metric.mem_closedBall,Metric.mem_ball,Metric.mem_sphere] at *
  exact ⟨fun h => lt_of_le_of_ne h hx,le_of_lt⟩

lemma integral_ballCloud (F : Space → ℝ) (y : Space) (a : ℝ) :
    (∫ x, F x*ballCloud y a 1 x) =
      (4*Real.pi/3*a^3)⁻¹*(∫ x in Metric.closedBall y a, F x) := by
  have he : (fun x => F x*ballCloud y a 1 x) =
      (Metric.ball y a).indicator (fun x => F x*(4*Real.pi/3*a^3)⁻¹) := by
    funext x
    have hd : x-y∈Metric.ball (0:Space) a ↔ x∈Metric.ball y a := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero]
    by_cases hx : x∈Metric.ball y a
    · simp only [ballCloud,uniformBall,indicator_of_mem hx,indicator_of_mem (hd.mpr hx),one_div]
    · simp only [ballCloud,uniformBall,indicator_of_notMem hx,indicator_of_notMem (not_congr hd |>.mpr hx),mul_zero]
  rw [he,integral_indicator measurableSet_ball,integral_mul_const,
    ←setIntegral_congr_set (closedBall_ae_ball y a),mul_comm]

lemma integral_closedBall_affine (F : Space → ℝ) (y : Space) {a : ℝ} (ha : 0<a) (r : ℝ) :
    (∫ z in Metric.closedBall (0:Space) r, F (y+a • z)) =
      (a^3)⁻¹*(∫ x in Metric.closedBall y (a*r), F x) := by
  let g := (Metric.closedBall y (a*r)).indicator F
  have he (z : Space) : g (y+a • z) =
      (Metric.closedBall (0:Space) r).indicator (fun x => F (y+a • x)) z := by
    have hz : y+a • z∈Metric.closedBall y (a*r) ↔ z∈Metric.closedBall (0:Space) r := by
      simp only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos ha,sub_zero]
      exact mul_le_mul_iff_right₀ ha
    by_cases h : z∈Metric.closedBall (0:Space) r
    · simp only [g,indicator_of_mem h,indicator_of_mem (hz.mpr h)]
    · simp only [g,indicator_of_notMem h,indicator_of_notMem (not_congr hz |>.mpr h)]
  have hh := Measure.integral_comp_smul_of_nonneg volume (fun x => g (y+x)) a (hR:=ha.le)
  simp only [Space,finrank_euclideanSpace_fin,smul_eq_mul] at hh
  simp_rw [he] at hh
  rw [integral_indicator measurableSet_closedBall,integral_add_left_eq_self] at hh
  simpa only [g,integral_indicator measurableSet_closedBall] using hh

lemma volume_closedBall_three (y : Space) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall y r) = 4*Real.pi/3*r^3 := by
  rw [Measure.addHaar_real_closedBall_eq_addHaar_real_ball,
    Measure.addHaar_real_ball_center,volume_real_ball_three r hr]

lemma submean_affine {F : Space → ℝ} (y : Space) {a : ℝ} (ha : 0<a)
    (hm : F y ≤ ∫ x, F x*ballCloud y (2*a) 1 x) :
    volume.real (Metric.closedBall (0:Space) 2)*(a^4*F y) ≤
      ∫ z in Metric.closedBall (0:Space) 2, a^4*F (y+a • z) := by
  rw [integral_ballCloud] at hm
  rw [integral_const_mul,integral_closedBall_affine F y ha,volume_closedBall_three _ (by norm_num)]
  have hV : 0<4*Real.pi/3*(2*a)^3 := by positivity
  have hi : (4*Real.pi/3*(2*a)^3)*F y ≤ (∫ x in Metric.closedBall y (2*a), F x) := by
    have hh := mul_le_mul_of_nonneg_left hm hV.le
    simpa only [←mul_assoc,mul_inv_cancel₀ hV.ne',one_mul] using hh
  have hh := mul_le_mul_of_nonneg_left hi (show 0≤a^4*(a^3)⁻¹ by positivity)
  rw [show a*2=2*a by ring]
  convert hh using 1 <;> first | rfl | field_simp [ha.ne']

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ScaledOscillation
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom

lemma affine_ball_distance (y z : Position) {a : ℝ} (ha : 0<a) :
    dist (y+a • z) y = a*‖z‖ := by
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem poisson_scaled_negative_oscillation {A M : ℝ} (hA : 0≤A) (hM : 0≤M) :
    ∃ C : ℝ, 0<C ∧ ∀ (F σ : Position → ℝ) (y : Position) (a : ℝ), 0<a →
      ContinuousOn F (Metric.ball y (3*a)) →
      HasWeakLaplacian F (Metric.ball y (2*a)) (fun x => 4*Real.pi*σ x) →
      Integrable σ → (∀ x, 0≤σ x) →
      (∀ x ∈ Metric.closedBall y (3*a), σ x≤A/a^6) →
      (∀ x ∈ Metric.closedBall y (2*a), F x≤M/a^4) →
      F y ≤ (∫ x, F x*Coulomb.ballCloud y (2*a) 1 x) →
      ∀ z ∈ Metric.closedBall y a,
        ‖F z-F y‖ ≤ C*(‖z-y‖/a)*((a^4)⁻¹+max (-F y) 0) := by
  obtain ⟨C,hC,H⟩ := poisson_unit_negative_oscillation hA hM
  refine ⟨C,hC,?_⟩
  intro F σ y a ha hF hLap hi hp hb hcap hmean z hz
  let G := fun x => a^4*F (y+a • x)
  let τ := fun x => a^6*σ (y+a • x)
  have hmap {R : ℝ} {x : Position} (hx : x∈Metric.ball 0 R) :
      y+a • x∈Metric.ball y (R*a) := by
    rw [Metric.mem_ball,affine_ball_distance y x ha]
    have h := mul_lt_mul_of_pos_left (show ‖x‖<R by simpa using hx) ha
    simpa only [mul_comm a R] using h
  have hmapc {R : ℝ} {x : Position} (hx : x∈Metric.closedBall 0 R) :
      y+a • x∈Metric.closedBall y (R*a) := by
    rw [Metric.mem_closedBall,affine_ball_distance y x ha]
    have h := mul_le_mul_of_nonneg_left (show ‖x‖≤R by simpa using hx) ha.le
    simpa only [mul_comm a R] using h
  have hAff : Continuous (fun x : Position => y+a • x) :=
    continuous_const.add (continuous_id.const_smul a)
  have hm3 : MapsTo (fun x : Position => y+a • x) (Metric.ball 0 3)
      (Metric.ball y (3*a)) := fun x hx => hmap (R:=3) hx
  have hGc : ContinuousOn G (Metric.ball 0 3) :=
    (hF.comp hAff.continuousOn hm3).const_mul (a^4)
  have hGL : HasWeakLaplacian G (Metric.ball 0 2) (fun x => 4*Real.pi*τ x) := by
    have hh := HasWeakLaplacian.dilate ha (hLap.translate y)
    have hh' := hh.mono (show Metric.ball (0:Position) 2⊆(fun z => a • z) ⁻¹' {x | y+x∈Metric.ball y (2*a)} from
      fun x hx => hmap hx)
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    dsimp [G,τ]
    ring
  have hτ : Integrable τ := ((hi.comp_add_left y).comp_smul ha.ne').const_mul _
  have hτ0 (x) : 0≤τ x := mul_nonneg (pow_nonneg ha.le _) (hp _)
  have hτA (x) (hx : x∈Metric.closedBall (0:Position) 3) : τ x≤A := by
    have hh := mul_le_mul_of_nonneg_left (hb _ (hmapc hx)) (pow_nonneg ha.le 6)
    dsimp [τ]
    exact hh.trans_eq (by field_simp [ha.ne'])
  have hGM (x) (hx : x∈Metric.closedBall (0:Position) 2) : G x≤M := by
    have hh := mul_le_mul_of_nonneg_left (hcap _ (hmapc hx)) (pow_nonneg ha.le 4)
    dsimp [G]
    exact hh.trans_eq (by field_simp [ha.ne'])
  have hG0 : G 0=a^4*F y := by simp [G]
  have hGmean : volume.real (Metric.closedBall (0:Position) 2)*G 0 ≤
      (∫ x in Metric.closedBall 0 2, G x) := by
    rw [hG0]
    exact Coulomb.submean_affine y ha hmean
  let w := a⁻¹ • (z-y)
  have hw : w∈Metric.closedBall (0:Position) 1 := by
    have hdist : ‖z-y‖≤a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    simp only [Metric.mem_closedBall,dist_zero_right,w,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    exact (inv_mul_le_iff₀ ha).mpr (by simpa using hdist)
  have hGw : G w=a^4*F z := by
    simp only [G,w,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,add_sub_cancel]
  have hh := H G τ hGc hGL hτ hτ0 hτA hGM hGmean w hw
  rw [hGw,hG0,←mul_sub,norm_mul,Real.norm_eq_abs (a^4),abs_of_pos (pow_pos ha 4)] at hh
  have hm : max (-(a^4*F y)) 0=a^4*max (-F y) 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le 4)]
    simp only [mul_zero,mul_neg]
  rw [hm] at hh
  have hn : ‖w‖=a⁻¹*‖z-y‖ := by
    simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
  rw [hn] at hh
  have ht : a^4*(C*(‖z-y‖/a)*((a^4)⁻¹+max (-F y) 0)) =
      C*(1+a^4*max (-F y) 0)*(a⁻¹*‖z-y‖) := by
    field_simp [ha.ne']
  exact (mul_le_mul_iff_right₀ (pow_pos ha 4)).mp (hh.trans_eq ht.symm)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFOscillation
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology ContDiff
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ

omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_eq_density {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfPotential f=NeutralAtom.potentialOf (tfDensity Ω f) := by
  funext x
  apply integral_congr_ae
  filter_upwards [tfDensity_ae_tfExtend hΩ hf] with z hz
  change coulombKernel (x-z)*tfExtend Ω f z=coulombKernel (x-z)*tfDensity Ω f z
  rw [hz]

lemma tfPotential_ballCloud_integrable {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => tfPotential f z*ballCloud y a 1 z) := by
  rw [tfPotential_eq_density hΩ hf]
  exact potentialOf_ballCloud_integrable ((tfExtend_integrable hΩ f).congr
    (tfDensity_ae_tfExtend hΩ hf).symm) (tfDensity_measurable hΩ f) ha y

lemma tfPotential_ballCloud_le {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    {a : ℝ} (ha : 0 < a) (y : Space) :
    (∫ z, tfPotential f z*ballCloud y a 1 z)  ≤  tfPotential f y := by
  rw [tfPotential_eq_density hΩ hf]
  have hi := (tfExtend_integrable hΩ f).congr (tfDensity_ae_tfExtend hΩ hf).symm
  exact potentialOf_ballCloud_le hi (tfDensity_measurable hΩ f) (tfDensity_nonneg f) ha y
    (density_coulomb_integrable _ (tfDensity_nonneg f) (tfDensity_measurable hΩ f) hi
      (tfDensity_power_integrable hΩ hf) y)

lemma tfScreened_ballCloud_submean {Φ : Space → ℝ} {f : TFLp (volume.restrict Ω)}
    (hf : TFNonneg f) {a : ℝ} (ha : 0 < a) (y : Space)
    (hi : Integrable (fun z => Φ z*ballCloud y a 1 z))
    (he : (∫ z, Φ z*ballCloud y a 1 z)=Φ y) :
    Φ y-tfPotential f y  ≤  ∫ z, (Φ z-tfPotential f z)*ballCloud y a 1 z := by
  simp_rw [sub_mul]
  rw [integral_sub hi (tfPotential_ballCloud_integrable hΩ hf ha y),he]
  linarith [tfPotential_ballCloud_le hΩ hf ha y]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfEulerDensity_of_cap {c a v : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hv : v ≤ tfInteriorConstant c/a^4) :
    (max v 0/(c*(5/3:ℝ)))^(3/2:ℝ)  ≤
      (tfInteriorConstant c/(c*(5/3:ℝ)))^(3/2:ℝ)/a^6 := by
  have Hb : max v 0 ≤ tfInteriorConstant c/a^4 :=
    max_le hv (div_nonneg (tfInteriorConstant_nonneg c) (by positivity))
  have HH := Real.rpow_le_rpow (by positivity : 0 ≤ max v 0/(c*(5/3:ℝ)))
    (div_le_div_of_nonneg_right Hb (by positivity : 0 ≤ c*(5/3:ℝ))) (by norm_num : (0:ℝ) ≤ 3/2)
  apply HH.trans_eq
  rw [show tfInteriorConstant c/a^4/(c*(5/3:ℝ))=(tfInteriorConstant c/(c*(5/3:ℝ)))/a^4 by ring,
    Real.div_rpow (div_nonneg (tfInteriorConstant_nonneg c) (by positivity)) (by positivity),
    ←Real.rpow_natCast,←Real.rpow_mul ha.le]
  norm_num

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in

theorem tfScreened_interior_oscillation (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Set Space} (hΩ : MeasurableSet Ω)
      [IsFiniteMeasure (volume.restrict Ω)], ∀ {F : ℝ}, 0 ≤ F →
    ∀ (W : TFLq (volume.restrict Ω)), (∀ᵐ x ∂volume.restrict Ω, W x ≤ F) →
    ∀ (f : TFLp (volume.restrict Ω)), TFNonneg f →
    (∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) →
    ∀ (Φ : Space → ℝ), ContinuousOn Φ Ω → IsOpen Ω →
    W =ᵐ[volume.restrict Ω] Φ → NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0) →
    ∀ (y : Space) (a : ℝ), 0 < a → Metric.closedBall y (4*a)⊆Ω →
    Integrable (fun z => Φ z*ballCloud y (2*a) 1 z) →
    (∫ z, Φ z*ballCloud y (2*a) 1 z)=Φ y →
    ∀ z∈Metric.closedBall y a,
      ‖(Φ z-tfPotential f z)-(Φ y-tfPotential f y)‖  ≤
        C*(‖z-y‖/a)*((a^4)⁻¹+max (-(Φ y-tfPotential f y)) 0) := by
  let A := (tfInteriorConstant c/(c*(5/3:ℝ)))^(3/2:ℝ)
  obtain ⟨C,hC,H⟩ := NeutralAtom.poisson_scaled_negative_oscillation
    (show 0 ≤ A from Real.rpow_nonneg (div_nonneg (tfInteriorConstant_nonneg c) (by positivity)) _) (tfInteriorConstant_nonneg c)
  refine ⟨C,hC,?_⟩
  intro Ω hΩ inst F hF W hW f hf hm Φ hΦ ho he hh y a ha hball hi hmean z hz
  let V := fun x => Φ x-tfPotential f x
  let σ := (Metric.closedBall y (3*a)).indicator (fun x => (max (V x) 0/(c*(5/3:ℝ)))^(3/2:ℝ))
  have h3 : Metric.closedBall y (3*a)⊆Ω :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have h2 : Metric.ball y (2*a)⊆Ω :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).trans hball
  have hP := tfPotential_continuous_of_minimizes hΩ hc hF W hW hf hm
  have hVc : ContinuousOn V Ω := hΦ.sub hP.continuousOn
  have hσc : ContinuousOn (fun x => (max (V x) 0/(c*(5/3:ℝ)))^(3/2:ℝ)) (Metric.closedBall y (3*a)) := by
    exact (((hVc.mono h3).sup continuousOn_const).div_const _).rpow_const (fun _ _ => Or.inr (by norm_num))
  have hσi : Integrable σ := (hσc.integrableOn_compact (isCompact_closedBall _ _)).integrable_indicator measurableSet_closedBall
  have hσ0 (x) : 0 ≤ σ x := indicator_nonneg (fun x _ => Real.rpow_nonneg (by positivity) _) x
  have hσb (x) (hx : x∈Metric.closedBall y (3*a)) : σ x ≤ A/a^6 := by
    rw [show σ x=(max (V x) 0/(c*(5/3:ℝ)))^(3/2:ℝ) from indicator_of_mem hx _]
    exact tfEulerDensity_of_cap hc ha (tfScreened_three_quarters hΩ hc hF W hW hf hm hΦ ho he hh ha hball hx)
  have hVL : NeutralAtom.HasWeakLaplacian V (Metric.ball y (2*a)) (fun x => 4*Real.pi*σ x) := by
    intro φ hφ hφc ht
    have h := (tfScreened_weak_equation hΩ hc hF W hW hf hm hΦ ho he hh).mono h2
    rw [h φ hφ hφc ht]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball y (2*a)
    · have hx3 : x∈Metric.closedBall y (3*a) :=
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) hx
      dsimp only [σ]
      rw [indicator_of_mem hx3,Real.div_rpow (le_max_right _ _) (by positivity)]
      dsimp only [V]
      ring
    · have hp0 : φ x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (ht h))
      simp only [hp0,mul_zero]
  apply H V σ y a ha (hVc.mono (Metric.ball_subset_closedBall.trans h3)) hVL hσi hσ0 hσb
    (fun x hx => tfScreened_three_quarters hΩ hc hF W hW hf hm hΦ ho he hh ha hball
      (Metric.closedBall_subset_closedBall (by linarith) hx))
    (tfScreened_ballCloud_submean hΩ hf (by positivity) y hi hmean) z hz

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
namespace Coulomb

theorem exists_patch_TF_oscillation :
    ∃ C : ℝ, 0 < C ∧ ∀ {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (_ : 18*b ≤ a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space),
    SpatiallySupported u {z | t ≤ ‖z-y‖} →
    ∀ (hn : ∀ j, 20*a ≤ ‖S.position j-y‖) (z : Space), z∈Metric.closedBall y a →
      ‖patchTFScreenedField S u ha hb ht.2 y hn z-
        patchTFScreenedField S u ha hb ht.2 y hn y‖ ≤
      C*(‖z-y‖/a)*((a^4)⁻¹+max (-patchTFScreenedField S u ha hb ht.2 y hn y) 0) := by
  obtain ⟨C,hC,H⟩ := tfScreened_interior_oscillation thomasFermiKineticConstant thomasFermiKineticConstant_pos
  refine ⟨C,hC,?_⟩
  intro J k S u a b t ha hb hsmall ht y hu hn z hz
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  have hW : ∀ᵐ x ∂volume.restrict (Metric.ball y (t-4*b)), W x ≤ totalCharge S/a := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn),ae_restrict_mem measurableSet_ball] with x hx hy
    rw [hx]
    apply (sub_le_self _ (coreCoulombPotential_nonneg u x)).trans
    exact attraction_le_totalCharge_div S ha x (fun j => patch_nucleus_separation S ha hb ht.2 y hn j x hy)
  have hi : Integrable (fun z => coreScreenedField S u z*ballCloud y (2*a) 1 z) := by
    apply ((attraction_ballCloud_integrable S (by positivity : 0 < 2*a) y).sub
      (coreCoulombPotential_mul_integrable u _ (ballCloud_integrable (2*a) 1 y))).congr
    filter_upwards [] with z
    change attraction S z*ballCloud y (2*a) 1 z-coreCoulombPotential u z*ballCloud y (2*a) 1 z = _
    rw [coreScreenedField,sub_mul]
  have hm : (∫ z, coreScreenedField S u z*ballCloud y (2*a) 1 z)=coreScreenedField S u y := by
    simpa only [one_mul] using coreScreenedField_ballCloud S u hu (by positivity : 0 < 2*a) zero_le_one y
      (fun z hz => by change t ≤ ‖z-y‖ at hz; linarith [ht.1])
      (fun j => by linarith [hn j])
  exact H measurableSet_ball (div_nonneg (totalCharge_nonneg S) ha.le) W hW
    (localTFMinimizer measurableSet_ball W) (localTFMinimizer_nonneg measurableSet_ball W)
    (fun g hg => localTFMinimizer_minimizes measurableSet_ball W hg)
    (coreScreenedField S u) (patch_continuous_field S u ha hb ht.2 y hu hn) Metric.isOpen_ball
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (patch_harmonic_field S u ha hb ht.2 y hu hn) y a ha (patch_inner_ball ha hb hsmall ht.1 y) hi hm z hz

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchNegativeCost
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ in
lemma tf_negative_cost_integrable (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} {σ : Space → ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x=0) :
    Integrable (fun x => max (tfPotential f x-Φ x) 0*σ x) := by
  have : ENNReal.HolderConjugate TFFieldExponent TFExponent :=
    coulomb_holder_exponents.ennrealOfReal
  have H : IntegrableOn (fun x => (tfPotential f x-Φ x)*σ x) Ω :=
    ((tfPotential_memLp hΩ f).sub ((memLp_congr_ae hW).mp (Lp.memLp W))).integrable_mul hσ
  have Hi : Integrable (fun x => (tfPotential f x-Φ x)*σ x) := by
    apply (H.integrable_indicator hΩ).congr
    filter_upwards [] with x
    by_cases hx : x∈Ω
    · simp [hx]
    · simp [hx,hs x hx]
  apply Hi.pos_part.congr
  filter_upwards [hp] with x hx
  rw [max_mul_of_nonneg _ _ hx,zero_mul]

lemma rawTF_negativeError_le_gap (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x=0) :
    rawTFNegativeError Φ (localTFDensity hΩ W) σ ≤
      rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  have H := raw_localTF_refined_gap_density hΩ Φ W hW hσ (ae_restrict_of_ae hp) hs
  have hρ : MemLp (localTFDensity hΩ W) TFExponent volume :=
    tfDensity_memLp hΩ (localTFMinimizer_nonneg hΩ W)
  have hpQ := raw_coulomb_nonneg hΩ (hσ.sub (hρ.restrict (s := Ω)))
    (fun x hx => by change σ x-localTFDensity hΩ W x=0; rw [hs x hx,show localTFDensity hΩ W x=0 from tfDensity_eq_zero _ hx,sub_self])
  change 0 ≤ coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
    (fun x => σ x-localTFDensity hΩ W x) at hpQ
  linarith

lemma tf_negative_center_le_gap (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x=0)
    (χ : Space → ℝ) (y : Space) (θ B K m : ℝ)
    (hθ : 0 ≤ θ) (hθh : θ ≤ 1/2) (hB : 0 ≤ B) (hK : 0 ≤ K) (hm : 0 < m)
    (hχ : ∀ᵐ x, 0 ≤ χ x ∧ χ x ≤ K) (hi : Integrable (fun x => σ x*χ x))
    (hmass : m ≤ ∫ x, σ x*χ x)
    (hosc : ∀ᵐ x, χ x≠0 →
      ‖(Φ x-tfPotential (localTFMinimizer hΩ W) x)-
        (Φ y-tfPotential (localTFMinimizer hΩ W) y)‖ ≤
        θ*(B+max (-(Φ y-tfPotential (localTFMinimizer hΩ W) y)) 0)) :
    max (-(Φ y-tfPotential (localTFMinimizer hΩ W) y)) 0 ≤
      (2*K/m)*(rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W))+2*θ*B := by
  have hc := tf_negative_cost_integrable hΩ Φ W hW (f := localTFMinimizer hΩ W) hσ hp hs
  have he : (∫ x, max (-(Φ x-tfPotential (localTFMinimizer hΩ W) x)) 0*σ x)=
      rawTFNegativeError Φ (localTFDensity hΩ W) σ := by
    rw [tfPotential_eq_density hΩ (localTFMinimizer_nonneg hΩ W)]
    simp only [neg_sub,NeutralAtom.potentialOf,rawTFNegativeError,localTFDensity,NeutralAtom.coulombKernel,coulombKernel]
  have H := NeutralAtom.negative_center_of_test_mass
    (fun x => Φ x-tfPotential (localTFMinimizer hΩ W) x) σ χ
    (Φ y-tfPotential (localTFMinimizer hΩ W) y) θ B K m hθ hθh hB hK hm hp hχ hi
    (by simpa only [neg_sub] using hc) hmass hosc
  rw [he] at H
  have Hg := mul_le_mul_of_nonneg_left (rawTF_negativeError_le_gap hΩ Φ W hW hσ hp hs)
    (show 0 ≤ 2*K/m by positivity)
  linarith

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in

theorem exists_patch_negative_center_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {J k n : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t r : ℝ} (ha : 0 < a) (hb : 0 < b) (hsmall : 18*b ≤ a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space),
    SpatiallySupported u {z | t ≤ ‖z-y‖} →
    ∀ (hn : ∀ j, 20*a ≤ ‖S.position j-y‖), 0 ≤ r → r ≤ a → C*(r/a) ≤ 1/2 →
    ∀ (x : Configuration n) (χ : Space → ℝ) (K m : ℝ), 0 ≤ K → 0 < m →
    (∀ᵐ z, 0 ≤ χ z ∧ χ z ≤ K) →
    Integrable (fun z => retainedFineDensity b (patchRetained y t b x) (position x) z*χ z) →
    (∀ z, χ z≠0 → ‖z-y‖ ≤ r) →
    m ≤ ∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*χ z →
    max (-patchTFScreenedField S u ha hb ht.2 y hn y) 0 ≤
      (2*K/m)*(rawThomasFermiEnergy (coreScreenedField S u)
        (retainedFineDensity b (patchRetained y t b x) (position x))-
        rawThomasFermiEnergy (coreScreenedField S u)
          (localTFDensity measurableSet_ball (coreTFField S u measurableSet_ball ha
            (patch_nucleus_separation S ha hb ht.2 y hn))))+2*(C*(r/a))*((a^4)⁻¹) := by
  obtain ⟨C,hC,H⟩ := exists_patch_TF_oscillation
  refine ⟨C,hC,?_⟩
  intro J k n S u a b t r ha hb hsmall ht y hu hn hr hra hθ x χ K m hK hm hχ hi hs hmass
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  apply tf_negative_center_le_gap measurableSet_ball (coreScreenedField S u) W
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (retainedFineDensity_memLp hb _ _) (Eventually.of_forall (fun _ => retainedFineDensity_nonneg ..))
    (retainedFineDensity_patch_support hb y t x) χ y (C*(r/a)) ((a^4)⁻¹) K m
    (by positivity) hθ (by positivity) hK hm hχ hi hmass
  filter_upwards [] with z
  intro hz
  have hzr := hs z hz
  have hza : z∈Metric.closedBall y a := by simpa [Metric.mem_closedBall,dist_eq_norm] using hzr.trans hra
  have hosc := H S u ha hb hsmall ht y hu hn z hza
  apply hosc.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hzr ha.le) hC.le) (by positivity)

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma patchSliceTFGap_nonneg {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m) (x : Configuration m) :
    0≤patchSliceTFGap S u ha hb ht y hn s x := by
  have H := rawTF_negativeError_le_gap measurableSet_ball
    (coreScreenedField S (u.coreSlice s x).normalized) _
    (coreTFField_coe S _ measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn))
    (retainedFineDensity_memLp hb (patchRetained y t b x) (position x))
    (Eventually.of_forall (fun z => retainedFineDensity_nonneg b _ _ z))
    (retainedFineDensity_patch_support hb y t x)
  apply le_trans _ H
  exact integral_nonneg (fun z => mul_nonneg (le_max_right _ _)
    (retainedFineDensity_nonneg b _ _ z))

lemma patchSliceTFGap_weight_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    Integrable (fun x => mass (u.coreSlice s x)*patchSliceTFGap S u ha hb ht y hn s x) := by
  have hT := (coreTF_conditional_integrable measurableSet_ball S u s ha
    (patch_nucleus_separation S ha hb ht y hn) (show 0<12*a by positivity)
    (patch_diameter ha hb ht y) (fun _ => totalCharge S/a)
    (Eventually.of_forall (fun _ => div_nonneg (totalCharge_nonneg S) ha.le))
    ((mass_coreSlice_integrable u s).mul_const ((totalCharge S/a)^2))
    (show ∀ᵐ x, ∀ z∈Metric.ball y (t-4*b),
      coreScreenedField S (u.coreSlice s x).normalized z≤totalCharge S/a from ?_)).2
  · have hF : Integrable (fun x => mass (u.coreSlice s x)*
        rawThomasFermiEnergy (coreScreenedField S (u.coreSlice s x).normalized)
          (retainedFineDensity b (patchRetained y t b x) (position x))) := by
      apply (discreteFineTF_weight_integrable S u hb (patchRetained y t b)
        (patchRetained_measurable y t b) s).congr
      filter_upwards [hcs] with x hx
      rw [discreteFineTF_eq_raw S u hb (patchRetained y t b) s x hx ?_
        (patch_retained_separated ha hb y x)]
      intro j i hi
      have hret := (patchRetained_mem ..).mp hi
      have H := norm_sub_le_norm_sub_add_norm_sub (S.position j) (position x i) y
      have hs : Real.sqrt 3≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
      nlinarith [hn j]
    apply (hF.sub hT).congr
    filter_upwards [] with x
    simp only [patchSliceTFGap,Pi.sub_apply,mul_sub]
  · filter_upwards [] with x
    intro z hz
    apply (sub_le_self _ (coreCoulombPotential_nonneg _ z)).trans
    exact attraction_le_totalCharge_div S ha z
      (fun j => patch_nucleus_separation S ha hb ht y hn j z hz)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoulombTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma ballCloud_norm_bound {a : ℝ} (ha : 0<a) (y z : Space) :
    ‖ballCloud y a 1 z‖≤1/(4*Real.pi/3*a^3) := by
  change ‖uniformBall a 1 (z-y)‖≤_
  rw [Real.norm_of_nonneg (uniformBall_nonneg ha zero_le_one _)]
  exact uniformBall_le ha zero_le_one _

lemma density_ballCloud_test_integrable {ρ : Space → ℝ} (hi : Integrable ρ)
    (hm : Measurable ρ) {a : ℝ} (ha : 0<a) (y : Space) :
    Integrable (fun x => ρ x*(∫ z, coulombKernel (x-z)*ballCloud y a 1 z)) := by
  have H := (coulomb_pair_integrable hi hm (ballCloud_integrable a 1 y)
    (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y)).integral_prod_left
  apply H.congr
  filter_upwards [] with x
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

lemma potential_ballCloud_remainder {ρ : Space → ℝ} (hi : Integrable ρ)
    (hm : Measurable ρ) (hp : ∀ x, 0≤ρ x) {a : ℝ} (ha : 0<a) (y : Space)
    (hK : Integrable (fun x => coulombKernel (y-x)*ρ x)) :
    0≤NeutralAtom.potentialOf ρ y-coulombBilinear ρ (ballCloud y a 1) ∧
    NeutralAtom.potentialOf ρ y-coulombBilinear ρ (ballCloud y a 1)≤
      ∫ x in Metric.ball y a, ρ x*coulombKernel (y-x) := by
  have ht := density_ballCloud_test_integrable hi hm ha y
  let f := fun x => coulombKernel (y-x)*ρ x-
    ρ x*(∫ z, coulombKernel (x-z)*ballCloud y a 1 z)
  have he : NeutralAtom.potentialOf ρ y-coulombBilinear ρ (ballCloud y a 1)=∫ x, f x := by
    rw [coulombBilinear_iterated hi hm (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y)]
    exact (integral_sub hK ht).symm
  have hbound : ∀ᵐ x, 0≤f x ∧ f x≤(Metric.ball y a).indicator
      (fun x => ρ x*coulombKernel (y-x)) x := by
    filter_upwards [volume.ae_ne y] with x hxy
    have hlu := ballCloud_coulomb_le ha zero_le_one y x hxy
    have hl : 0≤∫ z, coulombKernel (x-z)*ballCloud y a 1 z :=
      integral_nonneg (fun z => mul_nonneg (coulombKernel_nonneg _) (uniformBall_nonneg ha zero_le_one _))
    have hpos : 0≤f x := by
      dsimp only [f]
      simp only [one_mul,coulombKernel_sub_comm x y] at hlu
      nlinarith [mul_le_mul_of_nonneg_left hlu (hp x)]
    refine ⟨hpos,?_⟩
    by_cases hx : x∈Metric.ball y a
    · rw [indicator_of_mem hx]
      dsimp only [f]
      nlinarith [mul_nonneg (hp x) hl]
    · rw [indicator_of_notMem hx]
      have hx' : a≤‖x-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hx
      dsimp only [f]
      rw [ballCloud_coulomb ha zero_le_one y x hx',one_mul,coulombKernel_sub_comm x y]
      nlinarith
  rw [he]
  refine ⟨integral_nonneg_of_ae (hbound.mono (fun _ h => h.1)),?_⟩
  rw [←integral_indicator measurableSet_ball]
  apply integral_mono_ae (hK.sub ht)
  · exact (hK.congr (Eventually.of_forall (fun x => mul_comm _ _))).indicator measurableSet_ball
  · exact hbound.mono (fun _ h => h.2)

lemma coulombBilinear_sub_ballCloud {ρ σ : Space → ℝ}
    (hρ : Integrable ρ) (hρm : Measurable ρ) (hσ : Integrable σ) (hσm : Measurable σ)
    {a : ℝ} (ha : 0<a) (y : Space) :
    coulombBilinear (fun z => ρ z-σ z) (ballCloud y a 1)=
      coulombBilinear ρ (ballCloud y a 1)-coulombBilinear σ (ballCloud y a 1) := by
  change coulombBilinear (ρ-σ) (ballCloud y a 1)=_
  rw [coulombBilinear_iterated (hρ.sub hσ) (hρm.sub hσm)
    (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y),
    coulombBilinear_iterated hρ hρm (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y),
    coulombBilinear_iterated hσ hσm (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y)]
  simp only [Pi.sub_apply, sub_mul]
  exact integral_sub (density_ballCloud_test_integrable hρ hρm ha y)
    (density_ballCloud_test_integrable hσ hσm ha y)

theorem potential_difference_coulomb_transfer {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {ρ σ : Space → ℝ}
    (hρ : MemLp ρ TFExponent (volume.restrict Ω))
    (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hρm : Measurable ρ) (hσm : Measurable σ)
    (hρp : ∀ z, 0≤ρ z) (hσp : ∀ z, 0≤σ z)
    (hρs : ∀ z∉Ω, ρ z=0) (hσs : ∀ z∉Ω, σ z=0)
    {a : ℝ} (ha : 0<a) (y : Space) (hball : Metric.ball y a⊆Ω) :
    |NeutralAtom.potentialOf ρ y-NeutralAtom.potentialOf σ y|≤
      Real.sqrt ((5/(2*a))*coulombBilinear (fun z => ρ z-σ z) (fun z => ρ z-σ z))+
      (∫ z in Metric.ball y a, ρ z*coulombKernel (y-z))+
      (∫ z in Metric.ball y a, σ z*coulombKernel (y-z)) := by
  have hρe := tfExtend_toLp hΩ hρ hρs
  have hσe := tfExtend_toLp hΩ hσ hσs
  have hρi : Integrable ρ := (tfExtend_integrable hΩ (hρ.toLp ρ)).congr hρe
  have hσi : Integrable σ := (tfExtend_integrable hΩ (hσ.toLp σ)).congr hσe
  have hρl : MemLp ρ TFExponent volume := (memLp_congr_ae hρe).mp (tfExtend_memLp hΩ _)
  have hσl : MemLp σ TFExponent volume := (memLp_congr_ae hσe).mp (tfExtend_memLp hΩ _)
  have hρpow := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hρl
    (Eventually.of_forall hρp)
  have hσpow := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hσl
    (Eventually.of_forall hσp)
  have Hρ := potential_ballCloud_remainder hρi hρm hρp ha y
    (density_coulomb_integrable _ hρp hρm hρi hρpow y)
  have Hσ := potential_ballCloud_remainder hσi hσm hσp ha y
    (density_coulomb_integrable _ hσp hσm hσi hσpow y)
  have hs : ∀ z∉Ω, ρ z-σ z=0 := fun z hz => by rw [hρs z hz,hσs z hz,sub_self]
  have H := raw_coulomb_ballCloud_duality hΩ (hρ.sub hσ) hs y ha hball
  have hq : 0≤(5/(2*a))*coulombBilinear (fun z => ρ z-σ z) (fun z => ρ z-σ z) :=
    mul_nonneg (by positivity) (raw_coulomb_nonneg hΩ (hρ.sub hσ) hs)
  have HT : |coulombBilinear (fun z => ρ z-σ z) (ballCloud y a 1)|≤Real.sqrt
      ((5/(2*a))*coulombBilinear (fun z => ρ z-σ z) (fun z => ρ z-σ z)) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt hq]
    exact H
  rw [coulombBilinear_sub_ballCloud hρi hρm hσi hσm ha y] at HT
  have HH := abs_le.mp HT
  apply abs_le.mpr
  constructor <;> linarith [Hρ.1,Hρ.2,Hσ.1,Hσ.2]

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma translated_coulomb_ball_integral (y : Space) {r : ℝ} (hr : 0 ≤ r) :
    (∫ z in Metric.ball y r, coulombKernel (y-z))=2*Real.pi*r^2 := by
  have he : (Metric.ball y r).indicator (fun z => coulombKernel (y-z))=
      fun z => (Metric.ball (0:Space) r).indicator coulombKernel (y-z) := by
    funext z
    have hh : y-z∈Metric.ball (0:Space) r ↔ z∈Metric.ball y r := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hz : z∈Metric.ball y r <;> simp [hh,hz]
  rw [←integral_indicator measurableSet_ball,he,integral_sub_left_eq_self,
    integral_indicator measurableSet_ball,coulombKernel_ball_integral hr]

lemma translated_coulomb_integrableOn_ball (y : Space) (r : ℝ) :
    IntegrableOn (fun z => coulombKernel (y-z)) (Metric.ball y r) := by
  rw [←integrable_indicator_iff measurableSet_ball]
  have he : (Metric.ball y r).indicator (fun z => coulombKernel (y-z))=
      fun z => (Metric.ball (0:Space) r).indicator coulombKernel (y-z) := by
    funext z
    have hh : y-z∈Metric.ball (0:Space) r ↔ z∈Metric.ball y r := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hz : z∈Metric.ball y r <;> simp [hh,hz]
  rw [he]
  exact (integrable_comp_sub_left _ y).mpr
    ((coulombKernel_integrableOn_ball r).integrable_indicator measurableSet_ball)

lemma near_coulomb_of_density_cap {ρ : Space → ℝ} (y : Space) {r B : ℝ} (hr : 0 ≤ r)
    (hi : IntegrableOn (fun z => ρ z*coulombKernel (y-z)) (Metric.ball y r))
    (hc : ∀ᵐ z ∂volume.restrict (Metric.ball y r), ρ z≤B) :
    (∫ z in Metric.ball y r, ρ z*coulombKernel (y-z))≤B*(2*Real.pi*r^2) := by
  calc
    _≤∫ z in Metric.ball y r, B*coulombKernel (y-z) := by
      apply integral_mono_ae hi ((translated_coulomb_integrableOn_ball y r).const_mul B)
      exact hc.mono (fun z hz => mul_le_mul_of_nonneg_right hz (coulombKernel_nonneg _))
    _=_ := by rw [integral_const_mul,translated_coulomb_ball_integral y hr]

theorem patch_tf_density_cap {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖})
    (hn : ∀ j, 20*a≤‖S.position j-y‖) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall y (3*a)),
      localTFDensity measurableSet_ball (coreTFField S u measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht.2 y hn)) z≤
        (tfInteriorConstant thomasFermiKineticConstant/
          (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6 := by
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  have hW : ∀ᵐ z ∂volume.restrict (Metric.ball y (t-4*b)), W z≤totalCharge S/a := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn),ae_restrict_mem measurableSet_ball] with z hz hmem
    rw [hz]
    exact (sub_le_self _ (coreCoulombPotential_nonneg u z)).trans
      (attraction_le_totalCharge_div S ha z
        (fun j => patch_nucleus_separation S ha hb ht.2 y hn j z hmem))
  exact tfDensity_interior_bound measurableSet_ball thomasFermiKineticConstant_pos
    (div_nonneg (totalCharge_nonneg S) ha.le) W hW
    (localTFMinimizer_nonneg measurableSet_ball W)
    (fun g hg => localTFMinimizer_minimizes measurableSet_ball W hg)
    (patch_continuous_field S u ha hb ht.2 y hu hn) Metric.isOpen_ball
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (patch_harmonic_field S u ha hb ht.2 y hu hn) ha (patch_inner_ball ha hb hsmall ht.1 y)

theorem patch_potential_transfer {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a)
    (spin : Spins m) (x : Configuration m)
    (hcs : SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖}) :
    let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn)
    let σ := retainedFineDensity b (patchRetained y t b x) (position x)
    |NeutralAtom.potentialOf σ y-tfPotential (localTFMinimizer measurableSet_ball W) y|≤
      Real.sqrt ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn spin x)+
      (∫ z in Metric.ball y r, σ z*coulombKernel (y-z))+
      ((tfInteriorConstant thomasFermiKineticConstant/
          (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  intro W σ
  let Ω := Metric.ball y (t-4*b)
  let ρ := localTFDensity measurableSet_ball W
  have hσ : MemLp σ TFExponent (volume.restrict Ω) := retainedFineDensity_memLp hb _ _
  have hρ : MemLp ρ TFExponent volume := tfDensity_memLp measurableSet_ball
    (localTFMinimizer_nonneg measurableSet_ball W)
  have hσs : ∀ z∉Ω, σ z=0 := retainedFineDensity_patch_support hb y t x
  have hρs : ∀ z∉Ω, ρ z=0 := fun z hz => tfDensity_eq_zero _ hz
  have hball : Metric.ball y r⊆Ω := by
    apply Metric.ball_subset_ball
    linarith [ht.1]
  have H := potential_difference_coulomb_transfer measurableSet_ball hσ (hρ.restrict (s := Ω))
    (retainedFineDensity_measurable b _ _) (tfDensity_measurable measurableSet_ball _)
    (retainedFineDensity_nonneg b _ _) (tfDensity_nonneg _) hσs hρs hr y hball
  have HG := rawTF_gap_coulomb measurableSet_ball
    (coreScreenedField S (u.coreSlice spin x).normalized) W
    (coreTFField_coe S _ measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)) hσ
    (Eventually.of_forall (retainedFineDensity_nonneg b _ _)) hσs
  have Hsq : Real.sqrt ((5/(2*r))*coulombBilinear (fun z => σ z-ρ z) (fun z => σ z-ρ z))≤
      Real.sqrt ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn spin x) := by
    apply Real.sqrt_le_sqrt
    have HH := mul_le_mul_of_nonneg_left HG (show 0≤5/(2*r) by positivity)
    convert HH using 1 <;> (try dsimp only [patchSliceTFGap,σ,ρ,W]) <;> first | rfl | ring
  have hiρ : Integrable ρ := (tfExtend_integrable measurableSet_ball
    (localTFMinimizer measurableSet_ball W)).congr
      (tfDensity_ae_tfExtend measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)).symm
  have hnear := near_coulomb_of_density_cap y hr.le
    (((density_coulomb_integrable ρ (tfDensity_nonneg _) (tfDensity_measurable measurableSet_ball _)
      hiρ (tfDensity_power_integrable measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)) y).congr
        (Eventually.of_forall (fun z => mul_comm _ _))).integrableOn (s := Metric.ball y r))
    (ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith : r≤3*a)))
      (patch_tf_density_cap S (u.coreSlice spin x).normalized ha hb hsmall ht y hcs hn))
  rw [tfPotential_eq_density measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)]
  exact H.trans (add_le_add (add_le_add Hsq le_rfl) hnear)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_UniformGroundStateCountControl
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem packetWidth_pos {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (z : Position) : 0 < packetWidth c₁ r₀ s z := by
  unfold packetWidth
  have hmax : 0 < max ‖z‖ r₀ := lt_of_lt_of_le hr (le_max_right _ _)
  exact mul_pos (mul_pos hc hmax) (Real.rpow_pos_of_pos (lt_min hmax hs) _)

theorem packetKernel_eq_wavepacket_sq (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    packetKernel g c₁ r₀ s z y =
      ((packetWidth c₁ r₀ s z) ^ (-(3 / 2 : ℝ)) *
        g ((packetWidth c₁ r₀ s z)⁻¹ • (y-z))) ^ 2 := by
  have ht := (packetWidth_pos hc hr hs z).le
  rw [mul_pow]
  unfold packetKernel
  congr 1
  rw [← Real.rpow_natCast (_ ^ (-(3 / 2 : ℝ))) 2, ← Real.rpow_mul ht]
  norm_num

theorem packetKernel_nonneg (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    0 ≤ packetKernel g c₁ r₀ s z y := by
  rw [packetKernel_eq_wavepacket_sq g hc hr hs]
  positivity

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb

lemma nearWeight_nonneg (y : Space) (R : ℝ) (z : Space) : 0≤nearWeight y R z := by
  unfold nearWeight
  exact Set.indicator_nonneg (fun z _ => coulombKernel_nonneg _) z
end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb
lemma nearWeight_site_integrable {n : ℕ} (u : H1Vector n) (y : Space) (R : ℝ)
    (s : Spins n) (i : Fin n) :
    Integrable (fun x => nearWeight y R (position x i)*‖u.value s x‖^2) := by
  have H := (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1
  have hc : Integrable (fun x => coulombKernel (y-position x i)*‖u.value s x‖^2) := by
    simpa only [coulombKernel,norm_sub_rev] using H
  have hh := hc.indicator ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage
    (continuous_position i).measurable)
  apply hh.congr
  filter_upwards [] with x
  by_cases hx : position x i∈Metric.ball y R <;> simp [nearWeight,hx]

lemma nearPotential_outer_integrable {m k : ℕ} (u : H1Vector (m+k)) (y : Space) (R : ℝ)
    (s : Spins (m+k)) :
    Integrable (fun x => nearPotential y R ((joinConfiguration m k).symm x).1*‖u.value s x‖^2) := by
  simp only [nearPotential,position_split_left,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ => nearWeight_site_integrable u y R s (Fin.castAdd k i))

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_FineNear
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma fineKernel_near_coulomb_le {b : ℝ} (hb : 0<b) (y w : Space)
    (hw : w≠y) (r : ℝ) :
    (∫ z in Metric.ball y r,coulombKernel (y-z)*fineKernel b (z-w))≤nearWeight y (r+2*b) w := by
  by_cases hn : w∈Metric.ball y (r+2*b)
  · rw [nearWeight,indicator_of_mem hn]
    calc
      _≤∫ z,coulombKernel (y-z)*fineKernel b (z-w) :=
        setIntegral_le_integral (fineKernel_shift_coulomb_integrable hb y w)
          (Eventually.of_forall (fun z => mul_nonneg (coulombKernel_nonneg _) (fineKernel_nonneg ..)))
      _≤_ := by
        rw [fineKernel_shift_coulomb_integral]
        exact fineKernel_coulomb_le hb (sub_ne_zero.mpr hw.symm)
  · rw [nearWeight,indicator_of_notMem hn]
    have hdist : r+2*b≤‖w-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hn
    have he : (∫ z in Metric.ball y r,coulombKernel (y-z)*fineKernel b (z-w))=0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      exact Eventually.of_forall (fun z hz => by
      have hz' : ‖z-y‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
      have htri := norm_sub_le_norm_sub_add_norm_sub w z y
      rw [norm_sub_rev w z] at htri
      rw [fineKernel_eq_zero_of_two_mul_lt hb _ (by linarith),mul_zero])
    exact he.le

theorem retainedFine_near_le {n : ℕ} {b : ℝ} (hb : 0<b) (y : Space) (r : ℝ)
    (I : Finset (Fin n)) (x : Configuration n) (hxy : ∀ i,position x i≠y) :
    (∫ z in Metric.ball y r,coulombKernel (y-z)*retainedFineDensity b I (position x) z)≤
      nearPotential y (r+2*b) x := by
  simp only [retainedFineDensity,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => (fineKernel_shift_coulomb_integrable hb y (position x i)).integrableOn)]
  exact (Finset.sum_le_sum (fun i _ => fineKernel_near_coulomb_le hb y (position x i) (hxy i) r)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => nearWeight_nonneg y _ _))

lemma fineKernel_raw_deficit {b : ℝ} (hb : 0<b) (y w : Space) (hw : w≠y) :
    0 ≤ coulombKernel (y-w)-(∫ z,coulombKernel (y-z)*fineKernel b (z-w)) ∧
    coulombKernel (y-w)-(∫ z,coulombKernel (y-z)*fineKernel b (z-w))≤nearWeight y (2*b) w := by
  have hnewton : (∫ z,coulombKernel (y-z)*fineKernel b (z-w)) ≤ coulombKernel (y-w) := by
    rw [fineKernel_shift_coulomb_integral]
    exact fineKernel_coulomb_le hb (sub_ne_zero.mpr hw.symm)
  refine ⟨sub_nonneg.mpr hnewton,?_⟩
  by_cases hn : w∈Metric.ball y (2*b)
  · rw [nearWeight,indicator_of_mem hn]
    exact sub_le_self _ (integral_nonneg (fun z => mul_nonneg (coulombKernel_nonneg _) (fineKernel_nonneg ..)))
  · rw [nearWeight,indicator_of_notMem hn]
    have hsep : Real.sqrt 3*b≤‖y-w‖ := by
      have hd : 2*b≤‖w-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hn
      have hs : Real.sqrt 3≤2 := by apply (Real.sqrt_le_iff).mpr; norm_num
      rw [norm_sub_rev]
      exact (mul_le_mul_of_nonneg_right hs hb.le).trans hd
    rw [fineKernel_shift_coulomb_eq hb y w hsep,sub_self]

theorem patchFine_raw_deficit {n : ℕ} {b t a : ℝ} (hb : 0<b) (ha : 0<a)
    (hat : a≤t-7*b) (y : Space) (x : Configuration n) (hxy : ∀ i,position x i≠y) :
    0≤nuclearPotential (unitNucleus y) x-
      NeutralAtom.potentialOf (retainedFineDensity b (patchRetained y t b x) (position x)) y ∧
    nuclearPotential (unitNucleus y) x-
      NeutralAtom.potentialOf (retainedFineDensity b (patchRetained y t b x) (position x)) y≤
      nearPotential y (2*b) x+((deletedLabels (patchRetained y t b) x).card:ℝ)/a := by
  let I := patchRetained y t b x
  let D := deletedLabels (patchRetained y t b) x
  have hpot : NeutralAtom.potentialOf (retainedFineDensity b I (position x)) y=
      ∑ i∈I,∫ z,coulombKernel (y-z)*fineKernel b (z-position x i) := by
    unfold NeutralAtom.potentialOf
    simp only [retainedFineDensity,Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => fineKernel_shift_coulomb_integrable hb y _)
  have hraw : nuclearPotential (unitNucleus y) x=∑ i,coulombKernel (y-position x i) := by
    simp [nuclearPotential,attraction,unitNucleus,coulombKernel,norm_sub_rev]
  have hdel : (∑ i∈D,coulombKernel (y-position x i))≤(D.card:ℝ)/a := by
    calc
      _≤∑ _i∈D,a⁻¹ := by
        apply Finset.sum_le_sum
        intro i hi
        have hni : i∉I := by simpa only [D,deletedLabels,Finset.mem_sdiff,Finset.mem_univ,true_and] using hi
        have hn : t-7*b≤‖position x i-y‖ := by simpa only [I,patchRetained_mem,not_lt] using hni
        unfold coulombKernel
        rw [norm_sub_rev]
        exact inv_anti₀ ha (hat.trans hn)
      _=_ := by simp [div_eq_mul_inv]
  have he : nuclearPotential (unitNucleus y) x-NeutralAtom.potentialOf (retainedFineDensity b I (position x)) y=
      (∑ i∈I,(coulombKernel (y-position x i)-(∫ z,coulombKernel (y-z)*fineKernel b (z-position x i))))+
        ∑ i∈D,coulombKernel (y-position x i) := by
    rw [hraw,hpot,←retained_deleted_sum (patchRetained y t b) x (fun i => coulombKernel (y-position x i)),Finset.sum_sub_distrib]
    ring
  change 0≤nuclearPotential (unitNucleus y) x-NeutralAtom.potentialOf (retainedFineDensity b I (position x)) y ∧ _
  rw [he]
  constructor
  · exact add_nonneg (Finset.sum_nonneg (fun i _ => (fineKernel_raw_deficit hb y _ (hxy i)).1))
      (Finset.sum_nonneg (fun i _ => coulombKernel_nonneg _))
  · have hh := (Finset.sum_le_sum (fun i (_ : i∈I) => (fineKernel_raw_deficit hb y _ (hxy i)).2)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => nearWeight_nonneg y (2*b) _))
    exact add_le_add hh hdel
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PatchRawTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma sqrt_young (x : ℝ) (hx : 0≤x) {ε : ℝ} (hε : 0<ε) :
    Real.sqrt x≤ε+x/(4*ε) := by
  have h := sq_nonneg (Real.sqrt x-2*ε)
  rw [sub_sq,Real.sq_sqrt hx] at h
  have he : x/(4*ε)*(4*ε)=x := div_mul_cancel₀ _ (by positivity)
  apply (mul_le_mul_iff_of_pos_right (show 0<4*ε by positivity)).mp
  nlinarith

theorem patch_raw_field_transfer {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a)
    (spin : Spins m) (x : Configuration m)
    (hcs : SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖})
    (hxy : ∀ i,position x i≠y) :
    |(coreScreenedField S (u.coreSlice spin x).normalized y-nuclearPotential (unitNucleus y) x)-
      patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y|≤
      Real.sqrt ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn spin x)+
      nearPotential y (r+2*b) x+nearPotential y (2*b) x+
      ((deletedLabels (patchRetained y t b) x).card:ℝ)/a+
      ((tfInteriorConstant thomasFermiKineticConstant/
        (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  let σ := retainedFineDensity b (patchRetained y t b x) (position x)
  let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
    (patch_nucleus_separation S ha hb ht.2 y hn)
  have hf := patch_potential_transfer S u ha hb hsmall ht y hn hr hra spin x hcs
  have hn' := retainedFine_near_le hb y r (patchRetained y t b x) x hxy
  have hdiff := patchFine_raw_deficit (t := t) hb ha (by linarith [ht.1]) y x hxy
  have ht' := abs_sub_le (nuclearPotential (unitNucleus y) x) (NeutralAtom.potentialOf σ y)
    (tfPotential (localTFMinimizer measurableSet_ball W) y)
  rw [abs_of_nonneg hdiff.1] at ht'
  have he : |(coreScreenedField S (u.coreSlice spin x).normalized y-nuclearPotential (unitNucleus y) x)-
      patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y|=
      |nuclearPotential (unitNucleus y) x-tfPotential (localTFMinimizer measurableSet_ball W) y| := by
    unfold patchTFScreenedField
    rw [show (coreScreenedField S (u.coreSlice spin x).normalized y-nuclearPotential (unitNucleus y) x)-
        (coreScreenedField S (u.coreSlice spin x).normalized y-tfPotential
        (localTFMinimizer measurableSet_ball W) y)=
        -(nuclearPotential (unitNucleus y) x-tfPotential (localTFMinimizer measurableSet_ball W) y) by ring,
      abs_neg]
  rw [he]
  have heint : (∫ z in Metric.ball y r,σ z*coulombKernel (y-z))=
      (∫ z in Metric.ball y r,coulombKernel (y-z)*σ z) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => mul_comm _ _)
  dsimp only [σ,W] at ht' heint
  dsimp only at hf
  rw [heint] at hf
  linarith
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFPotentialParameter
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω)
include hΩ

variable [IsFiniteMeasure (volume.restrict Ω)]

lemma continuous_tfPotential_evaluation (y : Space) :
    Continuous (fun f : TFLp (volume.restrict Ω) => tfPotential f y) :=
  (tfPotentialEvaluation hΩ y).continuous

lemma aestronglyMeasurable_localTFPotential {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (W : A → TFLq (volume.restrict Ω)) (hW : AEStronglyMeasurable W μ) (y : Space) :
    AEStronglyMeasurable (fun x => tfPotential (localTFMinimizer hΩ (W x)) y) μ :=
  (continuous_tfPotential_evaluation hΩ y).comp_aestronglyMeasurable
    ((continuous_localTFMinimizer hΩ).comp_aestronglyMeasurable hW)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CorePointMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma potentialForm_coreSlice_point_aestronglyMeasurable {m k : ℕ}
    (u : H1Vector (m+k)) (s : Spins m)
    (W : Configuration m × Configuration k → ℝ) (hW : Measurable W) :
    AEStronglyMeasurable (fun x => potentialForm (fun v => W (x,v)) (u.coreSlice s x)) volume := by
  apply AEStronglyMeasurable.congr _
    (show (fun x => ∑ t : Spins k, ∫ v, W (x,v)*
      ‖u.value (Fin.append s t) (joinConfiguration m k (x,v))‖^2) =ᵐ[volume]
      (fun x => potentialForm (fun v => W (x,v)) (u.coreSlice s x)) from ?_)
  · apply Finset.aestronglyMeasurable_fun_sum
    intro t ht
    have hψ := ((u.value_L2 (Fin.append s t)).aestronglyMeasurable.comp_measurePreserving
      (joinConfiguration_measurePreserving m k)).norm.pow 2
    exact (hW.aestronglyMeasurable.mul hψ).integral_prod_right'
  · filter_upwards [u.coreSliceRegular_ae s] with x hx
    simp only [potentialForm,u.coreSlice_value s hx]

lemma coreScreenedField_slice_point_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) (y : Space) :
    AEStronglyMeasurable (fun x => coreScreenedField S (u.coreSlice s x).normalized y) volume := by
  have hw : Measurable (fun z : Configuration m × Configuration k => restrictedOutPotential z.2 Set.univ y) := by
    apply Finset.measurable_fun_sum
    intro i hi
    simp only [Set.mem_univ,ite_true,coulombKernel]
    exact (((continuous_position i).measurable.comp measurable_snd).sub measurable_const).norm.inv
  have H := potentialForm_coreSlice_point_aestronglyMeasurable u s _ hw
  have H' : AEStronglyMeasurable (fun x : Configuration m =>
      (mass (u.coreSlice s x))⁻¹*potentialForm (fun v => restrictedOutPotential v Set.univ y)
        (u.coreSlice s x)) volume :=
    (mass_coreSlice_integrable u s).aestronglyMeasurable.inv₀.mul H
  have H'' : AEStronglyMeasurable (fun x => coreCoulombPotential (u.coreSlice s x).normalized y) volume := by
    apply H'.congr
    filter_upwards [] with x
    symm
    rw [←potentialForm_normalized_eq,potentialForm_restrictedOutPotential _ MeasurableSet.univ]
    simp only [restrictedCorePotential,Set.mem_univ,ite_true,coreCoulombPotential]
  exact aestronglyMeasurable_const.sub H''

lemma patchTFScreenedField_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) {a b t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t≤6*a) (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖) (z : Space) :
    AEStronglyMeasurable (fun x => patchTFScreenedField S (u.coreSlice s x).normalized ha hb ht y hn z) volume := by
  exact (coreScreenedField_slice_point_aestronglyMeasurable S u s z).sub
    (aestronglyMeasurable_localTFPotential measurableSet_ball _
      (coreTFField_slice_aestronglyMeasurable S u s measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht y hn)) z)

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma ae_position_ne (n : ℕ) (y : Space) : ∀ᵐ x : Configuration n,∀ i,position x i≠y := by
  rw [ae_all_iff]
  intro i
  let L : Configuration n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x (i,0)
      map_add' := by intro x z; rfl
      map_smul' := by intro c x; rfl }
  have hL : LinearMap.ker L≠⊤ := by
    intro h
    have hh : EuclideanSpace.single (i,0) (1:ℝ)∈LinearMap.ker L := by rw [h]; trivial
    change (EuclideanSpace.single (i,0) (1:ℝ)) (i,0)=0 at hh
    simp at hh
  let v : Configuration n := EuclideanSpace.single (i,0) (y 0)
  have hv : v (i,0)=y 0 := by simp [v]
  have hz := Measure.addHaar_submodule (volume : Measure (Configuration n)) (LinearMap.ker L) hL
  have hnull : (volume : Measure (Configuration n)) {x | position x i=y}=0 := by
    apply measure_mono_null (t := (fun x : Configuration n => x+(-v)) ⁻¹' (LinearMap.ker L : Set (Configuration n)))
    · intro x hx
      change (x+(-v)) (i,0)=0
      simp only [PiLp.add_apply,PiLp.neg_apply,hv]
      have hs := congrArg (fun z : Space => z 0) hx
      change x (i,0)=y 0 at hs
      rw [hs,add_neg_cancel]
    · rw [measure_preimage_add_right,hz]
  rw [ae_iff]
  simpa only [not_not] using hnull

lemma patchFieldTransferError_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (s : Spins m) :
    AEStronglyMeasurable (patchFieldTransferError S u ha hb ht y hn s) volume := by
  have hnuc : Measurable (nuclearPotential (n := m) (unitNucleus y)) :=
    Finset.measurable_sum _ (fun i _ => (attraction_measurable _).comp (continuous_position i).measurable)
  exact ((coreScreenedField_slice_point_aestronglyMeasurable S u s y).sub hnuc.aestronglyMeasurable).sub
    (patchTFScreenedField_slice_aestronglyMeasurable S u s ha hb ht y hn y)

lemma patchTransferRemainder_weight_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (r ε : ℝ) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    Integrable (fun x => mass (u.coreSlice s x)*patchTransferRemainder S u ha hb ht y hn r ε s x) := by
  have hgap := (patchSliceTFGap_weight_integrable S u ha hb ht y hn s hcs).const_mul (5/(4*r*ε))
  have hnear (R : ℝ) := slice_weight_integrable_const u (nearPotential y R)
    (nearPotential_outer_integrable u y R) s
  have hcount := (sliceCount_weight_integrable u (A := {z | t-7*b≤‖z-y‖})
    (isClosed_le continuous_const (by fun_prop : Continuous (fun z : Space => ‖z-y‖))).measurableSet s 1).div_const a
  simp only [pow_one] at hcount
  have hε := (mass_coreSlice_integrable u s).mul_const ε
  have hC := (mass_coreSlice_integrable u s).mul_const
    (((tfInteriorConstant thomasFermiKineticConstant/
      (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2))
  apply (((((hε.add hgap).add (hnear (r+2*b))).add (hnear (2*b))).add hcount).add hC).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply]; unfold patchTransferRemainder; ring)

lemma patchFieldTransferError_ae_bound {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a) (hε : 0<ε) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    ∀ᵐ x, |patchFieldTransferError S u ha hb ht.2 y hn s x|≤
      patchTransferRemainder S u ha hb ht.2 y hn r ε s x := by
  filter_upwards [ae_position_ne m y,hcs] with x hxy hcore
  have hh := patch_raw_field_transfer S u ha hb hsmall ht y hn hr hra s x hcore hxy
  have hyoung := sqrt_young ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn s x)
    (mul_nonneg (by positivity) (patchSliceTFGap_nonneg S u ha hb ht.2 y hn s x)) hε
  have he : ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn s x)/(4*ε)=
      (5/(4*r*ε))*patchSliceTFGap S u ha hb ht.2 y hn s x := by ring
  rw [he] at hyoung
  rw [deletedLabels_patchRetained] at hh
  change |_ - _|≤_
  unfold patchTransferRemainder
  linarith

theorem patchFieldTransferError_integrable_mean {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a) (hε : 0<ε)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    (∀ s, Integrable (fun x => mass (u.coreSlice s x)*patchFieldTransferError S u ha hb ht.2 y hn s x)) ∧
    |sliceExpectation u (patchFieldTransferError S u ha hb ht.2 y hn)|≤
      sliceExpectation u (patchTransferRemainder S u ha hb ht.2 y hn r ε) := by
  have hR := fun s => patchTransferRemainder_weight_integrable S u ha hb ht.2 y hn r ε s (hcs s)
  have hB := fun s => patchFieldTransferError_ae_bound S u ha hb hsmall ht y hn hr hra hε s (hcs s)
  have hI (s) : Integrable (fun x => mass (u.coreSlice s x)*patchFieldTransferError S u ha hb ht.2 y hn s x) := by
    apply (hR s).mono' ((mass_coreSlice_integrable u s).aestronglyMeasurable.mul
      (patchFieldTransferError_aestronglyMeasurable S u ha hb ht.2 y hn s))
    filter_upwards [hB s] with x hx
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mass_nonneg _)]
    exact mul_le_mul_of_nonneg_left hx (mass_nonneg _)
  refine ⟨hI,?_⟩
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s _
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hI s).abs (hR s)
  filter_upwards [hB s] with x hx
  rw [abs_mul,abs_of_nonneg (mass_nonneg _)]
  exact mul_le_mul_of_nonneg_left hx (mass_nonneg _)
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FreshFieldTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma fresh_raw_coulomb_weight_integrable {m k : ℕ} (u : H1Vector (m+k)) (y : Space) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*(coreCoulombPotential (u.coreSlice s x).normalized y+
      nuclearPotential (unitNucleus y) x)) := by
  have hc : Integrable (fun x => mass (u.coreSlice s x)*coreCoulombPotential (u.coreSlice s x).normalized y) := by
    simp only [←nuclearEnergy_unit_eq_coreCoulomb]
    change Integrable (fun x => mass (u.coreSlice s x)*potentialForm (nuclearPotential (unitNucleus y))
      (u.coreSlice s x).normalized)
    simp_rw [potentialForm_normalized_weight]
    exact potentialForm_coreSlice_integrable u s _ (fun t => u.core_nuclear_integrable (unitNucleus y) (Fin.append s t))
  have ho := slice_weight_integrable_const u (nuclearPotential (unitNucleus y))
    (u.outer_nuclear_integrable (unitNucleus y)) s
  apply (hc.add ho).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply]; rw [mul_add])

lemma fresh_raw_screened_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (y : Space) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*(coreScreenedField S (u.coreSlice s x).normalized y-
      nuclearPotential (unitNucleus y) x)) := by
  apply (((mass_coreSlice_integrable u s).mul_const (attraction S y)).sub
    (fresh_raw_coulomb_weight_integrable u y s)).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply]; unfold coreScreenedField; ring)

theorem patchTFScreenedField_weight_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a) (hε : 0<ε)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*patchTFScreenedField S (u.coreSlice s x).normalized ha hb ht.2 y hn y) := by
  have hE := (patchFieldTransferError_integrable_mean S u ha hb hsmall ht y hn hr hra hε hcs).1 s
  apply ((fresh_raw_screened_weight_integrable S u y s).sub hE).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply]; unfold patchFieldTransferError; ring)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FreshMeanBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

lemma field_lower_of_gap {v G q L : ℝ} (hG : 0≤G) (hq : 0<q) (hL : 0≤L)
    (hgood : G≤q → L≤v) : L-(L/q)*G-max (-v) 0≤v := by
  by_cases hg : G≤q
  · have hp : 0≤(L/q)*G := mul_nonneg (div_nonneg hL hq.le) hG
    linarith [hgood hg,le_max_right (-v) 0]
  · have hg : q≤G := (lt_of_not_ge hg).le
    have H := mul_le_mul_of_nonneg_left hg (div_nonneg hL hq.le)
    rw [div_mul_cancel₀ L hq.ne'] at H
    linarith [le_max_left (-v) 0]

lemma field_upper_of_gap {v G q U C : ℝ} (hG : 0≤G) (hq : 0<q)
    (hU : 0≤U) (hC : 0≤C) (hcap : v≤C) (hgood : G≤q → v≤U) :
    v≤U+(C/q)*G := by
  by_cases hg : G≤q
  · have hp : 0≤(C/q)*G := mul_nonneg (div_nonneg hC hq.le) hG
    linarith [hgood hg]
  · have hg : q≤G := (lt_of_not_ge hg).le
    have H := mul_le_mul_of_nonneg_left hg (div_nonneg hC hq.le)
    rw [div_mul_cancel₀ C hq.ne'] at H
    linarith

lemma weighted_field_mean_lower {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w v G : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hv : Integrable (fun x => w x*v x) μ)
    (hGi : Integrable (fun x => w x*G x) μ)
    (hneg : Integrable (fun x => w x*max (-v x) 0) μ)
    {q L : ℝ} (hq : 0<q) (hL : 0≤L) (hG : ∀ᵐ x ∂μ, 0≤G x)
    (hgood : ∀ᵐ x ∂μ, w x≠0 → G x≤q → L≤v x) :
    L*(∫ x,w x ∂μ)-(L/q)*(∫ x,w x*G x ∂μ)-
      (∫ x,w x*max (-v x) 0 ∂μ)≤∫ x,w x*v x ∂μ := by
  have hi := ((hw.const_mul L).sub (hGi.const_mul (L/q))).sub hneg
  have H := integral_mono_ae hi hv (show ∀ᵐ x ∂μ,
      L*w x-(L/q)*(w x*G x)-w x*max (-v x) 0≤w x*v x from ?_)
  · have he := integral_sub ((hw.const_mul L).sub (hGi.const_mul (L/q))) hneg
    have he' := integral_sub (hw.const_mul L) (hGi.const_mul (L/q))
    simp only [Pi.sub_apply] at he he' H
    rw [he,he',integral_const_mul,integral_const_mul] at H
    exact H
  · filter_upwards [hw0,hG,hgood] with x hw hg hh
    by_cases hz : w x=0
    · simp [hz]
    nlinarith [mul_le_mul_of_nonneg_left (field_lower_of_gap hg hq hL (hh hz)) hw]

lemma weighted_field_mean_upper {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w v G : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hv : Integrable (fun x => w x*v x) μ)
    (hGi : Integrable (fun x => w x*G x) μ)
    {q U C : ℝ} (hq : 0<q) (hU : 0≤U) (hC : 0≤C)
    (hG : ∀ᵐ x ∂μ, 0≤G x) (hcap : ∀ᵐ x ∂μ, w x≠0 → v x≤C)
    (hgood : ∀ᵐ x ∂μ, w x≠0 → G x≤q → v x≤U) :
    (∫ x,w x*v x ∂μ)≤U*(∫ x,w x ∂μ)+(C/q)*(∫ x,w x*G x ∂μ) := by
  have hi := (hw.const_mul U).add (hGi.const_mul (C/q))
  have H := integral_mono_ae hv hi (show ∀ᵐ x ∂μ,
      w x*v x≤U*w x+(C/q)*(w x*G x) from ?_)
  · simpa only [Pi.add_apply,integral_add (hw.const_mul U) (hGi.const_mul (C/q)),
      integral_const_mul] using H
  · filter_upwards [hw0,hG,hcap,hgood] with x hw hg hc hh
    by_cases hz : w x=0
    · simp [hz]
    nlinarith [mul_le_mul_of_nonneg_left (field_upper_of_gap hg hq hU hC (hc hz) (hh hz)) hw]
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_LipschitzMollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Topology ContDiff Convolution
noncomputable section
namespace NeutralAtom

theorem exists_smooth_lipschitz_approx
    (K : EuclideanSpace ℝ (Fin 3) → ℝ) {A R ε : ℝ} (hA : 0≤A) (hε : 0<ε)
    (y : EuclideanSpace ℝ (Fin 3))
    (hs : ∀ z, R<‖z-y‖ → K z=0)
    (hL : ∀ z v, |K z-K v|≤A*‖z-v‖) :
    ∃ χ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ⊆Metric.closedBall y (R+ε) ∧
      (∀ z v, |χ z-χ v|≤A*‖z-v‖) ∧ (∀ z, |χ z-K z|≤A*ε) := by
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨ε/2,ε,by positivity,by linarith⟩
  have hKl : LipschitzWith ⟨A,hA⟩ K := by
    apply LipschitzWith.of_dist_le_mul
    intro z v
    change dist (K z) (K v) ≤ A*dist z v
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs] using hL z v
  have hKc := hKl.continuous
  let χ := φ.normed volume ⋆[lsmul ℝ ℝ,volume] K
  have hχ : ContDiff ℝ ∞ χ :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      φ.contDiff_normed hKc.locallyIntegrable
  have hi (z : EuclideanSpace ℝ (Fin 3)) :
      Integrable (fun u => φ.normed volume u * K (z-u)) := by
    exact φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed hKc.locallyIntegrable z
  refine ⟨χ,hχ,?_,?_,?_⟩
  · apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    change χ z≠0 at hz
    by_contra hn
    have hd : R+ε<‖z-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hn
    apply hz
    change (∫ u, φ.normed volume u*K (z-u))=0
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    change φ.normed volume u*K (z-u)=0
    by_cases hu : φ.normed volume u=0
    · simp only [hu,zero_mul]
    have hu' : ‖u‖<ε := by
      have hh : u∈Function.support (φ.normed volume) := hu
      rw [φ.support_normed_eq] at hh
      simpa only [Metric.mem_ball,dist_zero_right] using hh
    have htri : ‖z-y‖≤‖z-u-y‖+‖u‖ := by
      calc _=‖(z-u-y)+u‖ := by congr 1; module
           _≤_ := norm_add_le _ _
    rw [hs _ (by linarith),mul_zero]
  · intro z v
    change |(∫ u, φ.normed volume u*K (z-u))-(∫ u, φ.normed volume u*K (v-u))|≤_
    rw [←integral_sub (hi z) (hi v)]
    calc
      _≤∫ u, |φ.normed volume u*K (z-u)-φ.normed volume u*K (v-u)| := abs_integral_le_integral_abs
      _≤∫ u, φ.normed volume u*(A*‖z-v‖) := by
        apply integral_mono
        · simpa only [Pi.sub_apply,Real.norm_eq_abs] using ((hi z).sub (hi v)).norm
        · exact φ.integrable_normed.mul_const _
        · intro u
          dsimp only
          rw [←mul_sub,abs_mul,abs_of_nonneg (φ.nonneg_normed u)]
          have he : z-u-(v-u)=z-v := by module
          exact mul_le_mul_of_nonneg_left (by simpa only [he] using hL (z-u) (v-u)) (φ.nonneg_normed u)
      _=A*‖z-v‖ := by rw [integral_mul_const,φ.integral_normed,one_mul]
  · intro z
    have hh := φ.dist_normed_convolution_le (μ := volume) hKc.aestronglyMeasurable
      (x₀ := z) (ε := A*ε) (fun v hv => by
        rw [Real.dist_eq]
        exact (hL v z).trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_ball,dist_eq_norm] using hv.le) hA))
    exact hh

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_LipschitzTestEnergy
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
namespace Coulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

lemma smooth_test_energy_identity {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) :
    (∫ x, testCharge χ x*χ x)=
      (4*Real.pi)⁻¹*∑ a : Fin 3, ∫ x, (dirPartial χ (axis a) x)^2 := by
  have hp (v : Space) : ContDiff ℝ ∞ (dirPartial χ v) :=
    NeutralAtom.contDiff_partial (by simpa using hχ) v
  have hpc (v : Space) := NeutralAtom.hasCompactSupport_partial hc v
  have hpp (v : Space) : ContDiff ℝ ∞ (dirPartial (dirPartial χ v) v) :=
    NeutralAtom.contDiff_partial (by simpa using hp v) v
  have hcross (v : Space) : Integrable (fun x : Space => (dirPartial χ v x)^2) (volume : Measure Space) := by
    have hh : HasCompactSupport (fun x => dirPartial χ v x*dirPartial χ v x) := (hpc v).mul_right
    have hc : Continuous (fun x : Space => (dirPartial χ v x)^2) := (hp v).continuous.pow 2
    exact hc.integrable_of_hasCompactSupport (μ := (volume : Measure Space)) (by simpa only [pow_two] using hh)
  have hsecond (v : Space) : Integrable (fun x => χ x*dirPartial (dirPartial χ v) v x) :=
    (hχ.continuous.mul (hpp v).continuous).integrable_of_hasCompactSupport hc.mul_right
  have hprod (v : Space) : Integrable (fun x => χ x*dirPartial χ v x) :=
    (hχ.continuous.mul (hp v).continuous).integrable_of_hasCompactSupport hc.mul_right
  have hibp (v : Space) : (∫ x, χ x*dirPartial (dirPartial χ v) v x)=
      -(∫ x, (dirPartial χ v x)^2) := by
    simpa only [dirPartial,pow_two] using
      (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by simpa only [pow_two,dirPartial] using hcross v) (hsecond v) (hprod v)
        (fun x _ => hχ.differentiable (by simp) x)
        (fun x _ => (hp v).differentiable (by simp) x))
  have he : (fun x => testCharge χ x*χ x)=
      (fun x => -(4*Real.pi)⁻¹*∑ a : Fin 3, χ x*dirPartial (dirPartial χ (axis a)) (axis a) x) := by
    funext x
    rw [testCharge,NeutralAtom.coordinateLaplacian_eq_partials
      ((hχ.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt),←Finset.mul_sum]
    ring
  rw [he,integral_const_mul,integral_finsetSum _ (fun a _ => hsecond (axis a))]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib]
  ring

lemma smooth_test_energy_le {χ : Space → ℝ} {A R : ℝ} (hA : 0≤A)
    (hχ : ContDiff ℝ ∞ χ) (y : Space)
    (hs : tsupport χ⊆Metric.closedBall y R)
    (hL : ∀ z v, |χ z-χ v|≤A*‖z-v‖) :
    (∫ x, testCharge χ x*χ x)≤
      (4*Real.pi)⁻¹*(3*(volume (Metric.closedBall y R)).toReal*A^2) := by
  have hc : HasCompactSupport χ := (isCompact_closedBall y R).of_isClosed_subset (isClosed_tsupport χ) hs
  rw [smooth_test_energy_identity hχ hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsingle (a : Fin 3) : (∫ x, (dirPartial χ (axis a) x)^2)≤
      (volume (Metric.closedBall y R)).toReal*A^2 := by
    have hd (x : Space) : |dirPartial χ (axis a) x|≤A := by
      have hd := norm_fderiv_le_of_lip' ℝ (f := χ) (x₀ := x) hA (Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs] using hL z x))
      have ha : ‖axis a‖=1 := by simp [axis]
      have hh := (fderiv ℝ χ x).le_opNorm (axis a)
      rw [ha,mul_one] at hh
      exact (show |dirPartial χ (axis a) x|≤‖fderiv ℝ χ x‖ from hh).trans hd
    have hout (x : Space) (hx : x∉Metric.closedBall y R) : (dirPartial χ (axis a) x)^2=0 := by
      rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs (NeutralAtom.tsupport_dirPartial_subset χ _ hh)))]
      norm_num
    rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    have hh := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (isCompact_closedBall y R).measure_lt_top (fun z _ => show ‖(dirPartial χ (axis a) z)^2‖≤A^2 by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA).2 (hd z))
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,Measure.real,mul_comm] using hh)
  have HH := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hsingle a)
  simpa [mul_assoc] using HH

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
namespace Coulomb

theorem raw_coulomb_lipschitz_test {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {σ K : Space → ℝ} {A B R : ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω)) (hσs : ∀ x∉Ω, σ x=0)
    (hA : 0≤A) (hR : 0<R) (y : Space)
    (hB : ∀ x, |K x|≤B) (hK : ∀ x, R<‖x-y‖ → K x=0)
    (hL : ∀ z v, |K z-K v|≤A*‖z-v‖)
    (hball : Metric.closedBall y (2*R)⊆Ω) :
    (∫ x, σ x*K x)^2 ≤ coulombBilinear σ σ*
      ((4*Real.pi)⁻¹*(3*(volume (Metric.closedBall y (2*R))).toReal*A^2)) := by
  let ε : ℕ → ℝ := fun n => R*(1/((n:ℝ)+1))
  have hε (n : ℕ) : 0<ε n := by dsimp [ε]; positivity
  have hεR (n : ℕ) : ε n≤R := by
    dsimp [ε]
    apply mul_le_of_le_one_right hR.le
    exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hεt : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul R
  choose χ hsm hsp hLip happ using
    (fun n => NeutralAtom.exists_smooth_lipschitz_approx K hA (hε n) y hK hL)
  have hiΩ : Integrable σ (volume.restrict Ω) := hσ.integrable (by norm_num [TFExponent])
  have hind : Ω.indicator σ=σ := by
    funext x
    by_cases hx : x∈Ω
    · exact indicator_of_mem hx σ
    · rw [indicator_of_notMem hx,hσs x hx]
  have hi : Integrable σ := by
    have hh := (integrable_indicator_iff hΩ).2 hiΩ
    rwa [hind] at hh
  have hpoint (x : Space) : Tendsto (fun n => χ n x) atTop (𝓝 (K x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hh : Tendsto (fun n => A*ε n) atTop (𝓝 0) := by simpa using hεt.const_mul A
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by simpa only [Real.dist_eq] using happ n x) hh
  have hdom (n : ℕ) (x : Space) : |χ n x|≤B+A*R := by
    calc
      _≤|χ n x-K x|+|K x| := by simpa only [sub_add_cancel] using abs_add_le (χ n x-K x) (K x)
      _≤A*ε n+B := add_le_add (happ n x) (hB x)
      _≤_ := by have hh := mul_le_mul_of_nonneg_left (hεR n) hA; linarith
  have hconv : Tendsto (fun n => ∫ x, σ x*χ n x) atTop (𝓝 (∫ x, σ x*K x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖σ x‖*(B+A*R))
    · intro n
      exact hi.aestronglyMeasurable.mul (hsm n).continuous.aestronglyMeasurable
    · exact hi.norm.mul_const _
    · intro n
      filter_upwards [] with x
      rw [norm_mul,Real.norm_eq_abs (χ n x)]
      exact mul_le_mul_of_nonneg_left (hdom n x) (norm_nonneg _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (hpoint x)
  have hQ := raw_coulomb_nonneg hΩ hσ hσs
  apply le_of_tendsto (hconv.pow 2)
  filter_upwards [] with n
  have hsp' : tsupport (χ n)⊆Metric.closedBall y (2*R) :=
    (hsp n).trans (Metric.closedBall_subset_closedBall (by linarith [hεR n]))
  have hc : HasCompactSupport (χ n) := (isCompact_closedBall y (2*R)).of_isClosed_subset
    (isClosed_tsupport _) hsp'
  exact (raw_coulomb_smooth_test hΩ (hsm n) hc (hsp'.trans hball) hσ hσs).trans
    (mul_le_mul_of_nonneg_left (smooth_test_energy_le hA (hsm n) y hsp' (hLip n)) hQ)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_WeightedNegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
noncomputable section
namespace NeutralAtom

lemma weighted_nonneg_integrable_of_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w Y G : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hY : AEStronglyMeasurable Y μ) (hY0 : ∀ᵐ x ∂μ, 0≤Y x)
    (hGi : Integrable (fun x => w x*G x) μ) {A d : ℝ}
    (hbound : ∀ᵐ x ∂μ, w x≠0 → Y x≤A*G x+d) :
    Integrable (fun x => w x*Y x) μ := by
  apply ((hGi.const_mul A).add (hw.const_mul d)).mono' (hw.aestronglyMeasurable.mul hY)
  filter_upwards [hw0,hY0,hbound] with x hw hy hb
  change ‖w x*Y x‖≤A*(w x*G x)+d*w x
  rw [Real.norm_of_nonneg (mul_nonneg hw hy)]
  by_cases hz : w x=0
  · simp [hz]
  have H := mul_le_mul_of_nonneg_left (hb hz) hw
  change w x*Y x≤A*(w x*G x)+d*w x
  nlinarith

lemma weighted_integral_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w Y G : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hY : AEStronglyMeasurable Y μ) (hY0 : ∀ᵐ x ∂μ, 0≤Y x)
    (hGi : Integrable (fun x => w x*G x) μ) {A d : ℝ}
    (hbound : ∀ᵐ x ∂μ, w x≠0 → Y x≤A*G x+d) :
    (∫ x, w x*Y x ∂μ)≤A*(∫ x, w x*G x ∂μ)+d*(∫ x, w x ∂μ) := by
  have H := integral_mono_ae (weighted_nonneg_integrable_of_le hw hw0 hY hY0 hGi hbound)
    ((hGi.const_mul A).add (hw.const_mul d)) (show ∀ᵐ x ∂μ,
      w x*Y x≤A*(w x*G x)+d*w x from ?_)
  · simpa only [Pi.add_apply,integral_add (hGi.const_mul A) (hw.const_mul d),integral_const_mul] using H
  · filter_upwards [hw0,hbound] with x hw hb
    by_cases hz : w x=0
    · simp [hz]
    nlinarith [mul_le_mul_of_nonneg_left (hb hz) hw]

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PatchNegativeMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

theorem exists_patch_negative_mean_bound :
    ∃ C : ℝ, 0<C ∧ ∀ {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 0 ≤ r → r≤a → C*(r/a)≤1/2 →
    ∀ (χ : Space → ℝ) (K M : ℝ), 0≤K → 0<M → Measurable χ →
    (∀ z, 0≤χ z ∧ χ z≤K) → (∀ z, χ z≠0 → ‖z-y‖ ≤ r) →
    (∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      M≤∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*χ z) →
    (∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*
      max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0)) ∧
    (∑ p, sliceExpectation (T.vector p) (fun s x =>
      max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0))≤
      (2*K/M)*(∑ p, sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))+
      (2*(C*(r/a))*(a^4)⁻¹)*T.totalMass := by
  obtain ⟨C,hC,H⟩ := exists_patch_negative_center_bound
  refine ⟨C,hC,?_⟩
  intro J n S T a b t r ha hb hsmall ht y hn hcs hr hra hθ χ K M hK hM hχm hχ hs hmass
  let Y := fun p s x => max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0
  let G := fun p s x => patchSliceTFGap S (T.vector p) ha hb ht.2 y hn s x
  let A := 2*K/M
  let d := 2*(C*(r/a))*(a^4)⁻¹
  have hcs' (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x,
      SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun _ hx => hx.normalized)
  have hGi (p : T.index) (s : Spins (T.out p)) :
      Integrable (fun x => mass ((T.vector p).coreSlice s x)*G p s x) :=
    patchSliceTFGap_weight_integrable S (T.vector p) ha hb ht.2 y hn s (hcs' p s)
  have hYm (p : T.index) (s : Spins (T.out p)) : AEStronglyMeasurable (Y p s) volume :=
    (patchTFScreenedField_slice_aestronglyMeasurable S (T.vector p) s ha hb ht.2 y hn y).neg.sup aestronglyMeasurable_const
  have hY0 (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x, 0≤Y p s x :=
    Eventually.of_forall (fun _ => le_max_right _ _)
  have hbound (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x,
      mass ((T.vector p).coreSlice s x)≠0 → Y p s x≤A*G p s x+d := by
    filter_upwards [hcs' p s,hmass p s] with x hx hm
    intro hw
    apply H S ((T.vector p).coreSlice s x).normalized ha hb hsmall ht y hx hn hr hra hθ x χ K M hK hM
      (Eventually.of_forall hχ) _ hs (hm hw)
    exact (retainedFineDensity_integrable hb _ _).mul_bdd hχm.aestronglyMeasurable
      (Eventually.of_forall (fun z => by rw [Real.norm_of_nonneg (hχ z).1]; exact (hχ z).2))
  have hYi (p : T.index) (s : Spins (T.out p)) :
      Integrable (fun x => mass ((T.vector p).coreSlice s x)*Y p s x) :=
    NeutralAtom.weighted_nonneg_integrable_of_le (mass_coreSlice_integrable (T.vector p) s)
      (Eventually.of_forall (fun _ => mass_nonneg _)) (hYm p s) (hY0 p s) (hGi p s) (hbound p s)
  refine ⟨hYi,?_⟩
  have hmean (p : T.index) : sliceExpectation (T.vector p) (Y p)≤
      A*sliceExpectation (T.vector p) (G p)+d*mass (T.vector p) := by
    have HH := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
      NeutralAtom.weighted_integral_le (mass_coreSlice_integrable (T.vector p) s)
        (Eventually.of_forall (fun _ => mass_nonneg _)) (hYm p s) (hY0 p s) (hGi p s) (hbound p s))
    simpa only [Finset.sum_add_distrib,←Finset.mul_sum,integral_mass_coreSlice,sliceExpectation] using HH
  have HH := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hmean p)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,RecordedEnsemble.totalMass,Y,G,A,d] using HH

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ExplicitMultiplyGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

open scoped ENNReal Convolution

theorem observationNoiseDensity_contDiff : ContDiff ℝ ∞ observationNoiseDensity :=
  contDiff_const.mul observationNoiseBase_contDiff

theorem observationNoiseDensity_formula (u : ℝ) :
    observationNoiseDensity u = observationNoiseNormalizer*
      (if |u| < 1 then Real.exp (-(1-u^2)⁻¹) else 0) := by
  rw [observationNoiseDensity, observationNoiseBase_formula]

theorem observationNoiseDensity_even (u : ℝ) :
    observationNoiseDensity (-u) = observationNoiseDensity u := by
  simp [observationNoiseDensity, observationNoiseBase]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_WindowSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set
open scoped SchwartzMap
noncomputable section
namespace NeutralAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem schwartz_square_bounded_lipschitz (g : 𝓢(E,ℝ)) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ (∀ x, |g x^2| ≤ B) ∧
      (∀ x v, |g x^2-g v^2| ≤ L*‖x-v‖) := by
  let M := SchwartzMap.seminorm ℝ 0 0 g
  let D := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ E ℝ g)
  have hM : 0 ≤ M := apply_nonneg _ _
  have hD : 0 ≤ D := apply_nonneg _ _
  have hm (x : E) : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using g.norm_le_seminorm ℝ x
  have hd (x : E) : ‖fderiv ℝ g x‖ ≤ D :=
    (SchwartzMap.fderivCLM ℝ E ℝ g).norm_le_seminorm ℝ x
  have hl (x v : E) : |g x-g v| ≤ D*‖x-v‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := (g : E → ℝ)) (f' := fderiv ℝ g)
      (fun z (_ : z∈(univ : Set E)) => (g.hasFDerivAt z).hasFDerivWithinAt)
      (fun z _ => hd z) (convex_univ : Convex ℝ (univ : Set E)) (mem_univ v) (mem_univ x)
    simpa only [Real.norm_eq_abs] using hh
  refine ⟨M^2,2*M*D,sq_nonneg _,mul_nonneg (mul_nonneg (by norm_num) hM) hD,?_,?_⟩
  · intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hm x) 2
  · intro x v
    have hsum : |g x+g v| ≤ 2*M := (abs_add_le _ _).trans (by linarith [hm x,hm v])
    rw [show g x^2-g v^2=(g x-g v)*(g x+g v) by ring,abs_mul]
    calc
      _ ≤ (D*‖x-v‖)*(2*M) := mul_le_mul (hl x v) hsum (abs_nonneg _) (mul_nonneg hD (norm_nonneg _))
      _ = _ := by ring
end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_KernelScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set
namespace NeutralAtom

lemma inv_upper_of_half_le {T a : ℝ} (hT : 0 < T) (ha : T/2 ≤ a) :
    a⁻¹ ≤ 2/T := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos hT) ha
  calc
    a⁻¹ ≤ (T/2)⁻¹ := (inv_le_inv₀ ha0 (half_pos hT)).mpr ha
    _ = 2/T := by simp [div_eq_mul_inv]

lemma inv_sub_bound_of_half_le {T a b : ℝ}
    (hT : 0 < T) (ha : T/2 ≤ a) (hb : T/2 ≤ b) :
    |a⁻¹-b⁻¹| ≤ (4/T^2)*|a-b| := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos hT) ha
  have hb0 : 0 < b := lt_of_lt_of_le (half_pos hT) hb
  rw [inv_sub_inv' ha0.ne' hb0.ne', abs_mul,abs_mul,
    abs_of_pos (inv_pos.mpr ha0),abs_of_pos (inv_pos.mpr hb0),abs_sub_comm b a]
  calc
    _ ≤ ((2/T)*|a-b|)*(2/T) := mul_le_mul
      (mul_le_mul_of_nonneg_right (inv_upper_of_half_le hT ha) (abs_nonneg _))
      (inv_upper_of_half_le hT hb) (inv_nonneg.mpr hb0.le)
      (mul_nonneg (by positivity) (abs_nonneg _))
    _ = _ := by ring

lemma inv_cube_sub_bound_of_half_le {T a b : ℝ}
    (hT : 0 < T) (ha : T/2 ≤ a) (hb : T/2 ≤ b) :
    |(a^3)⁻¹-(b^3)⁻¹| ≤ (48/T^4)*|a-b| := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos hT) ha
  have hb0 : 0 < b := lt_of_lt_of_le (half_pos hT) hb
  have href : ∀ z ∈ Ici (T/2),
      HasDerivWithinAt (fun x : ℝ => x^(-3:ℝ)) (-3*z^(-4:ℝ)) (Ici (T/2)) z := by
    intro z hz
    have hd := (Real.hasDerivAt_rpow_const (x := z) (p := -3)
      (Or.inl (ne_of_gt (lt_of_lt_of_le (half_pos hT) hz)))).hasDerivWithinAt (s := Ici (T/2))
    norm_num only at hd
    exact hd
  have hbd : ∀ z ∈ Ici (T/2), ‖-3*z^(-4:ℝ)‖ ≤ 48/T^4 := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le (half_pos hT) hz
    rw [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<3),
      Real.norm_of_nonneg (Real.rpow_nonneg hz0.le _)]
    calc
      _ ≤ 3*(T/2)^(-4:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (half_pos hT) hz (by norm_num)) (by norm_num)
      _ = 48/T^4 := by norm_num [Real.rpow_neg (le_of_lt (half_pos hT)),Real.rpow_natCast]; ring
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le href hbd (convex_Ici _)
    (show a ∈ Ici (T/2) from ha) (show b ∈ Ici (T/2) from hb)
  simpa only [Real.norm_eq_abs,show (-3:ℝ) = -(3:ℝ) by norm_num,
    Real.rpow_neg ha0.le,Real.rpow_neg hb0.le,Real.rpow_ofNat,abs_sub_comm] using hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma inverse_scaled_argument_bound {T a b : ℝ} (hT : 0 < T)
    (ha : T/2 ≤ a) (hb : T/2 ≤ b) (x v : E) (hv : ‖v‖ ≤ 2*T) :
    ‖a⁻¹ • x-b⁻¹ • v‖ ≤ (2/T)*‖x-v‖+(8/T)*|a-b| := by
  have ha0 : 0<a := lt_of_lt_of_le (half_pos hT) ha
  have he : a⁻¹ • x-b⁻¹ • v = a⁻¹ • (x-v)+(a⁻¹-b⁻¹) • v := by module
  rw [he]
  calc
    _ ≤ ‖a⁻¹ • (x-v)‖+‖(a⁻¹-b⁻¹) • v‖ := norm_add_le _ _
    _ = a⁻¹*‖x-v‖+|a⁻¹-b⁻¹| *‖v‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha0)]
    _ ≤ (2/T)*‖x-v‖+((4/T^2)*|a-b|)*(2*T) := add_le_add
      (mul_le_mul_of_nonneg_right (inv_upper_of_half_le hT ha) (norm_nonneg _))
      (mul_le_mul (inv_sub_bound_of_half_le hT ha hb) hv (norm_nonneg _)
        (mul_nonneg (by positivity) (abs_nonneg _)))
    _ = _ := by field_simp; ring

theorem scaled_kernel_local_bound {T a b B L : ℝ} (hT : 0 < T)
    (ha : T/2 ≤ a) (hb : T/2 ≤ b) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (φ : E → ℝ) (hφ : ∀ x, |φ x| ≤ B)
    (hφL : ∀ x v, |φ x-φ v| ≤ L*‖x-v‖)
    (x v : E) (hv : ‖v‖ ≤ 2*T) :
    |(a^3)⁻¹*φ (a⁻¹ • x)-(b^3)⁻¹*φ (b⁻¹ • v)| ≤
      ((48*B+64*L)/T^4)*|a-b|+(16*L/T^4)*‖x-v‖ := by
  have hb0 : 0<b := lt_of_lt_of_le (half_pos hT) hb
  have hb3 : (b^3)⁻¹ ≤ 8/T^3 := by
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hb0.le) (inv_upper_of_half_le hT hb) 3
    simpa only [inv_pow,div_pow,show (2:ℝ)^3=8 by norm_num] using hh
  have he : (a^3)⁻¹*φ (a⁻¹ • x)-(b^3)⁻¹*φ (b⁻¹ • v) =
      ((a^3)⁻¹-(b^3)⁻¹)*φ (a⁻¹ • x)+(b^3)⁻¹*(φ (a⁻¹ • x)-φ (b⁻¹ • v)) := by ring
  rw [he]
  calc
    _ ≤ |((a^3)⁻¹-(b^3)⁻¹)*φ (a⁻¹ • x)|+
        |(b^3)⁻¹*(φ (a⁻¹ • x)-φ (b⁻¹ • v))| := abs_add_le _ _
    _ = |(a^3)⁻¹-(b^3)⁻¹| *|φ (a⁻¹ • x)|+
        (b^3)⁻¹*|φ (a⁻¹ • x)-φ (b⁻¹ • v)| := by
      rw [abs_mul,abs_mul,abs_of_pos (inv_pos.mpr (pow_pos hb0 _))]
    _ ≤ ((48/T^4)*|a-b|)*B+(8/T^3)*
        (L*((2/T)*‖x-v‖+(8/T)*|a-b|)) := add_le_add
      ((mul_le_mul_of_nonneg_left (hφ _) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (inv_cube_sub_bound_of_half_le hT ha hb) hB))
      (mul_le_mul hb3 ((hφL _ _).trans (mul_le_mul_of_nonneg_left
        (inverse_scaled_argument_bound hT ha hb x v hv) hL))
        (abs_nonneg _) (by positivity))
    _ = _ := by field_simp; ring

end NeutralAtom

end
open Set
namespace NeutralAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scaledCenterKernel_support (φ : E → ℝ) (t : E → ℝ)
    (hs : ∀ x, 1 < ‖x‖ → φ x = 0) (ht : ∀ z, 0 < t z)
    (z y : E) (hK : scaledCenterKernel φ t z y ≠ 0) : ‖y-z‖ ≤ t z := by
  by_contra h
  have hu : 1 < ‖(t z)⁻¹ • (y-z)‖ := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (ht z).le),←div_eq_inv_mul]
    exact (lt_div_iff₀ (ht z)).mpr (by simpa using lt_of_not_ge h)
  exact hK (by simp [scaledCenterKernel,hs _ hu])

lemma scaledCenterKernel_support_width (φ : E → ℝ) (t : E → ℝ)
    (hs : ∀ x, 1 < ‖x‖ → φ x = 0) (ht : ∀ z, 0 < t z)
    (hLip : ∀ x v, |t x-t v| ≤ ‖x-v‖/4)
    (z y : E) (hK : scaledCenterKernel φ t z y ≠ 0) :
    t z ∈ Icc (4*t y/5) (4*t y/3) ∧ ‖y-z‖ ≤ 4*t y/3 := by
  have hc := scaledCenterKernel_support φ t hs ht z y hK
  have hl := hLip z y
  rw [norm_sub_rev z y] at hl
  have hh : |t z-t y| ≤ t z/4 := hl.trans (by linarith)
  have hab := abs_le.mp hh
  constructor
  · constructor <;> linarith
  · linarith

lemma scaledCenterKernel_uniform_bound (φ : E → ℝ) (t : E → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hs : ∀ x, 1 < ‖x‖ → φ x = 0)
    (hφ : ∀ x, |φ x| ≤ B) (ht : ∀ z, 0 < t z)
    (hLip : ∀ x v, |t x-t v| ≤ ‖x-v‖/4) (z y : E) :
    |scaledCenterKernel φ t z y| ≤ 8*B/(t y)^3 := by
  have hT := ht y
  by_cases hK : scaledCenterKernel φ t z y=0
  · rw [hK,abs_zero]; positivity
  have hc := (scaledCenterKernel_support_width φ t hs ht hLip z y hK).1.1
  have hi := inv_upper_of_half_le (ht y) (show t y/2 ≤ t z by linarith [ht y])
  have hh := pow_le_pow_left₀ (inv_nonneg.mpr (ht z).le) hi 3
  have hh' : ((t z)^3)⁻¹ ≤ 8/(t y)^3 := by
    simpa only [inv_pow,div_pow,show (2:ℝ)^3=8 by norm_num] using hh
  rw [scaledCenterKernel,abs_mul,abs_of_pos (inv_pos.mpr (pow_pos (ht z) _))]
  calc
    _ ≤ (8/(t y)^3)*B := mul_le_mul hh' (hφ _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem scaledCenterKernel_center_lipschitz (φ : E → ℝ) (t : E → ℝ)
    {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hs : ∀ x, 1 < ‖x‖ → φ x = 0) (hφ : ∀ x, |φ x| ≤ B)
    (hφL : ∀ x v, |φ x-φ v| ≤ L*‖x-v‖) (ht : ∀ z, 0 < t z)
    (hLip : ∀ x v, |t x-t v| ≤ ‖x-v‖/4) (z z' y : E) :
    |scaledCenterKernel φ t z y-scaledCenterKernel φ t z' y| ≤
      ((64*B+80*L)/(t y)^4)*‖z-z'‖ := by
  have hT := ht y
  have hordered (z z' : E) (hK : scaledCenterKernel φ t z y≠0) :
      |scaledCenterKernel φ t z y-scaledCenterKernel φ t z' y| ≤
        ((64*B+80*L)/(t y)^4)*‖z-z'‖ := by
    have hc := scaledCenterKernel_support_width φ t hs ht hLip z y hK
    by_cases hf : t y/4 ≤ ‖z-z'‖
    · calc
        _ ≤ |scaledCenterKernel φ t z y|+|scaledCenterKernel φ t z' y| := by simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (scaledCenterKernel φ t z y) 0 (scaledCenterKernel φ t z' y))
        _ ≤ 16*B/(t y)^3 := by
          have h₁ := scaledCenterKernel_uniform_bound φ t hB hs hφ ht hLip z y
          have h₂ := scaledCenterKernel_uniform_bound φ t hB hs hφ ht hLip z' y
          calc
            _ ≤ 8*B/(t y)^3+8*B/(t y)^3 := add_le_add h₁ h₂
            _ = _ := by ring
        _ = ((64*B)/(t y)^4)*(t y/4) := by field_simp; ring
        _ ≤ ((64*B+80*L)/(t y)^4)*‖z-z'‖ := mul_le_mul
          (div_le_div_of_nonneg_right (show 64*B ≤ 64*B+80*L by linarith) (pow_nonneg (ht y).le _)) hf
          (by positivity) (by positivity)
    · have hnear : ‖z-z'‖ < t y/4 := lt_of_not_ge hf
      have hab := abs_le.mp (hLip z z')
      have hb : t y/2 ≤ t z' := by linarith [hc.1.1]
      have ha : t y/2 ≤ t z := by linarith [hc.1.1,ht y]
      have hv : ‖y-z'‖ ≤ 2*t y := by
        have hh : ‖y-z'‖ ≤ ‖y-z‖+‖z-z'‖ := by
          simpa only [sub_add_sub_cancel] using (norm_add_le (y-z) (z-z'))
        linarith [hc.2]
      have hh := scaled_kernel_local_bound (ht y) ha hb hB hL φ hφ hφL (y-z) (y-z') hv
      have he : (y-z)-(y-z')=z'-z := by abel
      rw [he,norm_sub_rev z' z] at hh
      have had : |t z-t z'| ≤ ‖z-z'‖ := (hLip z z').trans (by linarith [norm_nonneg (z-z')])
      apply hh.trans
      calc
        _ ≤ ((48*B+64*L)/(t y)^4)*‖z-z'‖+(16*L/(t y)^4)*‖z-z'‖ :=
          add_le_add (mul_le_mul_of_nonneg_left had (by positivity)) le_rfl
        _ = ((48*B+80*L)/(t y)^4)*‖z-z'‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (show 48*B+80*L ≤ 64*B+80*L by linarith) (pow_nonneg (ht y).le _)) (norm_nonneg _)
  by_cases hz : scaledCenterKernel φ t z y=0
  · by_cases hz' : scaledCenterKernel φ t z' y=0
    · rw [hz,hz',sub_self,abs_zero]; positivity
    · simpa only [abs_sub_comm,norm_sub_rev] using hordered z' z hz'
  · exact hordered z z' hz

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_KernelCenterMass
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace NeutralAtom

lemma continuous_scaledCenterKernel {φ t : Coulomb.Space → ℝ}
    (hφ : Continuous φ) (htc : Continuous t) (ht : ∀ z, 0 < t z) (y : Coulomb.Space) :
    Continuous (fun z => scaledCenterKernel φ t z y) := by
  unfold scaledCenterKernel
  exact ((htc.pow 3).inv₀ (fun z => pow_ne_zero _ (ht z).ne')).mul
    (hφ.comp ((htc.inv₀ (fun z => (ht z).ne')).smul (continuous_const.sub continuous_id)))

lemma integrable_scaledCenterKernel {φ t : Coulomb.Space → ℝ}
    (hφ : Continuous φ) (htc : Continuous t) (ht : ∀ z, 0 < t z)
    (hs : ∀ x, 1 < ‖x‖ → φ x=0)
    (hLip : ∀ z z', |t z-t z'| ≤ ‖z-z'‖/4) (y : Coulomb.Space) :
    Integrable (fun z => scaledCenterKernel φ t z y) := by
  apply (continuous_scaledCenterKernel hφ htc ht y).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Metric.closedBall y (2*t y)) (isCompact_closedBall _ _)
  intro z hz
  by_contra hK
  have hh := (scaledCenterKernel_support_width φ t hs ht hLip z y hK).2
  apply hz
  rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev]
  linarith [ht y]

lemma integral_constant_scaledCenterKernel (φ : Coulomb.Space → ℝ)
    {T : ℝ} (hT : 0 < T) (y : Coulomb.Space) :
    (∫ z, scaledCenterKernel φ (fun _ => T) z y) = ∫ z, φ z := by
  unfold scaledCenterKernel
  rw [integral_const_mul, integral_sub_left_eq_self
    (fun z : Coulomb.Space => φ (T⁻¹ • z)),
    Measure.integral_comp_inv_smul_of_nonneg volume φ hT.le]
  simp only [Coulomb.Space,finrank_euclideanSpace_fin,smul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hT.ne'),one_mul]

theorem center_kernel_mass_defect {φ t : Coulomb.Space → ℝ} {B L q : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hq : 0 ≤ q) (hqs : q ≤ 1/4)
    (hφc : Continuous φ) (htc : Continuous t) (ht : ∀ z, 0 < t z)
    (hs : ∀ x, 1 < ‖x‖ → φ x=0) (hφ : ∀ x, |φ x| ≤ B)
    (hφL : ∀ x v, |φ x-φ v| ≤ L*‖x-v‖)
    (hLip : ∀ z z', |t z-t z'| ≤ q*‖z-z'‖)
    (y : Coulomb.Space) :
    |(∫ z, scaledCenterKernel φ t z y)-(∫ z, φ z)| ≤
      (64*Real.pi/3)*(48*B+64*L)*q := by
  have hT := ht y
  have hLip' : ∀ z z', |t z-t z'| ≤ ‖z-z'‖/4 := by
    intro z z'
    calc
      _ ≤ q*‖z-z'‖ := hLip z z'
      _ ≤ (1/4)*‖z-z'‖ := mul_le_mul_of_nonneg_right hqs (norm_nonneg _)
      _ = _ := by ring
  let F : Coulomb.Space → ℝ := fun z => scaledCenterKernel φ t z y
  let G : Coulomb.Space → ℝ := fun z => scaledCenterKernel φ (fun _ => t y) z y
  have hFi : Integrable F := integrable_scaledCenterKernel hφc htc ht hs hLip' y
  have hGi : Integrable G := integrable_scaledCenterKernel hφc continuous_const (fun _ => hT) hs
    (by intro z z'; simp only [sub_self,abs_zero]; positivity) y
  have hpt (z : Coulomb.Space) (hz : z∈Metric.closedBall y (2*t y)) :
      |F z-G z| ≤ 2*(48*B+64*L)*q/(t y)^3 := by
    have hz' : ‖y-z‖ ≤ 2*t y := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hz
    have hwd : |t z-t y| ≤ 2*q*t y := by
      calc
        _ ≤ q*‖z-y‖ := hLip z y
        _ ≤ q*(2*t y) := mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hz') hq
        _ = _ := by ring
    have ha : t y/2 ≤ t z := by
      have hab := abs_le.mp hwd
      have hqt := mul_le_mul_of_nonneg_right hqs hT.le
      nlinarith
    have hh := scaled_kernel_local_bound hT ha (show t y/2 ≤ t y by linarith) hB hL φ hφ hφL
      (y-z) (y-z) hz'
    simp only [sub_self,norm_zero,mul_zero,add_zero] at hh
    calc
      _ ≤ ((48*B+64*L)/(t y)^4)*|t z-t y| := hh
      _ ≤ ((48*B+64*L)/(t y)^4)*(2*q*t y) := mul_le_mul_of_nonneg_left hwd (by positivity)
      _ = _ := by field_simp
  have hout (z : Coulomb.Space) (hz : z∉Metric.closedBall y (2*t y)) : F z-G z=0 := by
    have hz' : 2*t y < ‖y-z‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev,not_le] using hz
    have hF : F z=0 := by
      by_contra hh
      have hh' := (scaledCenterKernel_support_width φ t hs ht hLip' z y hh).2
      linarith
    have hG : G z=0 := by
      by_contra hh
      have hh' := scaledCenterKernel_support φ (fun _ => t y) hs (fun _ => hT) z y hh
      linarith
    rw [hF,hG,sub_self]
  rw [←integral_constant_scaledCenterKernel φ hT y,←integral_sub hFi hGi]
  change |∫ z, F z-G z| ≤ _
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  have hh := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (isCompact_closedBall y (2*t y)).measure_lt_top
    (fun z hz => (show ‖F z-G z‖ ≤ 2*(48*B+64*L)*q/(t y)^3 by simpa only [Real.norm_eq_abs] using hpt z hz))
  rw [Real.norm_eq_abs,Coulomb.volume_closedBall_three y (by positivity : 0 ≤ 2*t y)] at hh
  apply hh.trans_eq
  field_simp
  ring

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketWidthScalar
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set
namespace NeutralAtom

theorem clamped_width_scalar_lipschitz {w s u v : ℝ}
    (hw : 0  ≤  w) (hs : 0  <  s) (hu : 0  <  u) (hv : 0  <  v) :
    |u * (min u s)^w - v * (min v s)^w|  ≤
      (1+w)*s^w*|u-v| := by
  have hbelow {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ s) :
      |y*(min y s)^w-x*(min x s)^w|  ≤  (1+w)*s^w*(y-x) := by
    have href : ∀ z ∈ Icc x y,
        HasDerivWithinAt (fun z : ℝ => z^(w+1)) ((w+1)*z^w) (Icc x y) z := by
      intro z hz
      simpa only [add_sub_cancel_right] using (Real.hasDerivAt_rpow_const (p := w+1) (Or.inl (ne_of_gt (hx.trans_le hz.1)))).hasDerivWithinAt (s := Icc x y)
    have hbd : ∀ z ∈ Icc x y, ‖(w+1)*z^w‖  ≤  (1+w)*s^w := by
      intro z hz
      rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (hx.le.trans hz.1) _))]
      calc
        (w+1)*z^w  ≤  (w+1)*s^w := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hx.le.trans hz.1) (hz.2.trans hy) hw) (by linarith)
        _ = (1+w)*s^w := by ring
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le href hbd
      (convex_Icc x y) (show x ∈ Icc x y from ⟨le_rfl,hxy⟩)
      (show y ∈ Icc x y from ⟨hxy,le_rfl⟩)
    rw [Real.rpow_add_one (ne_of_gt (hx.trans_le hxy)), Real.rpow_add_one hx.ne',
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
    simpa only [min_eq_left hy, min_eq_left (hxy.trans hy), mul_comm] using hh
  have hordered {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
      |y*(min y s)^w-x*(min x s)^w|  ≤  (1+w)*s^w*(y-x) := by
    by_cases hy : y ≤ s
    · exact hbelow hx hxy hy
    by_cases hxs : s ≤ x
    · rw [min_eq_right hxs, min_eq_right (hxs.trans hxy), ←sub_mul,
        abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (Real.rpow_nonneg hs.le _))]
      have hw0 := mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hxy))
      nlinarith
    · have hxle : x  ≤  s := le_of_not_ge hxs
      have hsy : s  ≤  y := le_of_not_ge hy
      have hh := hbelow hx hxle le_rfl
      rw [min_self, min_eq_left hxle] at hh
      have he : y*s^w - x*x^w = (y-s)*s^w+(s*s^w-x*x^w) := by ring
      rw [min_eq_right hsy, min_eq_left hxle,he]
      calc
        |(y-s)*s^w+(s*s^w-x*x^w)|  ≤  |(y-s)*s^w|+|s*s^w-x*x^w| := abs_add_le _ _
        _  ≤  (y-s)*s^w+(1+w)*s^w*(s-x) := by
          rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hsy) (Real.rpow_nonneg hs.le _))]
          exact add_le_add_right hh _
        _  ≤  (1+w)*s^w*(y-x) := by
          have hw0 := mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hsy))
          nlinarith
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm,abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [neg_sub] using hordered hu huv
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hordered hv hvu
end NeutralAtom

end
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace NeutralAtom

theorem continuous_packetWidth (c₁ r₀ s : ℝ) : Continuous (packetWidth c₁ r₀ s) := by
  unfold packetWidth
  fun_prop (disch := norm_num [packetExponent])

theorem packetWidth_lipschitz {c r₀ s : ℝ} (hc : 0 ≤ c)
    (hr : 0 < r₀) (hs : 0 < s) (z z' : Position) :
    |packetWidth c r₀ s z-packetWidth c r₀ s z'| ≤
      (c*(1+packetExponent)*s^packetExponent)*‖z-z'‖ := by
  have h := clamped_width_scalar_lipschitz (w := packetExponent) (u := max ‖z‖ r₀) (v := max ‖z'‖ r₀) (by norm_num [packetExponent]) hs
    (hr.trans_le (le_max_right _ _)) (hr.trans_le (le_max_right _ _))
  have hm : |max ‖z‖ r₀-max ‖z'‖ r₀| ≤ ‖z-z'‖ := by
    calc
      _ ≤ max |‖z‖-‖z'‖| |r₀-r₀| := abs_max_sub_max_le_max _ _ _ _
      _ = |‖z‖-‖z'‖| := by simp
      _ ≤ ‖z-z'‖ := abs_norm_sub_norm_le _ _
  unfold packetWidth
  rw [show c*max ‖z‖ r₀*(min (max ‖z‖ r₀) s)^packetExponent-
      c*max ‖z'‖ r₀*(min (max ‖z'‖ r₀) s)^packetExponent =
      c*(max ‖z‖ r₀*(min (max ‖z‖ r₀) s)^packetExponent-
      max ‖z'‖ r₀*(min (max ‖z'‖ r₀) s)^packetExponent) by ring,
    abs_mul,abs_of_nonneg hc]
  calc
    _ ≤ c*((1+packetExponent)*s^packetExponent*|max ‖z‖ r₀-max ‖z'‖ r₀|) :=
      mul_le_mul_of_nonneg_left h hc
    _ ≤ (c*(1+packetExponent)*s^packetExponent)*‖z-z'‖ := by
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ c*(1+packetExponent)*s^packetExponent from
          mul_nonneg (mul_nonneg hc (by norm_num [packetExponent])) (Real.rpow_nonneg hs.le _))
      simpa only [mul_assoc] using hh

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_MasterKernel
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem master_kernel_estimates (g : 𝓢(Position,ℝ))
    (hg : ∀ x, 1 < ‖x‖ → g x=0) (hm : (∫ x, g x^2)=1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ y : Position,
      (∀ z, packetKernel g c r₀ s z y≠0 → ‖y-z‖ ≤ 2*packetWidth c r₀ s y) ∧
      (∀ z, |packetKernel g c r₀ s z y| ≤ C/(packetWidth c r₀ s y)^3) ∧
      (∀ z z', |packetKernel g c r₀ s z y-packetKernel g c r₀ s z' y| ≤
        (C/(packetWidth c r₀ s y)^4)*‖z-z'‖) ∧
      Integrable (fun z => packetKernel g c r₀ s z y) ∧
      |(∫ z, packetKernel g c r₀ s z y)-1| ≤
        C*(c*(1+packetExponent)*s^packetExponent) := by
  obtain ⟨B,L,hB,hL,hφ,hφL⟩ := schwartz_square_bounded_lipschitz g
  let A := 8*B
  let D := 64*B+80*L
  let M := (64*Real.pi/3)*(48*B+64*L)
  let C := 1+A+D+M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hMC : M ≤ C := by dsimp [C]; linarith
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro c r₀ s hc hr hs hsmall y
  let t := packetWidth c r₀ s
  let q := c*(1+packetExponent)*s^packetExponent
  have ht : ∀ z, 0 < t z := packetWidth_pos hc hr hs
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (mul_nonneg hc.le (by norm_num [packetExponent]))
      (Real.rpow_nonneg hs.le _)
  have hlip : ∀ z z', |t z-t z'| ≤ q*‖z-z'‖ := packetWidth_lipschitz hc.le hr hs
  have hlip' : ∀ z z', |t z-t z'| ≤ ‖z-z'‖/4 := by
    intro z z'
    calc
      _ ≤ q*‖z-z'‖ := hlip z z'
      _ ≤ (1/4)*‖z-z'‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ = _ := by ring
  have hφs : ∀ x, 1 < ‖x‖ → (fun z => g z^2) x=0 := by
    intro x hx; simp only [hg x hx,zero_pow (by decide : (2:ℕ)≠0)]
  have he (z : Position) : packetKernel g c r₀ s z y=scaledCenterKernel (fun z => g z^2) t z y := rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro z hK
    rw [he] at hK
    have hh := (scaledCenterKernel_support_width _ t hφs ht hlip' z y hK).2
    linarith [ht y]
  · intro z
    rw [he]
    exact (scaledCenterKernel_uniform_bound _ t hB hφs hφ ht hlip' z y).trans
      (div_le_div_of_nonneg_right hAC (pow_nonneg (ht y).le _))
  · intro z z'
    rw [he,he]
    exact (scaledCenterKernel_center_lipschitz _ t hB hL hφs hφ hφL ht hlip' z z' y).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hDC (pow_nonneg (ht y).le _)) (norm_nonneg _))
  · exact integrable_scaledCenterKernel (g.continuous.pow 2) (continuous_packetWidth c r₀ s) ht hφs hlip' y
  · have hh := center_kernel_mass_defect hB hL hq hsmall (g.continuous.pow 2)
      (continuous_packetWidth c r₀ s) ht hφs hφ hφL hlip y
    change |(∫ z, packetKernel g c r₀ s z y)-(∫ z, g z^2)| ≤ M*q at hh
    rw [hm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hMC hq)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_MasterKernelDuality
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem master_kernel_coulomb_duality (g : 𝓢(Position,ℝ))
    (hg : ∀ x, 1<‖x‖ → g x=0) (hm : (∫ x, g x^2)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ (y : Position) {Ω : Set Coulomb.Space} (_ : MeasurableSet Ω)
      [IsFiniteMeasure (volume.restrict Ω)] (σ : Coulomb.Space → ℝ),
    MemLp σ Coulomb.TFExponent (volume.restrict Ω) →
    (∀ z∉Ω, σ z=0) → Metric.closedBall y (4*packetWidth c r₀ s y)⊆Ω →
    (∫ z, σ z*packetKernel g c r₀ s z y)^2≤
      (C/(packetWidth c r₀ s y)^5)*Coulomb.coulombBilinear σ σ := by
  obtain ⟨B,hB,H⟩ := master_kernel_estimates g hg hm
  refine ⟨64*B^2,by positivity,?_⟩
  intro c r₀ s hc hr hs hq y Ω hΩ _ σ hσ hσs hball
  obtain ⟨hsp,hamp,hL,_,_⟩ := H hc hr hs hq y
  let t := packetWidth c r₀ s y
  have ht : 0<t := packetWidth_pos hc hr hs y
  have hK : ∀ z, 2*t<‖z-y‖ → packetKernel g c r₀ s z y=0 := by
    intro z hz
    by_contra hn
    have hh := hsp z hn
    rw [norm_sub_rev] at hh
    linarith
  have HH := Coulomb.raw_coulomb_lipschitz_test hΩ hσ hσs
    (show 0≤B/t^4 by positivity) (show 0<2*t by positivity) y hamp hK hL
    (by simpa only [t,show (2:ℝ)*(2*t)=4*t by ring] using hball)
  have he : (4*Real.pi)⁻¹*(3*(volume (Metric.closedBall y (2*(2*t)))).toReal*(B/t^4)^2)=
      (64*B^2)/t^5 := by
    rw [←Measure.real,Coulomb.volume_closedBall_three y (by positivity)]
    field_simp [ht.ne',Real.pi_ne_zero]
    ring
  rw [he,mul_comm] at HH
  exact HH

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PatchKernelDuality
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace Coulomb

theorem master_kernel_patch_gap (g : 𝓢(NeutralAtom.Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z, g z^2)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent≤1/4 →
    ∀ {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
      {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
      (hn : ∀ j, 20*a≤‖S.position j-y‖),
    4*NeutralAtom.packetWidth c r₀ s y<t-4*b →
    ∀ (spin : Spins m) (x : Configuration m),
      (∫ z, (retainedFineDensity b (patchRetained y t b x) (position x) z-
        localTFDensity measurableSet_ball (coreTFField S (u.coreSlice spin x).normalized
          measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn)) z)*
            NeutralAtom.packetKernel g c r₀ s z y)^2≤
      (C/(NeutralAtom.packetWidth c r₀ s y)^5)*patchSliceTFGap S u ha hb ht y hn spin x := by
  obtain ⟨C,hC,H⟩ := NeutralAtom.master_kernel_coulomb_duality g hg hm
  refine ⟨2*C,by positivity,?_⟩
  intro c r₀ s hc hr hs hq J m k S u a b t ha hb ht y hn hball spin x
  let Ω := Metric.ball y (t-4*b)
  let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
    (patch_nucleus_separation S ha hb ht y hn)
  let ρ := localTFDensity measurableSet_ball W
  let σ := retainedFineDensity b (patchRetained y t b x) (position x)
  have hσ : MemLp σ TFExponent (volume.restrict Ω) := retainedFineDensity_memLp hb _ _
  have hρ : MemLp ρ TFExponent volume := tfDensity_memLp measurableSet_ball
    (localTFMinimizer_nonneg measurableSet_ball W)
  have hσs : ∀ z∉Ω, σ z=0 := retainedFineDensity_patch_support hb y t x
  have hρs : ∀ z∉Ω, ρ z=0 := fun z hz => tfDensity_eq_zero _ hz
  have hd := hσ.sub (hρ.restrict (s := Ω))
  have hds : ∀ z∉Ω, σ z-ρ z=0 := fun z hz => by rw [hσs z hz,hρs z hz,sub_self]
  have HH := H hc hr hs hq y measurableSet_ball (fun z => σ z-ρ z) hd hds
    (fun z hz => show z∈Ω from (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hball)))
  have Hgap := rawTF_gap_coulomb measurableSet_ball
    (coreScreenedField S (u.coreSlice spin x).normalized) W
    (coreTFField_coe S _ measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn)) hσ
    (Eventually.of_forall (fun z => retainedFineDensity_nonneg b _ _ z)) hσs
  have Hmul := mul_le_mul_of_nonneg_left Hgap
    (show 0≤C/(NeutralAtom.packetWidth c r₀ s y)^5 by
      have hw := NeutralAtom.packetWidth_pos hc hr hs y
      positivity)
  apply HH.trans
  convert Hmul using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [σ,ρ,W,patchSliceTFGap]
  ring

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace Coulomb

lemma fineKernel_test_integrable {b B : ℝ} (hb : 0<b) (K : Space → ℝ)
    (hKm : Measurable K) (hB : ∀ z, |K z|≤B) (w : Space) :
    Integrable (fun z => fineKernel b (z-w)*K z) :=
  (fineKernel_shift_integrable hb w).mul_bdd hKm.aestronglyMeasurable
    (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB z))

lemma fineKernel_test_matching {b A B : ℝ} (hb : 0<b) (hA : 0≤A)
    (K : Space → ℝ) (hKm : Measurable K) (hB : ∀ z, |K z|≤B)
    (hL : ∀ z v, |K z-K v|≤A*‖z-v‖) (w : Space) :
    |(∫ z, fineKernel b (z-w)*K z)-K w|≤A*(2*b) := by
  have hi := fineKernel_test_integrable hb K hKm hB w
  have hc := (fineKernel_shift_integrable hb w).mul_const (K w)
  have he : (∫ z, fineKernel b (z-w)*K z)-K w =
      ∫ z, fineKernel b (z-w)*(K z-K w) := by
    rw [show (fun z => fineKernel b (z-w)*(K z-K w))=
      (fun z => fineKernel b (z-w)*K z-fineKernel b (z-w)*K w) by funext z; ring,
      integral_sub hi hc,integral_mul_const,fineKernel_shift_integral hb,one_mul]
  rw [he]
  calc
    _≤∫ z, |fineKernel b (z-w)*(K z-K w)| := abs_integral_le_integral_abs
    _≤∫ z, fineKernel b (z-w)*(A*(2*b)) := by
      apply integral_mono
      · simpa only [Pi.sub_apply,Real.norm_eq_abs,mul_sub] using (hi.sub hc).norm
      · exact (fineKernel_shift_integrable hb w).mul_const _
      · intro z
        dsimp only
        rw [abs_mul,abs_of_nonneg (fineKernel_nonneg ..)]
        by_cases hz : fineKernel b (z-w)=0
        · simp only [hz,zero_mul,le_refl]
        · have hs : ‖z-w‖≤2*b := le_of_not_gt (fun hh => hz (fineKernel_eq_zero_of_two_mul_lt hb _ hh))
          exact mul_le_mul_of_nonneg_left ((hL z w).trans (mul_le_mul_of_nonneg_left hs hA)) (fineKernel_nonneg ..)
    _=A*(2*b) := by rw [integral_mul_const,fineKernel_shift_integral hb,one_mul]

lemma fineKernel_test_zero_far {b R : ℝ} (hb : 0<b) (K : Space → ℝ) (y w : Space)
    (hs : ∀ z, R<‖z-y‖ → K z=0) (hw : R+2*b<‖w-y‖) :
    (∫ z, fineKernel b (z-w)*K z)=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  change fineKernel b (z-w)*K z=0
  by_cases hz : fineKernel b (z-w)=0
  · simp only [hz,zero_mul]
  have hn : ‖z-w‖≤2*b := le_of_not_gt (fun hh => hz (fineKernel_eq_zero_of_two_mul_lt hb _ hh))
  have htri := norm_sub_le_norm_sub_add_norm_sub w z y
  rw [norm_sub_rev w z] at htri
  rw [hs z (by linarith),mul_zero]

theorem patchFine_kernel_matching {n : ℕ} {b t R A B : ℝ} (hb : 0<b) (hA : 0≤A)
    (hretain : R+2*b<t-7*b) (K : Space → ℝ) (hKm : Measurable K)
    (hB : ∀ z, |K z|≤B) (y : Space)
    (hs : ∀ z, R<‖z-y‖ → K z=0)
    (hL : ∀ z v, |K z-K v|≤A*‖z-v‖) (x : Configuration n) :
    |(∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*K z)-
      ∑ i, K (position x i)| ≤
      (A*(2*b))*localCount (Metric.closedBall y (R+2*b)) x := by
  let r := patchRetained y t b x
  have hsum : (∑ i, K (position x i))=∑ i∈r, K (position x i) := by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    apply hs
    by_contra hh
    apply hi
    apply (patchRetained_mem ..).mpr
    have hn : ‖position x i-y‖≤R := le_of_not_gt hh
    linarith
  simp only [retainedFineDensity,Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => fineKernel_test_integrable hb K hKm hB _),hsum,←Finset.sum_sub_distrib]
  calc
    _≤∑ i∈r, |(∫ z, fineKernel b (z-position x i)*K z)-K (position x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ i∈r, (A*(2*b))*(Metric.closedBall y (R+2*b)).indicator (fun _ => (1:ℝ)) (position x i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : position x i ∈ Metric.closedBall y (R+2*b)
      · rw [indicator_of_mem hi,mul_one]
        exact fineKernel_test_matching hb hA K hKm hB hL _
      · rw [indicator_of_notMem hi,mul_zero]
        have hn : R+2*b<‖position x i-y‖ := by
          simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hi
        rw [fineKernel_test_zero_far hb K y _ hs hn,hs _ (by linarith),sub_self,abs_zero]
    _≤∑ i, (A*(2*b))*(Metric.closedBall y (R+2*b)).indicator (fun _ => (1:ℝ)) (position x i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => by norm_num) _)
    _=(A*(2*b))*localCount (Metric.closedBall y (R+2*b)) x := by
      rw [localCount,Finset.mul_sum]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalDensity
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace NeutralAtom

theorem continuous_packetKernel {g : Position → ℝ} (hg : Continuous g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    Continuous (fun zy : Position × Position => packetKernel g c₁ r₀ s zy.1 zy.2) := by
  have ht : Continuous (fun zy : Position × Position => packetWidth c₁ r₀ s zy.1) :=
    (continuous_packetWidth c₁ r₀ s).comp continuous_fst
  have htne : ∀ zy : Position × Position, packetWidth c₁ r₀ s zy.1 ≠ 0 :=
    fun zy => (packetWidth_pos hc hr hs zy.1).ne'
  unfold packetKernel
  exact ((ht.pow 3).inv₀ (fun zy => pow_ne_zero _ (htne zy))).mul
    ((hg.comp ((ht.inv₀ htne).smul (continuous_snd.sub continuous_fst))).pow 2)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace Coulomb

lemma tfScalarDensity_nonneg (v : ℝ) : 0≤tfScalarDensity v := by
  unfold tfScalarDensity
  have hc := thomasFermiKineticConstant_pos
  positivity

lemma tfScalarDensity_mono : Monotone tfScalarDensity := by
  intro v w hvw
  have hc := thomasFermiKineticConstant_pos
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  apply div_le_div_of_nonneg_right (max_le_max_right 0 hvw)
  exact mul_nonneg thomasFermiKineticConstant_pos.le (by norm_num)

lemma localTFDensity_euler {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W=ᵐ[volume.restrict Ω] Φ) :
    ∀ᵐ x, x∈Ω → localTFDensity hΩ W x=
      tfScalarDensity (Φ x-tfPotential (localTFMinimizer hΩ W) x) := by
  have HE := tfEuler_equation hΩ thomasFermiKineticConstant_pos W
    (localTFMinimizer_nonneg hΩ W) (fun f hf => localTFMinimizer_minimizes hΩ W hf)
  filter_upwards [(ae_restrict_iff' hΩ).mp HE,(ae_restrict_iff' hΩ).mp hW,
    tfDensity_ae_tfExtend hΩ (localTFMinimizer_nonneg hΩ W)] with x he hw hd
  intro hx
  change tfDensity Ω (localTFMinimizer hΩ W) x=_
  rw [hd,tfExtend,indicator_of_mem hx,(he hx).1,hw hx]
  rfl

lemma localTFDensity_test_enclosure {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W=ᵐ[volume.restrict Ω] Φ)
    (χ : Space → ℝ) (hχm : Measurable χ) (hχi : Integrable χ)
    (hχp : ∀ x, 0≤χ x) (B : ℝ) (hB : ∀ x, |χ x|≤B)
    (hs : ∀ x, χ x≠0 → x∈Ω) (u d : ℝ)
    (hosc : ∀ x, χ x≠0 → |(Φ x-tfPotential (localTFMinimizer hΩ W) x)-u|≤d) :
    tfScalarDensity (u-d)*(∫ x, χ x)≤∫ x, localTFDensity hΩ W x*χ x ∧
    (∫ x, localTFDensity hΩ W x*χ x)≤tfScalarDensity (u+d)*(∫ x, χ x) := by
  have hρi : Integrable (localTFDensity hΩ W) :=
    (tfExtend_integrable hΩ (localTFMinimizer hΩ W)).congr
      (tfDensity_ae_tfExtend hΩ (localTFMinimizer_nonneg hΩ W)).symm
  have hi : Integrable (fun x => localTFDensity hΩ W x*χ x) :=
    hρi.mul_bdd hχm.aestronglyMeasurable (Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hB x))
  have H := localTFDensity_euler hΩ Φ W hW
  have hh : ∀ᵐ x, tfScalarDensity (u-d)*χ x≤localTFDensity hΩ W x*χ x ∧
      localTFDensity hΩ W x*χ x≤tfScalarDensity (u+d)*χ x := by
    filter_upwards [H] with x hx
    by_cases hz : χ x=0
    · simp [hz]
    rw [hx (hs x hz)]
    have hr := abs_le.mp (hosc x hz)
    exact ⟨mul_le_mul_of_nonneg_right (tfScalarDensity_mono (by linarith : u-d≤_)) (hχp x),
      mul_le_mul_of_nonneg_right (tfScalarDensity_mono (by linarith : _≤u+d)) (hχp x)⟩
  have hl := integral_mono_ae (hχi.const_mul _) hi (hh.mono (fun _ h => h.1))
  have hu := integral_mono_ae hi (hχi.const_mul _) (hh.mono (fun _ h => h.2))
  simpa only [integral_const_mul] using And.intro hl hu

theorem exists_patch_tested_reaction_enclosure :
    ∃ C : ℝ, 0<C ∧ ∀ {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space),
    SpatiallySupported u {z | t≤‖z-y‖} →
    ∀ (hn : ∀ j, 20*a≤‖S.position j-y‖), 0 ≤ r → r≤a →
    ∀ (χ : Space → ℝ), Measurable χ → Integrable χ →
    (∀ z, 0≤χ z) → ∀ B : ℝ, (∀ z, |χ z|≤B) →
    (∀ z, χ z≠0 → ‖z-y‖ ≤ r) →
    let W := coreTFField S u measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn)
    let v := patchTFScreenedField S u ha hb ht.2 y hn y
    let d := C*(r/a)*((a^4)⁻¹+max (-v) 0)
    tfScalarDensity (v-d)*(∫ z, χ z)≤∫ z, localTFDensity measurableSet_ball W z*χ z ∧
    (∫ z, localTFDensity measurableSet_ball W z*χ z)≤tfScalarDensity (v+d)*(∫ z, χ z) := by
  obtain ⟨C,hC,H⟩ := exists_patch_TF_oscillation
  refine ⟨C,hC,?_⟩
  intro J k S u a b t r ha hb hsmall ht y hu hn hr hra χ hχm hχi hχp B hB hs
  dsimp only
  apply localTFDensity_test_enclosure measurableSet_ball (coreScreenedField S u) _
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    χ hχm hχi hχp B hB
  · intro z hz
    have HZ := hs z hz
    rw [Metric.mem_ball,dist_eq_norm]
    linarith [ht.1]
  · intro z hz
    have hz' : z∈Metric.closedBall y a := by
      rw [Metric.mem_closedBall,dist_eq_norm]
      exact (hs z hz).trans hra
    have hh := H S u ha hb hsmall ht y hu hn z hz'
    rw [Real.norm_eq_abs] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hs z hz) ha.le) hC.le

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PatchPacketResponse
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace Coulomb

theorem master_kernel_patch_response (g : 𝓢(NeutralAtom.Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z, g z^2)=1) :
    ∃ C D E : ℝ, 0<C ∧ 0<D ∧ 0<E ∧
    ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent≤1/4 →
    ∀ {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
      {a b t : ℝ} (ha : 0<a) (hb : 0<b) (_ : 18*b≤a)
      (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
      (hn : ∀ j, 20*a≤‖S.position j-y‖),
    2*NeutralAtom.packetWidth c r₀ s y≤a →
    4*NeutralAtom.packetWidth c r₀ s y<t-4*b →
    ∀ (spin : Spins m) (x : Configuration m),
    SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖} →
    let w := NeutralAtom.packetWidth c r₀ s y
    let χ := fun z => NeutralAtom.packetKernel g c r₀ s z y
    let v := patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y
    let d := C*(2*w/a)*((a^4)⁻¹+max (-v) 0)
    let e := Real.sqrt ((D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x)
    let I := ∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*χ z
    tfScalarDensity (v-d)*(∫ z, χ z)-e≤I ∧
    I≤tfScalarDensity (v+d)*(∫ z, χ z)+e ∧
    |(∫ z, χ z)-1|≤E*(c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent) := by
  obtain ⟨C,hC,HC⟩ := exists_patch_tested_reaction_enclosure
  obtain ⟨D,hD,HD⟩ := master_kernel_patch_gap g hg hm
  obtain ⟨E,hE,HE⟩ := NeutralAtom.master_kernel_estimates g hg hm
  refine ⟨C,D,E,hC,hD,hE,?_⟩
  intro c r₀ s hc hr hs hq J m k S u a b t ha hb hsmall ht y hn hw hball spin x hcs
  let w := NeutralAtom.packetWidth c r₀ s y
  let χ := fun z => NeutralAtom.packetKernel g c r₀ s z y
  let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
    (patch_nucleus_separation S ha hb ht.2 y hn)
  let ρ := localTFDensity measurableSet_ball W
  let σ := retainedFineDensity b (patchRetained y t b x) (position x)
  have hwp : 0<w := NeutralAtom.packetWidth_pos hc hr hs y
  obtain ⟨hsp,hamp,_,hχi,hχmass⟩ := HE hc hr hs hq y
  have hχm : Measurable χ := (((NeutralAtom.continuous_packetKernel g.continuous hc hr hs).comp
    (continuous_id.prodMk (continuous_const (y := y)))).measurable)
  have Hresponse := HC S (u.coreSlice spin x).normalized ha hb hsmall ht y hcs hn
    (show 0≤2*w by positivity) hw χ hχm hχi
    (fun z => NeutralAtom.packetKernel_nonneg g hc hr hs z y) (E/w^3) hamp
    (fun z hz => by simpa only [norm_sub_rev] using hsp z hz)
  have Hdual := HD hc hr hs hq S u ha hb ht.2 y hn hball spin x
  have hρi : Integrable ρ := (tfExtend_integrable measurableSet_ball (localTFMinimizer measurableSet_ball W)).congr
    (tfDensity_ae_tfExtend measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)).symm
  have htestρ : Integrable (fun z => ρ z*χ z) := hρi.mul_bdd hχm.aestronglyMeasurable
    (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hamp z))
  have htestσ : Integrable (fun z => σ z*χ z) :=
    (retainedFineDensity_integrable hb _ _).mul_bdd hχm.aestronglyMeasurable
      (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hamp z))
  have heq : (∫ z, (σ z-ρ z)*χ z)=(∫ z, σ z*χ z)-(∫ z, ρ z*χ z) := by
    simp_rw [sub_mul]
    rw [integral_sub htestσ htestρ]
  change (∫ z, (σ z-ρ z)*χ z)^2≤(D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x at Hdual
  rw [heq] at Hdual
  have hpos : 0≤(D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x :=
    mul_nonneg (by positivity) (patchSliceTFGap_nonneg S u ha hb ht.2 y hn spin x)
  have Habs : |(∫ z, σ z*χ z)-(∫ z, ρ z*χ z)|≤
      Real.sqrt ((D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt hpos]
    exact Hdual
  have HH := abs_le.mp Habs
  dsimp only at Hresponse ⊢
  refine ⟨?_,?_,hχmass⟩ <;> dsimp only [ρ,W,σ,χ,w] at Hresponse HH ⊢ <;> linarith [Hresponse.1,Hresponse.2]

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace Coulomb

theorem master_kernel_patch_array_response (g : 𝓢(NeutralAtom.Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z, g z^2)=1) :
    ∃ C D E F : ℝ, 0<C ∧ 0<D ∧ 0<E ∧ 0<F ∧
    ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent≤1/4 →
    ∀ {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
      {a b t : ℝ} (ha : 0<a) (hb : 0<b) (_ : 18*b≤a)
      (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
      (hn : ∀ j, 20*a≤‖S.position j-y‖),
    2*NeutralAtom.packetWidth c r₀ s y≤a →
    ∀ (spin : Spins m) (x : Configuration m),
    SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖} →
    let w := NeutralAtom.packetWidth c r₀ s y
    let χ := fun z => NeutralAtom.packetKernel g c r₀ s z y
    let v := patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y
    let d := C*(2*w/a)*((a^4)⁻¹+max (-v) 0)
    let e := Real.sqrt ((D/w^5)*patchSliceTFGap S u ha hb ht.2 y hn spin x)+
      (F/w^4*(2*b))*localCount (Metric.closedBall y (2*w+2*b)) x
    tfScalarDensity (v-d)*(∫ z, χ z)-e≤∑ i, χ (position x i) ∧
    (∑ i, χ (position x i))≤tfScalarDensity (v+d)*(∫ z, χ z)+e ∧
    |(∫ z, χ z)-1|≤E*(c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent) := by
  obtain ⟨C,D,E,hC,hD,hE,H⟩ := master_kernel_patch_response g hg hm
  obtain ⟨F,hF,HF⟩ := NeutralAtom.master_kernel_estimates g hg hm
  refine ⟨C,D,E,F,hC,hD,hE,hF,?_⟩
  intro c r₀ s hc hr hs hq J m k S u a b t ha hb hsmall ht y hn hw spin x hcs
  let w := NeutralAtom.packetWidth c r₀ s y
  let χ := fun z => NeutralAtom.packetKernel g c r₀ s z y
  have hpw : 0<w := NeutralAtom.packetWidth_pos hc hr hs y
  have hball : 4*w<t-4*b := by dsimp only [w]; linarith [ht.1]
  have HH := H hc hr hs hq S u ha hb hsmall ht y hn hw hball spin x hcs
  obtain ⟨hsp,hamp,hL,_,_⟩ := HF hc hr hs hq y
  have hχm : Measurable χ := (((NeutralAtom.continuous_packetKernel g.continuous hc hr hs).comp
    (continuous_id.prodMk (continuous_const (y := y)))).measurable)
  have hmatch := patchFine_kernel_matching hb (show 0≤F/w^4 by positivity)
    (show 2*w+2*b<t-7*b by dsimp only [w]; linarith [ht.1]) χ hχm hamp y
    (fun z hz => by by_contra hn; have HH := hsp z hn; rw [norm_sub_rev] at HH; linarith)
    hL x
  have habs := abs_le.mp hmatch
  dsimp only at HH ⊢
  refine ⟨?_,?_,HH.2.2⟩ <;> dsimp only [χ,w] at habs ⊢ <;> linarith [HH.1,HH.2.1]

lemma shifted_negative_feedback_mono {θ A : ℝ} (_ : 0≤θ) (hθ1 : θ≤1) :
    Monotone (fun v : ℝ => v+θ*(A+max (-v) 0)) := by
  intro v w hvw
  change v+θ*(A+max (-v) 0)≤w+θ*(A+max (-w) 0)
  by_cases hv : 0≤v
  · have hw : 0≤w := hv.trans hvw
    rw [max_eq_right (by linarith : -v≤0),max_eq_right (by linarith : -w≤0)]
    linarith
  · by_cases hw : 0≤w
    · rw [max_eq_left (by linarith : 0≤-v),max_eq_right (by linarith : -w≤0)]
      nlinarith [mul_le_mul_of_nonneg_right hθ1 (show 0≤-v by linarith)]
    · rw [max_eq_left (by linarith : 0≤-v),max_eq_left (by linarith : 0≤-w)]
      nlinarith [mul_nonneg (show 0≤1-θ by linarith) (show 0≤w-v by linarith)]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_SignAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution

open scoped BigOperators

instance observationNoiseLaw_negInvariant : observationNoiseLaw.IsNegInvariant := by
  constructor
  ext s hs
  change (Measure.map (fun u : ℝ => -u) observationNoiseLaw) s = observationNoiseLaw s
  rw [Measure.map_apply measurable_neg hs]
  unfold observationNoiseLaw
  rw [withDensity_apply _ (measurable_neg hs), withDensity_apply _ hs,
    ← lintegral_indicator (measurable_neg hs), ← lintegral_indicator hs]
  have h := lintegral_neg_eq_self (μ := (volume : Measure ℝ))
    (s.indicator (fun u => ENNReal.ofReal (observationNoiseDensity u)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext u
  classical
  by_cases hu : -u ∈ s <;> simp [hu, observationNoiseDensity_even]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationProductDensity
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators

open scoped Convolution

theorem observationProductDensity_nonneg {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    0 ≤ observationProductDensity u :=
  Finset.prod_nonneg (fun _i _ => observationNoiseDensity_nonneg _)

theorem observationProductDensity_contDiff {ι : Type*} [Fintype ι] :
    ContDiff ℝ ∞ (@observationProductDensity ι _) := by
  unfold observationProductDensity
  have h := observationNoiseDensity_contDiff
  fun_prop

theorem observationProductDensity_integrable {ι : Type*} [Fintype ι] :
    Integrable (@observationProductDensity ι _) :=
  Integrable.fintype_prod (fun _ => observationNoiseDensity_integrable)

theorem observationProductDensity_even {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    observationProductDensity (-u) = observationProductDensity u := by
  simp [observationProductDensity, observationNoiseDensity_even]

theorem observationNoiseLaw_pi_density {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι => observationNoiseLaw) =
      volume.withDensity (fun u : ι → ℝ => ENNReal.ofReal (observationProductDensity u)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal observationProductDensity_integrable.integrableOn
      (Filter.Eventually.of_forall observationProductDensity_nonneg)]
  change ENNReal.ofReal (∫ u : ι → ℝ in Set.univ.pi s,
    ∏ i, observationNoiseDensity (u i) ∂Measure.pi (fun _ => volume)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [observationNoiseLaw, withDensity_apply _ (hs i),
      ← ofReal_integral_eq_lintegral_ofReal observationNoiseDensity_integrable.integrableOn
        (Filter.Eventually.of_forall observationNoiseDensity_nonneg)]
  · intro i _
    exact integral_nonneg observationNoiseDensity_nonneg

theorem observationNoiseLaw_pi_integral {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) :
    (∫ u, f u ∂Measure.pi (fun _ : ι => observationNoiseLaw)) =
      ∫ u, observationProductDensity u * f u := by
  rw [observationNoiseLaw_pi_density, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (observationProductDensity_nonneg _), smul_eq_mul]
  · exact observationProductDensity_contDiff.continuous.measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

theorem observationEventLikelihood_integral {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (z : ι → ℝ) :
    observationEventLikelihood s z =
      ∫ u, s.indicator (fun _ => (1:ℝ)) (z+u)
        ∂Measure.pi (fun _ : ι => observationNoiseLaw) := by
  rw [observationEventLikelihood, convolution_def, observationNoiseLaw_pi_integral,
    ← integral_add_left_eq_self (fun y : ι → ℝ =>
      (ContinuousLinearMap.mul ℝ ℝ) (s.indicator (fun _ => (1:ℝ)) y)
        (observationProductDensity (z-y))) z]
  apply integral_congr_ae
  filter_upwards with u
  simp only [ContinuousLinearMap.mul_apply', show z-(z+u) = -u by abel,
    observationProductDensity_even]
  ring

theorem observationEventLikelihood_probability {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    observationEventLikelihood s z =
      (Measure.pi (fun _ : ι => observationNoiseLaw)).real ((fun u => z+u) ⁻¹' s) := by
  rw [observationEventLikelihood_integral]
  have he : (fun u => s.indicator (fun _ => (1:ℝ)) (z+u)) =
      ((fun u => z+u) ⁻¹' s).indicator (fun _ => (1:ℝ)) := by
    ext u
    exact (Set.indicator_comp_right (fun u : ι → ℝ => z+u)).symm
  rw [he]
  have ht : MeasurableSet ((fun u : ι → ℝ => z+u) ⁻¹' s) := hs.preimage (by fun_prop)
  rw [integral_indicator ht, setIntegral_const, smul_eq_mul, mul_one]

theorem observationEventLikelihood_nonneg {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    0 ≤ observationEventLikelihood s z := by
  rw [observationEventLikelihood_probability hs]
  exact measureReal_nonneg

theorem arrayEventLikelihood_nonneg {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration n) : 0 ≤ arrayEventLikelihood ℓ s x :=
  observationEventLikelihood_nonneg (hs.preimage (by unfold observationArrayRescale; fun_prop)) _

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationWidthSquareSum
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators
open scoped Convolution

theorem arrayEventLikelihood_integral {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, ℓ h ≠ 0)
    (s : Set ((H × (Fin n × Fin 3)) → ℝ)) (x : Configuration n) :
    arrayEventLikelihood ℓ s x =
      ∫ u, s.indicator (fun _ => (1:ℝ)) (fun hia => x hia.2.1 hia.2.2 + ℓ hia.1 * u hia)
        ∂Measure.pi (fun _ : H × (Fin n × Fin 3) => observationNoiseLaw) := by
  rw [arrayEventLikelihood, observationEventLikelihood_integral]
  apply integral_congr_ae
  filter_upwards with u
  have he : observationArrayRescale ℓ (observationArrayCenter ℓ x + u) =
      (fun hia => x hia.2.1 hia.2.2 + ℓ hia.1 * u hia) := by
    ext hia
    simp [observationArrayRescale, observationArrayCenter, mul_add, hℓ]
  change (observationArrayRescale ℓ ⁻¹' s).indicator
    ((fun _ => (1:ℝ)) ∘ observationArrayRescale ℓ) (observationArrayCenter ℓ x + u) = _
  rw [Set.indicator_comp_right, he]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationMatching
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

lemma observationProductDensity_ne_zero_support {I : Type*} [Fintype I]
    {u : I → ℝ} (hu : observationProductDensity u≠0) (i : I) : |u i|<1 := by
  have hi : observationNoiseDensity (u i)≠0 := fun h => hu (Finset.prod_eq_zero (Finset.mem_univ i) h)
  by_contra h
  apply hi
  rw [observationNoiseDensity_formula,ite_eq_right h,mul_zero]

lemma arrayEventLikelihood_pos_matching {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, ℓ h≠0)
    (s : Set ((H × (Fin n × Fin 3)) → ℝ)) (x : Configuration n)
    (hp : 0 < arrayEventLikelihood ℓ s x) :
    ∃ u : (H × (Fin n × Fin 3)) → ℝ, (∀ ia, |u ia|<1) ∧
      (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia)∈s := by
  by_contra hn
  push Not at hn
  have he : arrayEventLikelihood ℓ s x=0 := by
    rw [arrayEventLikelihood_integral ℓ hℓ,observationNoiseLaw_pi_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    by_cases hu : observationProductDensity u=0
    · simp [hu]
    · simp [Set.indicator_of_notMem (hn u (observationProductDensity_ne_zero_support hu))]
  linarith

lemma observationArrayPositions_displacement {H : Type*} {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (x : Configuration n)
    {u : (H × (Fin n × Fin 3)) → ℝ} (hu : ∀ ia, |u ia|<1) (h : H) (i : Fin n) :
    ‖observationArrayPositions h (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia) i-x i‖ ≤
      Real.sqrt 3*ℓ h := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (hℓ h).le)).mp
  rw [EuclideanSpace.real_norm_sq_eq,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  calc
    _ = ∑ a : Fin 3, (ℓ h*u (h,i,a))^2 := by
      apply Finset.sum_congr rfl
      intro a _
      change (x i a+ℓ h*u (h,i,a)-x i a)^2=_
      ring
    _ ≤ ∑ _a : Fin 3, (ℓ h)^2 := Finset.sum_le_sum (fun a _ => by
      have H := (sq_le_sq₀ (abs_nonneg (u (h,i,a))) (by norm_num : (0:ℝ)≤1)).2 (hu (h,i,a)).le
      rw [sq_abs,one_pow] at H
      nlinarith [mul_le_mul_of_nonneg_left H (sq_nonneg (ℓ h))])
    _ = _ := by simp

end NeutralAtom

end
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RecordedStatistic
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma arrayStatistic_measurable {n : ℕ} {χ : Space → ℝ} (hχ : Measurable χ) :
    Measurable (@arrayStatistic n χ) := by
  unfold arrayStatistic
  exact Finset.measurable_fun_sum _ (fun i _ => hχ.comp (continuous_position i).measurable)

lemma arrayStatistic_join {m k : ℕ} (χ : Space → ℝ) (x : Configuration m) (z : Configuration k) :
    arrayStatistic χ (joinConfiguration m k (x,z))=arrayStatistic χ x+arrayStatistic χ z := by
  simp only [arrayStatistic,Fin.sum_univ_add,position_join_left,position_join_right]

lemma arrayStatistic_reindex {m n : ℕ} (χ : Space → ℝ) (e : Fin m ≃ Fin n) (x : Configuration m) :
    arrayStatistic χ (reindexConfiguration e x)=arrayStatistic χ x := by
  change (∑ i : Fin n, χ (position x (e.symm i)))=_
  exact Equiv.sum_comp e.symm (fun i : Fin m => χ (position x i))

lemma arrayStatistic_eq_zero_of_allPositions {n : ℕ} {χ : Space → ℝ} {A : Set Space}
    (hχ : ∀ z∈A, χ z=0) {x : Configuration n} (hx : x∈allPositions A) :
    arrayStatistic χ x=0 := Finset.sum_eq_zero (fun i _ => hχ _ (hx i))

lemma potentialForm_statistic_join_of_support {m k : ℕ} {u : H1Vector k}
    {χ : Space → ℝ} {A : Set Space} (hχ : ∀ z∈A, χ z=0)
    (hu : SpatiallySupported u A) (φ : ℝ → ℝ) (x : Configuration m) :
    potentialForm (fun z => φ (arrayStatistic χ (joinConfiguration m k (x,z)))) u=
      φ (arrayStatistic χ x)*mass u := by
  rw [←potentialForm_const (φ (arrayStatistic χ x)) u]
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [hu s] with z hz
  by_cases h : z∈allPositions A
  · rw [arrayStatistic_join,arrayStatistic_eq_zero_of_allPositions hχ h,add_zero]
  · rw [hz h,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,mul_zero]

lemma sliceExpectation_statistic_eq {m k : ℕ} (u : H1Vector (m+k))
    {χ : Space → ℝ} (hχm : Measurable χ) {A : Set Space} (hχ : ∀ z∈A, χ z=0)
    (hu : PartlySupported u (coreIndexSet m k) A) (φ : ℝ → ℝ)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ q, |φ q|≤B) :
    sliceExpectation u (fun _ x => φ (arrayStatistic χ x))=
      potentialForm (fun x => φ (arrayStatistic χ x)) u := by
  have HH := sliceExpectation_coreConditionalObservable u (fun x => φ (arrayStatistic χ x))
    (hφ.comp (arrayStatistic_measurable hχm)) (fun x => hB _)
  rw [←HH]
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [hu.coreSlice s] with x hx
  by_cases hm : mass (u.coreSlice s x)=0
  · simp only [hm,zero_mul]
  · unfold coreConditionalObservable
    rw [potentialForm_statistic_join_of_support hχ hx.normalized φ x,
      mass_normalized _ (lt_of_le_of_ne (mass_nonneg _) (Ne.symm hm)),mul_one]

lemma RecordedEnsemble.Conserves.statistic {n : ℕ} {T : RecordedEnsemble n}
    {ψ : H1Vector n} (hT : T.Conserves ψ) {χ : Space → ℝ} (hχm : Measurable χ)
    {A : Set Space} (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {B : ℝ} (hB : ∀ q, |φ q|≤B) :
    (∑ p, sliceExpectation (T.vector p) (fun _ x => φ (arrayStatistic χ x)))=
      potentialForm (fun x => φ (arrayStatistic χ x)) ψ := by
  have H := hT (fun x => φ (arrayStatistic χ x)) (hφ.comp (arrayStatistic_measurable hχm)) ⟨B,fun x => hB _⟩
  simp only [Function.comp_def,arrayStatistic_reindex] at H
  rw [←H]
  exact Finset.sum_congr rfl (fun p _ => sliceExpectation_statistic_eq (T.vector p) hχm hχ (hcs p) φ hφ hB)

theorem RecordedEnsemble.Conserves.statistic_event_ae {n : ℕ} {T : RecordedEnsemble n}
    {ψ : H1Vector n} (hT : T.Conserves ψ) {χ : Space → ℝ} (hχm : Measurable χ)
    {A : Set Space} (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    {B : Set ℝ} (hB : MeasurableSet B)
    (hzero : potentialForm (fun x => Bᶜ.indicator (fun _ => (1:ℝ)) (arrayStatistic χ x)) ψ=0) :
    ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 → arrayStatistic χ x∈B := by
  let φ : ℝ → ℝ := Bᶜ.indicator (fun _ => 1)
  have hφ : Measurable φ := measurable_const.indicator hB.compl
  have hφ0 (q : ℝ) : 0≤φ q := indicator_nonneg (fun _ _ => zero_le_one) q
  have hφ1 (q : ℝ) : |φ q|≤1 := by
    dsimp [φ]
    by_cases h : q∈Bᶜ <;> simp [h]
  have HI (p : T.index) (s : Spins (T.out p)) :
      Integrable (fun x => mass ((T.vector p).coreSlice s x)*φ (arrayStatistic χ x)) := by
    have H := (mass_coreSlice_integrable (T.vector p) s).bdd_mul
      (hφ.comp (arrayStatistic_measurable hχm)).aestronglyMeasurable
      (Eventually.of_forall (fun x => (show ‖φ (arrayStatistic χ x)‖≤1 by simpa only [Real.norm_eq_abs] using hφ1 _)))
    exact H.congr (Eventually.of_forall (fun x => mul_comm _ _))
  have H0 (p : T.index) (s : Spins (T.out p)) (x : Configuration (T.out p)) :
      0 ≤ mass ((T.vector p).coreSlice s x)*φ (arrayStatistic χ x) := mul_nonneg (mass_nonneg _) (hφ0 _)
  have H := hT.statistic hχm hχ hcs φ hφ hφ1
  rw [show potentialForm (fun x => φ (arrayStatistic χ x)) ψ=0 from hzero] at H
  have Hs := (Finset.sum_eq_zero_iff_of_nonneg (fun p (_ : p∈Finset.univ) =>
    Finset.sum_nonneg (fun s _ => integral_nonneg (H0 p s)))).mp H
  intro p s
  have Hss := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s∈Finset.univ) =>
    integral_nonneg (H0 p s))).mp (Hs p (Finset.mem_univ _)) s (Finset.mem_univ _)
  have Hae := (integral_eq_zero_iff_of_nonneg (H0 p s) (HI p s)).mp Hss
  filter_upwards [Hae] with x hx
  intro hm
  have hz : φ (arrayStatistic χ x)=0 := (mul_eq_zero.mp hx).resolve_left hm
  by_contra hb
  have he : φ (arrayStatistic χ x)=1 := indicator_of_mem hb _
  linarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

theorem arrayEvent_fresh_statistic_ae {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, ℓ h≠0)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    {χ : Position → ℝ} (hχm : Measurable χ) {A : Set Position}
    (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    {B : Set ℝ} (hB : MeasurableSet B)
    (hmatch : ∀ (x : Configuration n) (z : (H × (Fin n × Fin 3)) → ℝ),
      (∀ ia, |z ia|<1) → (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*z ia)∈E →
      Coulomb.arrayStatistic χ (flattenConfiguration n x)∈B) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Coulomb.arrayStatistic χ x∈B := by
  apply hT.statistic_event_ae hχm hχ hcs hB
  rw [hbayes]
  have hz : stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*
      Bᶜ.indicator (fun _ => (1:ℝ)) (Coulomb.arrayStatistic χ (flattenConfiguration n x)))=0 := by
    unfold stateWeightedIntegral
    apply Finset.sum_eq_zero
    intro s hs
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    by_cases hp : arrayEventLikelihood ℓ E x=0
    · simp [hp]
    · have hpos := lt_of_le_of_ne (arrayEventLikelihood_nonneg ℓ hE x) (Ne.symm hp)
      obtain ⟨z,hz,he⟩ := arrayEventLikelihood_pos_matching ℓ hℓ E x hpos
      have hb := hmatch x z hz he
      simp only [Set.indicator_of_notMem (show Coulomb.arrayStatistic χ (flattenConfiguration n x)∉Bᶜ from not_not.mpr hb),mul_zero,zero_mul]
      rfl
  rw [hz,mul_zero]

end NeutralAtom
namespace Coulomb

theorem arrayStatistic_local_matching {n : ℕ} (χ : Space → ℝ) (x z : Configuration n)
    (y : Space) {r d L : ℝ} (hd : 0≤d) (hL : 0≤L)
    (hs : ∀ v, χ v≠0 → ‖v-y‖ ≤ r)
    (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hmatch : ∀ i, ‖position z i-position x i‖≤d) :
    |arrayStatistic χ z-arrayStatistic χ x|≤
      (L*d)*localCount (Metric.closedBall y (r+d)) x := by
  have Hone (i : Fin n) : |χ (position z i)-χ (position x i)|≤
      (L*d)*(Metric.closedBall y (r+d)).indicator (fun _ => (1:ℝ)) (position x i) := by
    by_cases hx : position x i∈Metric.closedBall y (r+d)
    · rw [indicator_of_mem hx,mul_one]
      exact (hLip _ _).trans (mul_le_mul_of_nonneg_left (hmatch i) hL)
    · rw [indicator_of_notMem hx,mul_zero]
      have hxx : χ (position x i)=0 := by
        by_contra h
        apply hx
        rw [Metric.mem_closedBall,dist_eq_norm]
        exact (hs _ h).trans (by linarith)
      have hzz : χ (position z i)=0 := by
        by_contra h
        apply hx
        rw [Metric.mem_closedBall,dist_eq_norm]
        have ht := norm_sub_le_norm_sub_add_norm_sub (position x i) (position z i) y
        have hh := hmatch i
        rw [norm_sub_rev (position z i) (position x i)] at hh
        linarith [hs _ h]
      simp [hxx,hzz]
  calc
    _ = |∑ i, (χ (position z i)-χ (position x i))| := by rw [Finset.sum_sub_distrib]; rfl
    _ ≤ ∑ i, |χ (position z i)-χ (position x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (L*d)*(Metric.closedBall y (r+d)).indicator (fun _ => (1:ℝ)) (position x i) :=
      Finset.sum_le_sum (fun i _ => Hone i)
    _ = _ := by rw [←Finset.mul_sum]; rfl

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationHigh
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma localCount_ball_matching {n : ℕ} (x z : Configuration n) (y : Space)
    {r d : ℝ} (hmatch : ∀ i, ‖position z i-position x i‖≤d) :
    localCount (Metric.closedBall y r) x≤localCount (Metric.closedBall y (r+d)) z := by
  unfold localCount
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : position x i∈Metric.closedBall y r
  · have hz : position z i∈Metric.closedBall y (r+d) := by
      rw [Metric.mem_closedBall,dist_eq_norm] at hx ⊢
      have ht := norm_sub_le_norm_sub_add_norm_sub (position z i) (position x i) y
      linarith [hmatch i]
    simp only [indicator_of_mem hx,indicator_of_mem hz,le_refl]
  · rw [indicator_of_notMem hx]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

lemma arrayStatistic_matching_observed_count {n : ℕ} (χ : Space → ℝ) (x z : Configuration n)
    (y : Space) {r d L : ℝ} (hd : 0≤d) (hL : 0≤L)
    (hs : ∀ v, χ v≠0 → ‖v-y‖ ≤ r) (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hmatch : ∀ i, ‖position z i-position x i‖≤d) :
    |arrayStatistic χ z-arrayStatistic χ x|≤
      (L*d)*localCount (Metric.closedBall y (r+2*d)) z := by
  have H := arrayStatistic_local_matching χ x z y hd hL hs hLip hmatch
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL hd)
  convert localCount_ball_matching x z y (r:=r+d) hmatch using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring
end Coulomb
namespace NeutralAtom

theorem arrayEvent_fresh_statistic_lower {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    (χ : Position → ℝ) (hχm : Measurable χ) {A : Set Position}
    (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    (y : Position) {r L M Q : ℝ} (hL : 0≤L)
    (hs : ∀ v, χ v≠0 → ‖v-y‖ ≤ r) (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hhigh : ∀ z∈E, Q≤∑ i, χ (observationArrayPositions h z i))
    (hcount : ∀ z∈E, rawCount (Metric.closedBall y (r+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Q-L*(Real.sqrt 3*ℓ h)*M≤Coulomb.arrayStatistic χ x := by
  apply arrayEvent_fresh_statistic_ae ℓ (fun h => (hℓ h).ne') hE ψ u hbayes T hT hχm hχ hcs
    measurableSet_Ici
  intro x z hz he
  let w := fun ia : H × (Fin n × Fin 3) => x ia.2.1 ia.2.2+ℓ ia.1*z ia
  let X := flattenConfiguration n x
  let Y := flattenConfiguration n (observationArrayPositions h w)
  have hd : 0≤Real.sqrt 3*ℓ h := mul_nonneg (Real.sqrt_nonneg _) (hℓ h).le
  have hd' (i : Fin n) : ‖Coulomb.position Y i-Coulomb.position X i‖≤Real.sqrt 3*ℓ h := by
    simpa only [X,Y,position_flattenConfiguration] using observationArrayPositions_displacement ℓ hℓ x hz h i
  have Hmatch := Coulomb.arrayStatistic_matching_observed_count χ X Y y hd hL hs hLip hd'
  have Hcount : Coulomb.localCount (Metric.closedBall y (r+2*(Real.sqrt 3*ℓ h))) Y≤M := by
    simpa only [Y,Coulomb.localCount,position_flattenConfiguration,rawCount] using hcount w he
  have Hhigh : Q≤Coulomb.arrayStatistic χ Y := by
    simpa only [Y,Coulomb.arrayStatistic,position_flattenConfiguration] using hhigh w he
  have Herror := Hmatch.trans (mul_le_mul_of_nonneg_left Hcount (mul_nonneg hL hd))
  change Q-L*(Real.sqrt 3*ℓ h)*M≤Coulomb.arrayStatistic χ X
  linarith [(abs_le.mp Herror).2]

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

theorem arrayEvent_fresh_count_upper {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    {A : Set Position} (hcs : T.CoreSupported A) (y : Position) {R M : ℝ}
    (hfar : ∀ z∈A, R<‖z-y‖)
    (hcount : ∀ z∈E, rawCount (Metric.closedBall y (R+Real.sqrt 3*ℓ h))
      (observationArrayPositions h z)≤M) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Coulomb.localCount (Metric.closedBall y R) x≤M := by
  let χ : Position → ℝ := (Metric.closedBall y R).indicator (fun _ => 1)
  have hχm : Measurable χ := measurable_const.indicator measurableSet_closedBall
  have hχ (z) (hz : z∈A) : χ z=0 := by
    apply indicator_of_notMem
    simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hfar z hz
  apply arrayEvent_fresh_statistic_ae ℓ (fun h => (hℓ h).ne') hE ψ u hbayes T hT hχm hχ hcs
    (B := Set.Iic M) measurableSet_Iic
  intro x z hz he
  let w := fun ia : H × (Fin n × Fin 3) => x ia.2.1 ia.2.2+ℓ ia.1*z ia
  let X := flattenConfiguration n x
  let Y := flattenConfiguration n (observationArrayPositions h w)
  have hd (i : Fin n) : ‖Coulomb.position Y i-Coulomb.position X i‖≤Real.sqrt 3*ℓ h := by
    simpa only [X,Y,position_flattenConfiguration] using observationArrayPositions_displacement ℓ hℓ x hz h i
  have HH := Coulomb.localCount_ball_matching X Y y (r:=R) hd
  have HC : Coulomb.localCount (Metric.closedBall y (R+Real.sqrt 3*ℓ h)) Y≤M := by
    simpa only [Y,Coulomb.localCount,position_flattenConfiguration,rawCount] using hcount w he
  exact HH.trans HC

theorem arrayEvent_fresh_fine_lower {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    (χ : Position → ℝ) (hχm : Measurable χ) (y : Position) {r b t L M Q K : ℝ}
    (hb : 0<b) (hL : 0≤L) (hretain : r+2*b<t-7*b)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hK : ∀ z, |χ z|≤K)
    (hs : ∀ v, χ v≠0 → ‖v-y‖ ≤ r) (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hhigh : ∀ z∈E, Q≤∑ i, χ (observationArrayPositions h z i))
    (hcount : ∀ z∈E, rawCount (Metric.closedBall y (r+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Q-L*(Real.sqrt 3*ℓ h+2*b)*M≤
        ∫ z, Coulomb.retainedFineDensity b (Coulomb.patchRetained y t b x) (Coulomb.position x) z*χ z := by
  have hd : 0≤Real.sqrt 3*ℓ h := mul_nonneg (Real.sqrt_nonneg _) (hℓ h).le
  have hχ (z) (hz : t≤‖z-y‖) : χ z=0 := by
    by_contra hn
    have hh := hs z hn
    linarith
  have hrawcount (z) (hz : z∈E) {R : ℝ} (hR : R ≤ r+2*b+2*(Real.sqrt 3*ℓ h)) :
      rawCount (Metric.closedBall y R) (observationArrayPositions h z)≤M := by
    have HH := Coulomb.localCount_mono (Metric.closedBall_subset_closedBall (x:=y) hR)
      (flattenConfiguration n (observationArrayPositions h z))
    simp only [Coulomb.localCount,position_flattenConfiguration] at HH
    exact HH.trans (hcount z hz)
  have Hhigh := arrayEvent_fresh_statistic_lower ℓ hℓ h hE ψ u hbayes T hT χ hχm
    hχ hcs y hL hs hLip hhigh (fun z hz => hrawcount z hz (by linarith))
  have Hcount := arrayEvent_fresh_count_upper ℓ hℓ h hE ψ u hbayes T hT hcs y
    (R:=r+2*b) (fun z hz => by change t≤‖z-y‖ at hz; linarith)
    (fun z hz => hrawcount z hz (by linarith))
  intro p s
  filter_upwards [Hhigh p s,Hcount p s] with x hx hc
  intro hm
  have hh := hx hm
  have hcx := hc hm
  have Hfine := Coulomb.patchFine_kernel_matching hb hL hretain χ hχm hK y
    (fun z hz => by by_contra hn; linarith [hs z hn]) hLip x
  have HE := Hfine.trans (mul_le_mul_of_nonneg_left hcx (by positivity : 0≤L*(2*b)))
  change Q-L*(Real.sqrt 3*ℓ h)*M≤∑ i,χ (Coulomb.position x i) at hh
  linarith [(abs_le.mp HE).1]

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationNegativeMean
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

theorem exists_arrayEvent_fresh_negative_mean :
    ∃ C : ℝ, 0<C ∧ ∀ {J n : ℕ} {H : Type*} [Fintype H]
    (ℓ : H → ℝ), (∀ h, 0<ℓ h) → ∀ (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet E →
    ∀ (ψ : Wavefunction n) (u : Coulomb.H1Vector n),
    (∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x))) →
    ∀ (S : Coulomb.Nuclei J) (T : Coulomb.RecordedEnsemble n), T.Conserves u →
    ∀ {a b t r L M Q K P : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
    ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 0 ≤ r → r≤a → r+2*b<t-7*b →
    C*(r/a)≤1/2 → 0≤L → 0≤K → 0<P → P≤Q-L*(Real.sqrt 3*ℓ h+2*b)*M →
    ∀ (χ : Position → ℝ), Measurable χ → (∀ z, 0≤χ z ∧ χ z≤K) →
    (∀ v, χ v≠0 → ‖v-y‖ ≤ r) → (∀ v w, |χ v-χ w|≤L*‖v-w‖) →
    (∀ z∈E, Q≤∑ i, χ (observationArrayPositions h z i)) →
    (∀ z∈E, rawCount (Metric.closedBall y (r+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) →
    (∀ p s, Integrable (fun x => Coulomb.mass ((T.vector p).coreSlice s x)*
      max (-Coulomb.patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0)) ∧
    (∑ p, Coulomb.sliceExpectation (T.vector p) (fun s x =>
      max (-Coulomb.patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0))≤
      (2*K/P)*(∑ p, Coulomb.sliceExpectation (T.vector p)
        (Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))+
      (2*(C*(r/a))*(a^4)⁻¹)*T.totalMass := by
  obtain ⟨C,hC,Hbound⟩ := Coulomb.exists_patch_negative_mean_bound
  refine ⟨C,hC,?_⟩
  intro J n H inst ℓ hℓ h E hE ψ u hbayes S T hT a b t r L M Q K P ha hb hsmall ht y hn hcs hr hra hret hθ hL hK hP hmargin χ hχm hχ hs hLip hhigh hcount
  have Hfine := arrayEvent_fresh_fine_lower ℓ hℓ h hE ψ u hbayes T hT χ hχm y hb hL hret hcs
    (fun z => by rw [abs_of_nonneg (hχ z).1]; exact (hχ z).2) hs hLip hhigh hcount
  apply Hbound S T ha hb hsmall ht y hn hcs hr hra hθ χ K P hK hP hχm hχ hs
  intro p s
  filter_upwards [Hfine p s] with x hx
  exact fun hm => hmargin.trans (hx hm)

theorem arrayEvent_fresh_statistic_upper {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    (χ : Position → ℝ) (hχm : Measurable χ) {A : Set Position}
    (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    (y : Position) {r L M Q : ℝ} (hL : 0≤L)
    (hs : ∀ v, χ v≠0 → ‖v-y‖ ≤ r) (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hlow : ∀ z∈E, (∑ i, χ (observationArrayPositions h z i))≤Q)
    (hcount : ∀ z∈E, rawCount (Metric.closedBall y (r+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Coulomb.arrayStatistic χ x≤Q+L*(Real.sqrt 3*ℓ h)*M := by
  have Hlow := arrayEvent_fresh_statistic_lower ℓ hℓ h hE ψ u hbayes T hT
    (fun z => -χ z) hχm.neg
    (fun z hz => by rw [hχ z hz,neg_zero]) hcs y hL
    (fun v hv => hs v (fun hh => hv (by rw [hh,neg_zero])))
    (fun v w => by simpa only [neg_sub_neg,abs_sub_comm] using hLip v w)
    (Q:=-Q) (fun z hz => by simpa only [Finset.sum_neg_distrib,neg_le_neg_iff] using hlow z hz) hcount
  intro p s
  filter_upwards [Hlow p s] with x hx
  intro hm
  have HH := hx hm
  simp only [Coulomb.arrayStatistic,Finset.sum_neg_distrib] at HH ⊢
  linarith

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

theorem arrayEvent_fresh_patch_response (g : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z,g z^2)=1) :
    ∃ C D E F K : ℝ, 0<C ∧ 0<D ∧ 0<E ∧ 0<F ∧ 0<K ∧
    ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ {H : Type*} [Fintype H] {n J : ℕ}
    (ℓ : H → ℝ), (∀ h, 0<ℓ h) → ∀ (h : H)
    {B : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet B →
    ∀ (ψ : Wavefunction n) (u : Coulomb.H1Vector n),
    (∀ f : Coulomb.Configuration n → ℝ, Coulomb.potentialForm f u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ B))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*f (flattenConfiguration n x))) →
    ∀ (S : Coulomb.Nuclei J) (T : Coulomb.RecordedEnsemble n), T.Conserves u →
    ∀ {a b t M Qlo Qhi : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
    ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 2*packetWidth c r₀ s y≤a →
    (∀ z∈B, Qlo≤∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y) →
    (∀ z∈B, (∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y)≤Qhi) →
    (∀ z∈B, rawCount (Metric.closedBall y
        (2*packetWidth c r₀ s y+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) →
    ∀ p spin, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice spin x)≠0 →
    let w := packetWidth c r₀ s y
    let χ := fun z => packetKernel g c r₀ s z y
    let v := Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y
    let d := C*(2*w/a)*((a^4)⁻¹+max (-v) 0)
    let e := Real.sqrt ((D/w^5)*Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn spin x)+
      (F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ℓ h))*M
    Coulomb.tfScalarDensity (v-d)*(∫ z,χ z)-e≤Qhi ∧
    Qlo≤Coulomb.tfScalarDensity (v+d)*(∫ z,χ z)+e ∧
    |(∫ z,χ z)-1|≤E*(c*(1+packetExponent)*s^packetExponent) := by
  obtain ⟨C,D,E,F,hC,hD,hE,hF,Hresponse⟩ := Coulomb.master_kernel_patch_array_response g hg hm
  obtain ⟨K,hK,Hkernel⟩ := master_kernel_estimates g hg hm
  refine ⟨C,D,E,F,K,hC,hD,hE,hF,hK,?_⟩
  intro c r₀ s hc hr hs hq H inst n J ℓ hℓ h B hB ψ u hbayes S T hT a b t M Qlo Qhi ha hb hsmall ht y hn hcs hw hhigh hlow hcount
  let w := packetWidth c r₀ s y
  let χ := fun z => packetKernel g c r₀ s z y
  have hpw : 0<w := packetWidth_pos hc hr hs y
  obtain ⟨hsp,_,hLip,_,_⟩ := Hkernel hc hr hs hq y
  have hχm : Measurable χ := (((continuous_packetKernel g.continuous hc hr hs).comp
    (continuous_id.prodMk (continuous_const (y := y)))).measurable)
  have hχs (z) (hz : χ z≠0) : ‖z-y‖≤2*w := by
    simpa only [norm_sub_rev] using hsp z hz
  have hχ (z) (hz : t≤‖z-y‖) : χ z=0 := by
    by_contra hh
    have HH := hχs z hh
    dsimp only [w] at HH
    linarith [ht.1]
  have hd : 0≤Real.sqrt 3*ℓ h := mul_nonneg (Real.sqrt_nonneg _) (hℓ h).le
  have hrawcount (z) (hz : z∈B) {R : ℝ} (hR : R≤2*w+2*b+2*(Real.sqrt 3*ℓ h)) :
      rawCount (Metric.closedBall y R) (observationArrayPositions h z)≤M := by
    have HH := Coulomb.localCount_mono (Metric.closedBall_subset_closedBall (x:=y) hR)
      (flattenConfiguration n (observationArrayPositions h z))
    simp only [Coulomb.localCount,position_flattenConfiguration] at HH
    exact HH.trans (hcount z hz)
  have Hhigh := arrayEvent_fresh_statistic_lower ℓ hℓ h hB ψ u hbayes T hT χ hχm hχ hcs y
    (show 0≤K/w^4 by positivity) hχs hLip hhigh (fun z hz => hrawcount z hz (by linarith))
  have Hlow := arrayEvent_fresh_statistic_upper ℓ hℓ h hB ψ u hbayes T hT χ hχm hχ hcs y
    (show 0≤K/w^4 by positivity) hχs hLip hlow (fun z hz => hrawcount z hz (by linarith))
  have Hcount := arrayEvent_fresh_count_upper ℓ hℓ h hB ψ u hbayes T hT hcs y
    (R:=2*w+2*b) (fun z hz => by change t≤‖z-y‖ at hz; dsimp only [w]; linarith [ht.1])
    (fun z hz => hrawcount z hz (by linarith))
  intro p spin
  have Hcore : ∀ᵐ x, Coulomb.SpatiallySupported ((T.vector p).coreSlice spin x).normalized
      {z | t≤‖z-y‖} := ((hcs p).coreSlice spin).mono (fun _ hx => hx.normalized)
  filter_upwards [Hhigh p spin,Hlow p spin,Hcount p spin,Hcore] with x hhi hlo hco hcore
  intro hmass
  have Hhi := hhi hmass
  have Hlo := hlo hmass
  have Hco := hco hmass
  have Hresponse := Hresponse hc hr hs hq S (T.vector p) ha hb hsmall ht y hn hw spin x hcore
  have HE := mul_le_mul_of_nonneg_left Hco (show 0≤F/w^4*(2*b) by positivity)
  dsimp only at Hresponse ⊢
  dsimp only [Coulomb.arrayStatistic,χ,w] at Hhi Hlo HE
  refine ⟨?_,?_,Hresponse.2.2⟩ <;> linarith [Hresponse.1,Hresponse.2.1]
end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_ObservationGoodGap
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace Coulomb

lemma tf_reaction_response_good_gap {v θ A M e e₀ δ Qlo Qhi L U : ℝ}
    (hθ : 0≤θ) (hθ1 : θ≤1) (hM : 0≤M) (hMass : |M-1|≤δ)
    (hL : 0≤L) (hU : 0≤U) (he : e≤e₀)
    (hlo : Qlo≤tfScalarDensity (v+θ*(A+max (-v) 0))*M+e)
    (hhi : tfScalarDensity (v-θ*(A+max (-v) 0))*M-e≤Qhi)
    : (tfScalarDensity (L+θ*A)*(1+δ)+e₀<Qlo → L<v) ∧
      (Qhi<tfScalarDensity (U-θ*A)*(1-δ)-e₀ → v<U) := by
  have hm := abs_le.mp hMass
  constructor
  · intro hlmargin
    by_contra hnot
    have hvL : v≤L := le_of_not_gt hnot
    have hv := shifted_negative_feedback_mono (A:=A) hθ hθ1 hvL
    dsimp only at hv
    rw [max_eq_right (by linarith : -L≤0),add_zero] at hv
    have H1 := mul_le_mul_of_nonneg_right (tfScalarDensity_mono hv) hM
    have H2 := mul_le_mul_of_nonneg_left (show M≤1+δ by linarith) (tfScalarDensity_nonneg (L+θ*A))
    linarith
  · intro humargin
    by_contra hnot
    have hUv : U≤v := le_of_not_gt hnot
    have hv : 0≤v := hU.trans hUv
    rw [max_eq_right (by linarith : -v≤0),add_zero] at hhi
    have H1 := mul_le_mul_of_nonneg_right (tfScalarDensity_mono (show U-θ*A≤v-θ*A by linarith)) hM
    have H2 := mul_le_mul_of_nonneg_left (show 1-δ≤M by linarith) (tfScalarDensity_nonneg (U-θ*A))
    linarith
end Coulomb
namespace NeutralAtom

theorem arrayEvent_fresh_good_gap (g : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z,g z^2)=1) :
    ∃ C D E F K : ℝ, 0<C ∧ 0<D ∧ 0<E ∧ 0<F ∧ 0<K ∧
    ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ {H : Type*} [Fintype H] {n J : ℕ}
    (ℓ : H → ℝ), (∀ h, 0<ℓ h) → ∀ (h : H)
    {B : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet B →
    ∀ (ψ : Wavefunction n) (u : Coulomb.H1Vector n),
    (∀ f : Coulomb.Configuration n → ℝ, Coulomb.potentialForm f u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ B))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*f (flattenConfiguration n x))) →
    ∀ (S : Coulomb.Nuclei J) (T : Coulomb.RecordedEnsemble n), T.Conserves u →
    ∀ {a b t M Qlo Qhi q L U : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
    ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 2*packetWidth c r₀ s y≤a →
    (∀ z∈B, Qlo≤∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y) →
    (∀ z∈B, (∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y)≤Qhi) →
    (∀ z∈B, rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) →
    0≤L → 0≤U → C*(2*packetWidth c r₀ s y/a)≤1 →
    let w := packetWidth c r₀ s y
    let θ := C*(2*w/a)
    let δ := E*(c*(1+packetExponent)*s^packetExponent)
    let e := Real.sqrt ((D/w^5)*q)+(F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ℓ h))*M
    ∀ p spin, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice spin x)≠0 →
      Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn spin x≤q →
      (Coulomb.tfScalarDensity (L+θ*(a^4)⁻¹)*(1+δ)+e<Qlo →
        L<Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y) ∧
      (Qhi<Coulomb.tfScalarDensity (U-θ*(a^4)⁻¹)*(1-δ)-e →
        Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y<U) := by
  obtain ⟨C,D,E,F,K,hC,hD,hE,hF,hK,Hresponse⟩ := arrayEvent_fresh_patch_response g hg hm
  refine ⟨C,D,E,F,K,hC,hD,hE,hF,hK,?_⟩
  intro c r₀ s hc hr hs hscale H inst n J ℓ hℓ h B hB ψ u hlaw S T hT a b t M Qlo Qhi q L U ha hb hsmall ht y hn hcs hw hlo hhi hcount hL hU hθ
  dsimp only
  intro p spin
  have HR := Hresponse hc hr hs hscale ℓ hℓ h hB ψ u hlaw S T hT ha hb hsmall ht y hn hcs hw hlo hhi hcount p spin
  filter_upwards [HR] with x hx
  intro hmass hgap
  obtain ⟨hl,hu,hmass'⟩ := hx hmass
  have hpw := packetWidth_pos hc hr hs y
  have he : Real.sqrt ((D/(packetWidth c r₀ s y)^5)*
      Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn spin x)≤
      Real.sqrt ((D/(packetWidth c r₀ s y)^5)*q) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hgap (div_nonneg hD.le (pow_nonneg hpw.le _)))
  exact Coulomb.tf_reaction_response_good_gap (by positivity) hθ
    (integral_nonneg (fun z => packetKernel_nonneg g hc hr hs z y)) hmass' hL hU
    (add_le_add he le_rfl) hu hl
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchFieldMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma patch_TF_center_bound {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j,20*a≤‖S.position j-y‖) :
    patchTFScreenedField S u ha hb ht.2 y hn y≤tfInteriorConstant thomasFermiKineticConstant/a^4 := by
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  have hW : ∀ᵐ x ∂volume.restrict (Metric.ball y (t-4*b)), W x≤totalCharge S/a := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn),ae_restrict_mem measurableSet_ball] with x hx hy
    rw [hx]
    apply (sub_le_self _ (coreCoulombPotential_nonneg u x)).trans
    exact attraction_le_totalCharge_div S ha x (fun j => patch_nucleus_separation S ha hb ht.2 y hn j x hy)
  exact tfScreened_three_quarters measurableSet_ball thomasFermiKineticConstant_pos
    (div_nonneg (totalCharge_nonneg S) ha.le) W hW
    (localTFMinimizer_nonneg measurableSet_ball W) (fun f hf => localTFMinimizer_minimizes measurableSet_ball W hf)
    (patch_continuous_field S u ha hb ht.2 y hu hn) Metric.isOpen_ball
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (patch_harmonic_field S u ha hb ht.2 y hu hn) ha (patch_inner_ball ha hb hsmall ht.1 y)
    (by simpa using (Metric.mem_closedBall_self (x:=y) (show 0≤3*a by positivity)))

theorem patch_field_mean_lower {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    {a b t q L : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space) (hn : ∀ j,20*a≤‖S.position j-y‖)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hq : 0<q) (hL : 0≤L)
    (hneg : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*
      max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0))
    (hgood : ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      patchSliceTFGap S (T.vector p) ha hb ht.2 y hn s x≤q →
      L≤patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) :
    L*T.totalMass-(L/q)*(∑ p,sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))-
      (∑ p,sliceExpectation (T.vector p) (fun s x =>
        max (-patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0))≤
      ∑ p,sliceExpectation (T.vector p) (fun s x =>
        patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) := by
  have hs (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x,
      SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun _ hx => hx.normalized)
  have H (p : T.index) (s : Spins (T.out p)) := NeutralAtom.weighted_field_mean_lower
    (mass_coreSlice_integrable (T.vector p) s) (Eventually.of_forall (fun _ => mass_nonneg _))
    (patchTFScreenedField_weight_integrable S (T.vector p) ha hb hsmall ht y hn ha le_rfl
      (by norm_num : (0:ℝ)<1) (hs p) s)
    (patchSliceTFGap_weight_integrable S (T.vector p) ha hb ht.2 y hn s (hs p s)) (hneg p s) hq hL
    (Eventually.of_forall (fun x => patchSliceTFGap_nonneg S (T.vector p) ha hb ht.2 y hn s x)) (hgood p s)
  have HP (p : T.index) := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => H p s)
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum,integral_mass_coreSlice] at HP
  have HH := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => HP p)
  simpa only [Finset.sum_sub_distrib,←Finset.mul_sum,RecordedEnsemble.totalMass,sliceExpectation] using HH

theorem patch_field_mean_upper {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    {a b t q U : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space) (hn : ∀ j,20*a≤‖S.position j-y‖)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hq : 0<q) (hU : 0≤U)
    (hgood : ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      patchSliceTFGap S (T.vector p) ha hb ht.2 y hn s x≤q →
      patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y≤U) :
    (∑ p,sliceExpectation (T.vector p) (fun s x =>
      patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y))≤
    U*T.totalMass+((tfInteriorConstant thomasFermiKineticConstant/a^4)/q)*
      (∑ p,sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn)) := by
  have hs (p : T.index) (s : Spins (T.out p)) : ∀ᵐ x,
      SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun _ hx => hx.normalized)
  have H (p : T.index) (s : Spins (T.out p)) := NeutralAtom.weighted_field_mean_upper
    (mass_coreSlice_integrable (T.vector p) s) (Eventually.of_forall (fun _ => mass_nonneg _))
    (patchTFScreenedField_weight_integrable S (T.vector p) ha hb hsmall ht y hn ha le_rfl
      (by norm_num : (0:ℝ)<1) (hs p) s)
    (patchSliceTFGap_weight_integrable S (T.vector p) ha hb ht.2 y hn s (hs p s)) hq hU
    (div_nonneg (tfInteriorConstant_nonneg _) (pow_nonneg ha.le _))
    (Eventually.of_forall (fun x => patchSliceTFGap_nonneg S (T.vector p) ha hb ht.2 y hn s x))
    ((hs p s).mono (fun x hx _ => patch_TF_center_bound S _ ha hb hsmall ht y hx hn)) (hgood p s)
  have HP (p : T.index) := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => H p s)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,integral_mass_coreSlice] at HP
  have HH := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => HP p)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,RecordedEnsemble.totalMass,sliceExpectation] using HH
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationMeanBounds
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem arrayEvent_fresh_field_means_oai (g : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z,g z^2)=1) :
    ∃ C D E F K N B₀ : ℝ, 0<C ∧ 0<D ∧ 0<E ∧ 0<F ∧ 0<K ∧ 0<N ∧ 0<B₀ ∧
    ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ {H : Type*} [Fintype H] {n J : ℕ}
    (ℓ : H → ℝ), (∀ h, 0<ℓ h) → ∀ (h : H)
    {B : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet B →
    ∀ (ψ : Wavefunction n) (u : Coulomb.H1Vector n),
    (∀ f : Coulomb.Configuration n → ℝ, Coulomb.potentialForm f u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ B))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*f (flattenConfiguration n x))) →
    ∀ (S : Coulomb.Nuclei J) (T : Coulomb.RecordedEnsemble n), T.Conserves u → T.totalMass=1 →
    ∀ {a b t M Qlo Qhi q L U : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
    ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 2*packetWidth c r₀ s y≤a →
    (∀ z∈B, Qlo≤∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y) →
    (∀ z∈B, (∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y)≤Qhi) →
    (∀ z∈B, rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) →
    0≤L → 0≤U → 0<q → C*(2*packetWidth c r₀ s y/a)≤1 →
    let w := packetWidth c r₀ s y
    let θ := C*(2*w/a)
    let δ := E*(c*(1+packetExponent)*s^packetExponent)
    let e := Real.sqrt ((D/w^5)*q)+(F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ℓ h))*M
    let G := ∑ p,Coulomb.sliceExpectation (T.vector p) (Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn)
    let V := ∑ p,Coulomb.sliceExpectation (T.vector p) (fun spin x =>
      Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y)
    (∀ {P : ℝ}, 0<P → N*(2*w/a)≤1/2 →
      P≤Qlo-(B₀/w^4)*(Real.sqrt 3*ℓ h+2*b)*M →
      Coulomb.tfScalarDensity (L+θ*(a^4)⁻¹)*(1+δ)+e<Qlo →
      L-(L/q+2*(B₀/w^3)/P)*G-2*(N*(2*w/a))*(a^4)⁻¹≤V) ∧
    (Qhi<Coulomb.tfScalarDensity (U-θ*(a^4)⁻¹)*(1-δ)-e →
      V≤U+((Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant/a^4)/q)*G) := by
  obtain ⟨C,D,E,F,K,hC,hD,hE,hF,hK,Hgood⟩ := arrayEvent_fresh_good_gap g hg hm
  obtain ⟨N,hN,Hneg⟩ := exists_arrayEvent_fresh_negative_mean
  obtain ⟨B₀,hB₀,Hkernel⟩ := master_kernel_estimates g hg hm
  refine ⟨C,D,E,F,K,N,B₀,hC,hD,hE,hF,hK,hN,hB₀,?_⟩
  intro c r₀ s hc hr hs hscale H inst n J ℓ hℓ h B hB ψ u hlaw S T hT hTM a b t M Qlo Qhi q L U ha hb hsmall ht y hn hcs hw hlo hhi hcount hL hU hq hθ
  dsimp only
  have HG := Hgood (q:=q) hc hr hs hscale ℓ hℓ h hB ψ u hlaw S T hT ha hb hsmall ht y hn hcs hw hlo hhi hcount hL hU hθ
  constructor
  · intro P hP hNw hPm hmargin
    have hpw := packetWidth_pos hc hr hs y
    obtain ⟨hsp,hamp,hLip,_,_⟩ := Hkernel hc hr hs hscale y
    have hχm : Measurable (fun z => packetKernel g c r₀ s z y) :=
      ((continuous_packetKernel g.continuous hc hr hs).comp (continuous_id.prodMk continuous_const)).measurable
    obtain ⟨hi,hnmean⟩ := Hneg ℓ hℓ h hB ψ u hlaw S T hT ha hb hsmall ht y hn hcs
      (show 0≤2*packetWidth c r₀ s y by positivity) hw
      (show 2*packetWidth c r₀ s y+2*b<t-7*b by linarith [ht.1]) hNw
      (show 0≤B₀/(packetWidth c r₀ s y)^4 by positivity)
      (show 0≤B₀/(packetWidth c r₀ s y)^3 by positivity) hP hPm
      (fun z => packetKernel g c r₀ s z y) hχm
      (fun z => ⟨packetKernel_nonneg g hc hr hs z y,(le_abs_self _).trans (hamp z)⟩)
      (fun z hz => by simpa only [norm_sub_rev] using hsp z hz) hLip hlo hcount
    have Hmean := Coulomb.patch_field_mean_lower S T ha hb hsmall ht y hn hcs hq hL hi (fun p spin => ?_)
    · rw [hTM,mul_one] at Hmean hnmean
      linarith
    · filter_upwards [HG p spin] with x hx
      exact fun hm hg => ((hx hm hg).1 hmargin).le
  · intro hmargin
    have Hmean := Coulomb.patch_field_mean_upper S T ha hb hsmall ht y hn hcs hq hU (fun p spin => ?_)
    · simpa only [hTM,mul_one] using Hmean
    · filter_upwards [HG p spin] with x hx
      exact fun hm hg => ((hx hm hg).2 hmargin).le
end NeutralAtom
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NeutralAtom.arrayEvent_fresh_field_means_oai.{u_1} := @OAI.NeutralAtom.arrayEvent_fresh_field_means_oai.{u_1}
