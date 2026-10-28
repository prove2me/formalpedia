-- Prove2me | solution 1 for OAI.NeutralAtom.physical_propagation_good_events
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:36:21.470477+00:00
-- url     : https://prove2.me/submissions/220d16a0-bb56-4c5f-bfb7-83bb65d2996d

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008
import Theorems.Thm_OAI_NeutralAtom_physical_normalized_inverse_point
import Theorems.Thm_OAI_NeutralAtom_physical_observed_small_annular_count_tail
import Theorems.Thm_OAI_NeutralAtom_physical_retained_spatial_cap

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
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AmplitudeOscillation
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem poisson_amplitude_negative_oscillation {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ,0 < C ∧ ∀ (F σ : Position → ℝ) (y : Position) (a lam : ℝ),0 < a → 0 < lam →
      ContinuousOn F (Metric.ball y (3*a)) →
      HasWeakLaplacian F (Metric.ball y (2*a)) (fun x => 4*Real.pi*σ x) →
      Integrable σ → (∀ x,0 ≤ σ x) →
      (∀ x∈Metric.closedBall y (3*a),σ x ≤ lam*(A/a^6)) →
      (∀ x∈Metric.closedBall y (2*a),F x ≤ lam*(M/a^4)) →
      F y ≤ (∫ x,F x*Coulomb.ballCloud y (2*a) 1 x) →
      ∀ z∈Metric.closedBall y a,
        ‖F z-F y‖ ≤ C*(‖z-y‖/a)*(lam/a^4+max (-F y) 0) := by
  obtain ⟨C,hC,H⟩ := poisson_scaled_negative_oscillation hA hM
  refine ⟨C,hC,?_⟩
  intro F σ y a lam ha hlam hF hLap hi hp hb hcap hmean z hz
  let G := fun x => lam⁻¹*F x
  let τ := fun x => lam⁻¹*σ x
  have hGL : HasWeakLaplacian G (Metric.ball y (2*a)) (fun x => 4*Real.pi*τ x) := by
    convert hLap.const_mul lam⁻¹ using 1
    all_goals try with_reducible_and_instances rfl
    funext point
    dsimp [G,τ]
    ring
  have hτA (x) (hx : x∈Metric.closedBall y (3*a)) : τ x ≤ A/a^6 := by
    dsimp [τ]
    have hh := mul_le_mul_of_nonneg_left (hb x hx) (inv_nonneg.mpr hlam.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hlam.ne',one_mul] using hh
  have hGM (x) (hx : x∈Metric.closedBall y (2*a)) : G x ≤ M/a^4 := by
    dsimp [G]
    have hh := mul_le_mul_of_nonneg_left (hcap x hx) (inv_nonneg.mpr hlam.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hlam.ne',one_mul] using hh
  have hGmean : G y ≤ ∫ x,G x*Coulomb.ballCloud y (2*a) 1 x := by
    dsimp [G]
    simp_rw [mul_assoc,integral_const_mul]
    exact mul_le_mul_of_nonneg_left hmean (inv_nonneg.mpr hlam.le)
  have HH := H G τ y a ha (hF.const_mul lam⁻¹) hGL (hi.const_mul _)
    (fun x => mul_nonneg (inv_nonneg.mpr hlam.le) (hp x)) hτA hGM hGmean z hz
  have hm : max (-(lam⁻¹*F y)) 0=lam⁻¹*max (-F y) 0 := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hlam.le)]
    simp only [mul_zero,mul_neg]
  change ‖lam⁻¹*F z-lam⁻¹*F y‖ ≤ C*(‖z-y‖/a)*((a^4)⁻¹+max (-(lam⁻¹*F y)) 0) at HH
  rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlam),hm] at HH
  have he : C*(‖z-y‖/a)*((a^4)⁻¹+lam⁻¹*max (-F y) 0)=
      lam⁻¹*(C*(‖z-y‖/a)*(lam/a^4+max (-F y) 0)) := by
    field_simp [hlam.ne']
  rw [he] at HH
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr hlam)).mp HH
end NeutralAtom
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

theorem rawCount_nonneg {n : ℕ} (S : Set Position) (x : Configuration n) :
    0 ≤ rawCount S x := by
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : x i ∈ S <;> simp [hi]

theorem rawCount_le_number {n : ℕ} (S : Set Position) (x : Configuration n) :
    rawCount S x ≤ n := by
  calc
    rawCount S x ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : x i ∈ S <;> simp [hi]
    _ = n := by simp

theorem measurable_rawCount {n : ℕ} {S : Set Position} (hS : MeasurableSet S) :
    Measurable (rawCount (n := n) S) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.indicator hS).comp (measurable_pi_apply i)

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

theorem integral_packetKernel (g : Position → ℝ) (hg : (∫ y, g y ^ 2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    (∫ y, packetKernel g c₁ r₀ s z y) = 1 := by
  have ht := packetWidth_pos hc hr hs z
  unfold packetKernel
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun y : Position => (g ((packetWidth c₁ r₀ s z)⁻¹ • y)) ^ 2)]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun y : Position => g y ^ 2) ht.le]
  simp only [Position, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, hg, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ ht.ne')

theorem integrable_packetKernel (g : Position → ℝ) (hg : (∫ y, g y ^ 2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    Integrable (packetKernel g c₁ r₀ s z) := by
  by_contra hnot
  have hzero := integral_undef hnot
  rw [integral_packetKernel g hg hc hr hs z] at hzero
  exact one_ne_zero hzero

theorem packetKernel_support (g : Position → ℝ)
    (hg : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position)
    (hK : packetKernel g c₁ r₀ s z y ≠ 0) :
    ‖y-z‖ ≤ packetWidth c₁ r₀ s z := by
  have ht := packetWidth_pos hc hr hs z
  by_contra! hlt
  have harg : 1 < ‖(packetWidth c₁ r₀ s z)⁻¹ • (y-z)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    have : 1 < ‖y-z‖ / packetWidth c₁ r₀ s z := (lt_div_iff₀ ht).mpr (by simpa using hlt)
    simpa only [one_mul, div_eq_mul_inv, mul_comm] using this
  exact hK (by simp [packetKernel, hg _ harg])

theorem packetWidth_le (c₁ r₀ s : ℝ) (hc : 0 ≤ c₁) (_hr : 0 < r₀)
    (hs : 0 < s) (z : Position) :
    packetWidth c₁ r₀ s z ≤ (c₁ * s ^ packetExponent) * max ‖z‖ r₀ := by
  unfold packetWidth
  calc
    c₁ * max ‖z‖ r₀ * min (max ‖z‖ r₀) s ^ packetExponent
      ≤ c₁ * max ‖z‖ r₀ * s ^ packetExponent := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow (le_min (le_max_of_le_left (norm_nonneg _)) hs.le)
            (min_le_right _ _) (by norm_num [packetExponent])
        · exact mul_nonneg hc (le_max_of_le_left (norm_nonneg _))
    _ = (c₁ * s ^ packetExponent) * max ‖z‖ r₀ := by ring

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

theorem rawPacketDensity_nonneg {n : ℕ} (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) (y : Position) :
    0 ≤ rawPacketDensity g c₁ r₀ s x y :=
  Finset.sum_nonneg (fun i _ => packetKernel_nonneg g hc hr hs (x i) y)

theorem rawPacketDensity_integrable {n : ℕ} (g : Position → ℝ) (hgnorm : (∫ y, g y^2)=1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) :
    Integrable (rawPacketDensity g c₁ r₀ s x) :=
  integrable_finsetSum _ (fun i _ => integrable_packetKernel g hgnorm hc hr hs (x i))

theorem rawPacketDensity_mass {n : ℕ} (g : Position → ℝ) (hgnorm : (∫ y, g y^2)=1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) :
    (∫ y, rawPacketDensity g c₁ r₀ s x y) = n := by
  unfold rawPacketDensity
  rw [integral_finsetSum _ (fun i _ => integrable_packetKernel g hgnorm hc hr hs (x i))]
  simp only [integral_packetKernel g hgnorm hc hr hs, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem continuous_rawPacketDensity {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    Continuous (fun xy : Configuration n × Position => rawPacketDensity g c₁ r₀ s xy.1 xy.2) := by
  have hi : ∀ i : Fin n, Continuous (fun xy : Configuration n × Position =>
      packetKernel g c₁ r₀ s (xy.1 i) xy.2) := by
    intro i
    have hh : Continuous (fun xy : Configuration n × Position => xy.1 i) :=
      (continuous_apply i).comp continuous_fst
    have hhpair : Continuous (fun xy : Configuration n × Position => (xy.1 i,xy.2)) :=
      hh.prodMk continuous_snd
    change Continuous ((fun zy : Position × Position => packetKernel g c₁ r₀ s zy.1 zy.2) ∘
      (fun xy : Configuration n × Position => (xy.1 i,xy.2)))
    exact (continuous_packetKernel hg hc hr hs).comp hhpair
  exact continuous_finsetSum Finset.univ (fun i _ => hi i)

theorem rawPacketDensity_prod_integrable {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    (hgnorm : (∫ y, g y^2)=1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] :
    Integrable (fun xy : Configuration n × Position => rawPacketDensity g c₁ r₀ s xy.1 xy.2)
      (ν.prod volume) := by
  apply (integrable_prod_iff (continuous_rawPacketDensity hg hc hr hs).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (rawPacketDensity_integrable g hgnorm hc hr hs)
  · have he : (fun x : Configuration n => ∫ y, ‖rawPacketDensity g c₁ r₀ s x y‖) =
        (fun _ => (n : ℝ)) := by
      funext x
      simp only [Real.norm_eq_abs, abs_of_nonneg (rawPacketDensity_nonneg g hc hr hs x _),
        rawPacketDensity_mass g hgnorm hc hr hs]
    rw [he]
    exact integrable_const _

theorem mixturePacketDensity_integrable {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    (hgnorm : (∫ y, g y^2)=1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] :
    Integrable (mixturePacketDensity ν g c₁ r₀ s) :=
  (rawPacketDensity_prod_integrable hg hgnorm hc hr hs ν).integral_prod_right

theorem mixturePacketDensity_nonneg {n : ℕ} (ν : Measure (Configuration n))
    (g : Position → ℝ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (y : Position) : 0 ≤ mixturePacketDensity ν g c₁ r₀ s y :=
  integral_nonneg (fun x => rawPacketDensity_nonneg g hc hr hs x y)

theorem packetWidth_lower {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    c₁*r₀*(min r₀ s)^packetExponent ≤ packetWidth c₁ r₀ s z := by
  unfold packetWidth
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le
  · exact Real.rpow_le_rpow (lt_min hr hs).le
      (min_le_min (le_max_right _ _) le_rfl) (by norm_num [packetExponent])
  · exact Real.rpow_nonneg (lt_min hr hs).le _
  · exact mul_nonneg hc.le (hr.le.trans (le_max_right _ _))

theorem compact_packet_function_bound {g : Position → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x, g x^2 ≤ A := by
  obtain ⟨A,hA⟩ := ((hgs.isCompact_range hg).image (continuous_id.pow 2)).bddAbove
  refine ⟨A, (sq_nonneg (g 0)).trans (hA ⟨g 0, ⟨0,rfl⟩,rfl⟩), ?_⟩
  intro x
  exact hA ⟨g x,⟨x,rfl⟩,rfl⟩

theorem packetKernel_bound {g : Position → ℝ} {A c₁ r₀ s : ℝ}
    (_hA : 0 ≤ A) (hg : ∀ x, g x^2 ≤ A)
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    packetKernel g c₁ r₀ s z y ≤ (c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A := by
  have hp : 0 < c₁*r₀*(min r₀ s)^packetExponent := by positivity
  have hh := packetWidth_lower hc hr hs z
  have hinv := inv_anti₀ (pow_pos hp 3) (pow_le_pow_left₀ hp.le hh 3)
  change (packetWidth c₁ r₀ s z^3)⁻¹*g _^2 ≤ _
  rw [zpow_neg]
  exact mul_le_mul hinv (hg _) (sq_nonneg _) (by positivity)

theorem rawPacketDensity_bound {n : ℕ} {g : Position → ℝ} {A c₁ r₀ s : ℝ}
    (hA : 0 ≤ A) (hg : ∀ x, g x^2 ≤ A)
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) (y : Position) :
    rawPacketDensity g c₁ r₀ s x y ≤
      n*((c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A) := by
  calc
    _ ≤ ∑ _i : Fin n, (c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A :=
      Finset.sum_le_sum (fun i _ => packetKernel_bound hA hg hc hr hs (x i) y)
    _ = _ := by simp

theorem rawPacketDensity_integrable_configuration {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (y : Position) :
    Integrable (fun x => rawPacketDensity g c₁ r₀ s x y) ν := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  have hm : AEStronglyMeasurable (fun x => rawPacketDensity g c₁ r₀ s x y) ν :=
    ((continuous_rawPacketDensity hg hc hr hs).comp
      (continuous_id.prodMk (continuous_const (y := y)))).aestronglyMeasurable
  apply (integrable_const (n*((c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A))).mono' hm
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (rawPacketDensity_nonneg g hc hr hs x y)]
    using rawPacketDensity_bound hA hAb hc hr hs x y

theorem mixturePacketDensity_bounded {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ν : Measure (Configuration n)) [IsProbabilityMeasure ν] y,
      mixturePacketDensity ν g c₁ r₀ s y ≤ A := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  let C := n*((c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A)
  have hw : 0 < c₁*r₀*(min r₀ s)^packetExponent := by positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ν hν y
  have hh := integral_mono (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y)
    (integrable_const C) (fun x => rawPacketDensity_bound hA hAb hc hr hs x y)
  simpa only [mixturePacketDensity, integral_const, probReal_univ, one_smul] using hh

theorem conditionalPacketDensity_nonneg {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (raw : Ω → Configuration n) (obs : Ω → B)
    (g : Position → ℝ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (datum : B) (y : Position) : 0 ≤ conditionalPacketDensity P raw obs g c₁ r₀ s datum y :=
  mixturePacketDensity_nonneg _ g hc hr hs y

theorem conditionalPacketDensity_bounded {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ datum y, conditionalPacketDensity P raw obs g c₁ r₀ s datum y ≤ A := by
  obtain ⟨A,hA,h⟩ := mixturePacketDensity_bounded (n := n) hg hgs hc hr hs
  exact ⟨A,hA,fun datum y => h (ProbabilityTheory.condDistrib raw obs P datum) y⟩

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalMatching
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff
namespace NeutralAtom

theorem measurable_forgetOrder {n : ℕ} : Measurable (forgetOrder (n := n)) :=
  measurable_iff_le_map.mpr le_rfl

theorem observationLaw_rawProjection {n J : ℕ} (ν : Measure (Configuration n)) :
    MeasurePreserving Prod.fst (observationLaw J ν) ν := measurePreserving_fst

theorem observationNoiseVector_coordinate (v : Fin 3 → ℝ) (a : Fin 3) :
    observationNoiseVector v a = v a := by
  simp [observationNoiseVector, Pi.single_apply]

theorem continuous_observationNoiseVector : Continuous observationNoiseVector := by
  unfold observationNoiseVector
  exact continuous_finsetSum Finset.univ (fun a _ => (continuous_apply a).smul continuous_const)

theorem measurable_observedOrdered {n J : ℕ} (r : Fin J → ℝ) (j : Fin J) :
    Measurable (observedOrdered (n := n) r j) := by
  apply Measurable.of_eval
  intro i
  have hn : Measurable (fun sample : ObservationSample n J => sample.2 j i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)
  exact ((measurable_pi_apply i).comp measurable_fst).add
    ((continuous_observationNoiseVector.measurable.comp hn).const_smul ((r j)^(101/100 : ℝ)))

theorem measurable_observedArray {n J : ℕ} (r : Fin J → ℝ) (j : Fin J) :
    Measurable (observedArray (n := n) r j) :=
  measurable_forgetOrder.comp (measurable_observedOrdered r j)

theorem measurable_tailObservation {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    Measurable (tailObservation (n := n) r j) := by
  apply Measurable.of_eval
  intro k
  by_cases hj : j ≤ k.val
  · simpa only [tailObservation, ite_eq_left hj] using measurable_observedArray r k
  · simpa only [tailObservation, ite_eq_right hj] using
      (measurable_const : Measurable (fun _ : ObservationSample n J => forgetOrder (0 : Configuration n)))

theorem observationSigma_le {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    observationSigma (n := n) r j ≤ (inferInstance : MeasurableSpace (ObservationSample n J)) :=
  measurable_iff_comap_le.mp (measurable_tailObservation r j)

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_OriginalPotentialTower
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
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
namespace NeutralAtom

theorem rawPacketPotential_uniform {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z, g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) :
    ∃ B : ℝ, 0≤B ∧ ∀ (x : Configuration n) (y : Position),
      Integrable (fun z => coulombKernel (y-z)*rawPacketDensity g c r₀ s x z) ∧
      0≤potentialOf (rawPacketDensity g c r₀ s x) y ∧
      potentialOf (rawPacketDensity g c r₀ s x) y≤B := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  let M : ℝ := n*((c*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A)
  have hM : 0≤M := by dsimp [M]; positivity
  refine ⟨2*Real.pi*M+n,by positivity,?_⟩
  intro x y
  have hρ := rawPacketDensity_integrable g hm hc hr hs x
  have hρm : Measurable (rawPacketDensity g c r₀ s x) :=
    ((continuous_rawPacketDensity hg hc hr hs).comp
      ((continuous_const (y := x)).prodMk continuous_id)).measurable
  have hρ0 := rawPacketDensity_nonneg g hc hr hs x
  have hρM : ∀ z,rawPacketDensity g c r₀ s x z≤M :=
    rawPacketDensity_bound hA hAb hc hr hs x
  refine ⟨Coulomb.coulomb_convolution_integrable hρ hρm hρ0 hρM
    (by norm_num : (0:ℝ)<1) y,integral_nonneg (fun z =>
      mul_nonneg (coulombKernel_nonneg _) (hρ0 z)),?_⟩
  simpa [potentialOf,coulombKernel,Coulomb.coulombKernel,rawPacketDensity_mass g hm hc hr hs] using
    Coulomb.coulomb_convolution_bound hρ hρm hρ0 hρM (by norm_num : (0:ℝ)<1) y

lemma measurable_rawPacketPotential {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable (fun x : Configuration n => potentialOf (rawPacketDensity g c r₀ s x) y) := by
  have hi : Measurable (fun xz : Configuration n × Position =>
      coulombKernel (y-xz.2)*rawPacketDensity g c r₀ s xz.1 xz.2) :=
    (measurable_coulombKernel.comp (measurable_const.sub measurable_snd)).mul
      (continuous_rawPacketDensity hg hc hr hs).measurable
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_rawPacketPotential {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (y : Position) :
    Integrable (fun x => potentialOf (rawPacketDensity g c r₀ s x) y) ν := by
  obtain ⟨B,hB,H⟩ := rawPacketPotential_uniform (n := n) hg hgs hm hc hr hs
  apply (integrable_const B).mono' (measurable_rawPacketPotential hg hc hr hs y).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa [Real.norm_of_nonneg (H x y).2.1] using (H x y).2.2)

theorem mixturePacketPotential {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (y : Position) :
    potentialOf (mixturePacketDensity ν g c r₀ s) y =
      ∫ x, potentialOf (rawPacketDensity g c r₀ s x) y ∂ν := by
  obtain ⟨B,hB,H⟩ := rawPacketPotential_uniform (n := n) hg hgs hm hc hr hs
  have hmeas : Measurable (fun xz : Configuration n × Position =>
      coulombKernel (y-xz.2)*rawPacketDensity g c r₀ s xz.1 xz.2) :=
    (measurable_coulombKernel.comp (measurable_const.sub measurable_snd)).mul
      (continuous_rawPacketDensity hg hc hr hs).measurable
  have hi : Integrable (fun xz : Configuration n × Position =>
      coulombKernel (y-xz.2)*rawPacketDensity g c r₀ s xz.1 xz.2) (ν.prod volume) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun x => (H x y).1),?_⟩
    have he : (fun x : Configuration n => ∫ z, ‖coulombKernel (y-z)*rawPacketDensity g c r₀ s x z‖)=
        fun x => potentialOf (rawPacketDensity g c r₀ s x) y := by
      funext x
      simp only [potentialOf,Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (rawPacketDensity_nonneg g hc hr hs x _))]
    rw [he]
    exact integrable_rawPacketPotential hg hgs hm hc hr hs ν y
  change (∫ z, coulombKernel (y-z)*(∫ x,rawPacketDensity g c r₀ s x z ∂ν))=_
  simp_rw [←integral_const_mul]
  exact integral_integral_swap hi.swap

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationSmallScale
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

lemma tendsto_positive_rpow_zero {q : ℝ} (hq : 0<q) :
    Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) := by
  simpa [Real.zero_rpow hq.ne'] using
    ((Real.continuous_rpow_const hq.le).tendsto 0).mono_left nhdsWithin_le_nhds

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

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFResponseMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma tfScalarDensity_continuous : Continuous tfScalarDensity := by
  unfold tfScalarDensity
  exact (Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/2)).comp
    ((continuous_id.max continuous_const).div_const _)

lemma tfScalarDensity_strict {v w : ℝ} (hv : 0≤v) (hvw : v<w) :
    tfScalarDensity v<tfScalarDensity w := by
  unfold tfScalarDensity
  rw [max_eq_left hv,max_eq_left (hv.trans hvw.le)]
  apply Real.rpow_lt_rpow (div_nonneg hv (mul_nonneg thomasFermiKineticConstant_pos.le (by norm_num))) _ (by norm_num)
  exact (div_lt_div_iff_of_pos_right (mul_pos thomasFermiKineticConstant_pos (by norm_num))).mpr hvw

theorem exists_tf_response_margins {hl hh η : ℝ} (hη : 0<η) (hηl : η<hl)
    (hlh : hl≤hh) : ∃ ε : ℝ, 0<ε ∧ ε≤1 ∧
    ∀ {h θ δ e : ℝ}, h∈Icc hl hh → 0≤θ → θ≤ε → 0≤δ → δ≤ε → 0≤e → e≤ε →
      tfScalarDensity (h-η+θ)*(1+δ)+e<tfScalarDensity h ∧
      tfScalarDensity h<tfScalarDensity (h+η-θ)*(1-δ)-e := by
  have hlo : 0<hl := hη.trans hηl
  have hcontL : Continuous (fun h => tfScalarDensity h-tfScalarDensity (h-η/2)) :=
    tfScalarDensity_continuous.sub (tfScalarDensity_continuous.comp (continuous_id.sub continuous_const))
  have hcontU : Continuous (fun h => tfScalarDensity (h+η/2)-tfScalarDensity h) :=
    (tfScalarDensity_continuous.comp (continuous_id.add continuous_const)).sub tfScalarDensity_continuous
  obtain ⟨minPoint,hminPoint,Hd₁⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hlh) hcontL.continuousOn
  let d₁ := tfScalarDensity minPoint-tfScalarDensity (minPoint-η/2)
  have hd₁ : 0<d₁ :=
    sub_pos.mpr (tfScalarDensity_strict (by linarith [hminPoint.1]) (by linarith))
  obtain ⟨d₂,hd₂,Hd₂⟩ := isCompact_Icc.exists_forall_le' hcontU.continuousOn
    (a:=0) (s:=Icc hl hh) (fun h hh' => sub_pos.mpr (tfScalarDensity_strict (by linarith [hh'.1]) (by linarith)))
  let A := tfScalarDensity (hh+η)
  have hA : 0≤A := tfScalarDensity_nonneg _
  let ε := min 1 (min (η/2) (min (d₁/(2*(A+1))) (d₂/(2*(A+1)))))
  have hε : 0<ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,min_le_left _ _,?_⟩
  intro h θ δ e hh' hθ hθε hδ hδε he heε
  have hεη : ε≤η/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεd₁ : ε≤d₁/(2*(A+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεd₂ : ε≤d₂/(2*(A+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd₁' := (le_div_iff₀ (show 0<2*(A+1) by positivity)).mp hεd₁
  have hd₂' := (le_div_iff₀ (show 0<2*(A+1) by positivity)).mp hεd₂
  have hb₁ : tfScalarDensity (h-η+θ)≤tfScalarDensity (h-η/2) := tfScalarDensity_mono (by linarith)
  have hb₂ : tfScalarDensity (h+η/2)≤tfScalarDensity (h+η-θ) := tfScalarDensity_mono (by linarith)
  have hc₁ : tfScalarDensity (h-η+θ)≤A := tfScalarDensity_mono (by linarith [hh'.2])
  have hc₂ : tfScalarDensity (h+η-θ)≤A := tfScalarDensity_mono (by linarith [hh'.2])
  have herr₁ := mul_le_mul hc₁ hδε hδ hA
  have herr₂ := mul_le_mul hc₂ hδε hδ hA
  have hg₁ : d₁≤tfScalarDensity h-tfScalarDensity (h-η/2) := Hd₁ hh'
  have hg₂ := Hd₂ h hh'
  constructor <;> nlinarith
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservedUnordered
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace NeutralAtom

lemma measurable_unorderedSum {n : ℕ} {f : Position → ℝ} (hf : Measurable f) :
    Measurable (unorderedSum (n := n) f) := by
  intro s hs
  change MeasurableSet ((fun x : Configuration n => ∑ i, f (x i)) ⁻¹' s)
  exact (Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))) hs

lemma observationNoiseLaw_ae_support : ∀ᵐ u ∂observationNoiseLaw, |u|<1 := by
  rw [observationNoiseLaw,ae_withDensity_iff observationNoiseDensity_contDiff.continuous.measurable.ennreal_ofReal]
  filter_upwards [] with u hu
  by_contra hn
  apply hu
  simp [observationNoiseDensity_formula,hn]

lemma allObservationNoiseLaw_ae_support (n J : ℕ) :
    ∀ᵐ u ∂allObservationNoiseLaw n J, ∀ j i a, |u j i a|<1 := by
  simp only [ae_all_iff]
  intro j i a
  exact ((measurePreserving_eval (fun _ : Fin 3 => observationNoiseLaw) a).comp
    ((measurePreserving_eval (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)) i).comp
      (measurePreserving_eval (fun _ : Fin J => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw))) j))).quasiMeasurePreserving.ae observationNoiseLaw_ae_support

lemma observationNoiseVector_norm_le {v : Fin 3 → ℝ} (hv : ∀ a, |v a|≤1) :
    ‖observationNoiseVector v‖≤Real.sqrt 3 := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  calc
    _≤∑ _a : Fin 3, (1:ℝ) := Finset.sum_le_sum (fun a _ => by
      rw [observationNoiseVector_coordinate]
      nlinarith [(abs_le.mp (hv a)).1,(abs_le.mp (hv a)).2])
    _=_ := by norm_num

lemma observationLaw_ae_displacement {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] (r : Fin J → ℝ) (hR : ∀ k, 0 ≤ r k) :
    ∀ᵐ z ∂observationLaw J ν, ∀ j i,
      ‖z.1 i-observedOrdered r j z i‖≤Real.sqrt 3*(r j)^(101/100:ℝ) := by
  have hh : ∀ᵐ z ∂observationLaw J ν, ∀ j i a, |z.2 j i a|<1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae (allObservationNoiseLaw_ae_support n J)
  filter_upwards [hh] with z hz j i
  have hn := observationNoiseVector_norm_le (fun a => (hz j i a).le)
  rw [observedOrdered,sub_add_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (hR j) _)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (hR j) _)

lemma unorderedSum_tail_stronglyMeasurable {n J : ℕ} (r : Fin J → ℝ) (j : ℕ)
    (k : Fin J) {f : Position → ℝ} (hf : Measurable f) :
    StronglyMeasurable[observationSigma (n := n) r j]
      (fun z => unorderedSum f (tailObservation r j z k)) :=
  ((measurable_unorderedSum hf).comp ((measurable_pi_apply k).comp
    (comap_measurable (tailObservation r j)))).stronglyMeasurable

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorDataMeasurable
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
namespace NeutralAtom

lemma measurable_conditionalPacketDensity_data {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable (fun datum => conditionalPacketDensity P raw obs g c r₀ s datum y) := by
  exact (((continuous_rawPacketDensity hg hc hr hs).comp
    (continuous_id.prodMk continuous_const)).stronglyMeasurable.integral_kernel
      (κ:=ProbabilityTheory.condDistrib raw obs P)).measurable

lemma measurable_conditionalPacketPotential_data {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable (fun datum => potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) y) := by
  have H := ((measurable_rawPacketPotential (n:=n) hg hc hr hs y).stronglyMeasurable.integral_kernel
      (κ:=ProbabilityTheory.condDistrib raw obs P)).measurable
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext datum
  exact mixturePacketPotential hg hgs hm hc hr hs _ y

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalPosteriorInverse
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace NeutralAtom

lemma mixturePacketDensity_measurable {n : ℕ} (ν : Measure (Configuration n)) [SFinite ν]
    {g : Position → ℝ} (hg : Continuous g) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) :
    Measurable (mixturePacketDensity ν g c r₀ s) :=
  (continuous_rawPacketDensity hg hc hr hs).stronglyMeasurable.integral_prod_left'.measurable

lemma conditionalPacketPotential_continuous {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (datum : B) :
    Continuous (potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum)) := by
  obtain ⟨A,hA,HA⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr hs
  exact potentialOf_continuous (mixturePacketDensity_integrable hg hm hc hr hs _)
    (conditionalPacketDensity_nonneg P raw obs g hc hr hs datum) (HA datum)

lemma atomic_screened_ballCloud_submean {ρ : Position → ℝ} (hi : Integrable ρ)
    (hm : Measurable ρ) (hp : ∀ x,0≤ρ x) {A : ℝ} (hA : ∀ x,ρ x≤A)
    (Z : ℝ) {a : ℝ} (ha : 0<a) (y : Position) (hy : a≤‖y‖) :
    Z*coulombKernel y-potentialOf ρ y ≤ ∫ z,
      (Z*coulombKernel z-potentialOf ρ z)*Coulomb.ballCloud y a 1 z := by
  have hnI : Integrable (fun z => coulombKernel z*Coulomb.ballCloud y a 1 z) := by
    have H := Coulomb.coulomb_convolution_integrable (Coulomb.ballCloud_integrable a 1 y)
      (Coulomb.ballCloud_measurable a 1 y) (fun z => Coulomb.uniformBall_nonneg ha zero_le_one (z-y))
      (fun z => Coulomb.uniformBall_le ha zero_le_one (z-y)) ha (0:Position)
    simpa only [Coulomb.coulombKernel,coulombKernel,zero_sub,norm_neg] using H
  have he : (∫ z,coulombKernel z*Coulomb.ballCloud y a 1 z)=coulombKernel y := by
    have H := Coulomb.ballCloud_coulomb ha zero_le_one y (0:Position) (by simpa only [zero_sub,norm_neg] using hy)
    simpa only [Coulomb.coulombKernel,coulombKernel,zero_sub,norm_neg,one_mul] using H
  have hK := Coulomb.coulomb_convolution_integrable hi hm hp hA (by norm_num : (0:ℝ)<1) y
  have H := Coulomb.potentialOf_ballCloud_le hi hm hp ha y hK
  simp_rw [sub_mul,mul_assoc]
  rw [integral_sub (hnI.const_mul Z) (Coulomb.potentialOf_ballCloud_integrable hi hm ha y),
    integral_const_mul,he]
  linarith

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorFieldPDE
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma atomic_screenedField_weakLaplacian {ρ : Position → ℝ} (hi : Integrable ρ)
    (hc : Continuous (potentialOf ρ)) (Z : ℝ) {U : Set Position} (hU : (0:Position) ∉ U) :
    HasWeakLaplacian (fun x => Z*coulombKernel x-potentialOf ρ x) U
      (fun x => 4*Real.pi*ρ x) := by
  intro φ hφ hφc ht
  have hL := continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := hasCompactSupport_coordinateLaplacian hφc
  have hts : tsupport (coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hK : Integrable (fun x => coulombKernel x*coordinateLaplacian φ x) := by
    apply integrable_mul_compact_of_continuousAt _ hL hLc
    intro x hx
    have hn : x≠0 := fun he => hU (he ▸ ht (hts hx))
    exact continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hn)
  have hP : Integrable (fun x => potentialOf ρ x*coordinateLaplacian φ x) :=
    (hc.mul hL).integrable_of_hasCompactSupport hLc.mul_left
  have he : (∫ x,coulombKernel x*coordinateLaplacian φ x)=0 := by
    rw [integral_coulombKernel_laplacian hφ hφc,
      image_eq_zero_of_notMem_tsupport (fun h => hU (ht h))]
    ring
  simp_rw [sub_mul,mul_assoc]
  rw [integral_sub (hK.const_mul Z) hP,integral_const_mul,he,mul_zero,
    potentialOf_weakLaplacian hi φ hφ hφc (fun _ _ => mem_univ _)]
  simp only [neg_mul,integral_neg,zero_sub,neg_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_BandOscillation
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma enlarged_band_near {r L : ℝ} (hr : 0 < r) (hL : 1 ≤ L)
    {y z : Position} (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hz : ‖z-y‖ ≤ 3*(r/16)) :
    3*r/4 ≤ ‖z‖ ∧ ‖z‖ ≤ 6*L*r := by
  have h0 := norm_le_norm_add_norm_sub z y
  have h1 := norm_le_norm_add_norm_sub y z
  rw [norm_sub_rev y z] at h1
  have hLr := mul_le_mul_of_nonneg_right hL hr.le
  constructor <;> linarith

theorem atomic_band_negative_oscillation {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ,0 < C ∧ ∀ (ρ : Position → ℝ) (Z r L lam : ℝ),
      Integrable ρ → Measurable ρ → (∀ x,0 ≤ ρ x) →
      (∃ B : ℝ,∀ x,ρ x ≤ B) → Continuous (potentialOf ρ) →
      0 < r → 1 ≤ L → 1 ≤ lam →
      (∀ x,3*r/4 ≤ ‖x‖ → ‖x‖ ≤ 6*L*r → ρ x ≤ lam*(A/r^6)) →
      (∀ x,3*r/4 ≤ ‖x‖ → ‖x‖ ≤ 6*L*r →
        Z*coulombKernel x-potentialOf ρ x ≤ lam*(M/r^4)) →
      ∀ y z : Position,r ≤ ‖y‖ → ‖y‖ ≤ 4*L*r → ‖z-y‖ ≤ r/16 →
        ‖(Z*coulombKernel z-potentialOf ρ z)-(Z*coulombKernel y-potentialOf ρ y)‖ ≤
          C*(‖z-y‖/r)*(lam/r^4+max (-(Z*coulombKernel y-potentialOf ρ y)) 0) := by
  obtain ⟨C,hC,H⟩ := poisson_amplitude_negative_oscillation hA hM
  refine ⟨16^5*C,by positivity,?_⟩
  intro ρ Z r L lam hi hm hp hb hc hr hL hlam hd hcap y z hy0 hy1 hz
  let F := fun x => Z*coulombKernel x-potentialOf ρ x
  let a := r/16
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a ≤ r := by dsimp [a]; linarith
  have hnear (x : Position) (hx : x∈Metric.closedBall y (3*a)) :
      3*r/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 6*L*r :=
    enlarged_band_near hr hL hy0 hy1 (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  have hnot (b : ℝ) (hb : b ≤ 3*a) : (0:Position) ∉ Metric.ball y b := by
    intro h0
    have he := hnear 0 (Metric.mem_closedBall.mpr ((Metric.mem_ball.mp h0).le.trans hb))
    simp only [norm_zero] at he
    linarith [he.1]
  have hF : ContinuousOn F (Metric.ball y (3*a)) :=
    ((continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr
      (fun he => hnot (3*a) le_rfl (he ▸ hx)))).const_mul Z).sub hc.continuousOn
  have hLap := atomic_screenedField_weakLaplacian hi hc Z (hnot (2*a) (by linarith))
  have hden (x) (hx : x∈Metric.closedBall y (3*a)) : ρ x ≤ lam*(A/a^6) := by
    apply (hd x (hnear x hx).1 (hnear x hx).2).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact div_le_div_of_nonneg_left hA (pow_pos ha _) (pow_le_pow_left₀ ha.le har _)
  have hbound (x) (hx : x∈Metric.closedBall y (2*a)) : F x ≤ lam*(M/a^4) := by
    have hx' : x∈Metric.closedBall y (3*a) := Metric.closedBall_subset_closedBall (by linarith) hx
    apply (hcap x (hnear x hx').1 (hnear x hx').2).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact div_le_div_of_nonneg_left hM (pow_pos ha _) (pow_le_pow_left₀ ha.le har _)
  obtain ⟨B,hB⟩ := hb
  have hmean := atomic_screened_ballCloud_submean hi hm hp hB Z (by linarith : 0 < 2*a) y
    (by dsimp [a]; linarith : 2*a ≤ ‖y‖)
  have HH := H F ρ y a lam ha (by linarith) hF hLap hi hp hden hbound hmean z
    (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz)
  apply HH.trans
  have hNN : 0 ≤ max (-F y) 0 := le_max_right _ _
  have hn : 0 ≤ ‖z-y‖ := norm_nonneg _
  dsimp only [a,F] at hNN ⊢
  field_simp
  norm_num
  simp only [neg_sub] at hNN
  nlinarith [mul_nonneg (mul_nonneg hn (pow_nonneg hr.le 4)) hNN]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

lemma packetKernel_fixed_amplitude {g : Position → ℝ} {B c r₀ s : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ z, |g z^2| ≤ B)
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (x y : Position) :
    |packetKernel g c r₀ s x y| ≤ B/(packetWidth c r₀ s x)^3 := by
  have ht := packetWidth_pos hc hr hs x
  unfold packetKernel
  rw [abs_mul,abs_of_pos (by positivity : 0 < ((packetWidth c r₀ s x)^3)⁻¹)]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul (hbound ((packetWidth c r₀ s x)⁻¹ • (y-x))) le_rfl
      (by positivity : 0 ≤ ((packetWidth c r₀ s x)^3)⁻¹) hB

lemma packetKernel_fixed_lipschitz {g : Position → ℝ} {L c r₀ s : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ z v, |g z^2-g v^2| ≤ L*‖z-v‖)
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (x y z : Position) :
    |packetKernel g c r₀ s x y-packetKernel g c r₀ s x z| ≤
      (L/(packetWidth c r₀ s x)^4)*‖y-z‖ := by
  let t := packetWidth c r₀ s x
  have ht : 0 < t := packetWidth_pos hc hr hs x
  change |(t^3)⁻¹*g (t⁻¹ • (y-x))^2-(t^3)⁻¹*g (t⁻¹ • (z-x))^2| ≤ _
  rw [←mul_sub,abs_mul,abs_of_pos (by positivity : 0 < (t^3)⁻¹)]
  calc
    _ ≤ (t^3)⁻¹*(L*‖t⁻¹ • (y-x)-t⁻¹ • (z-x)‖) :=
      by
        simpa only [_root_.mul_comm] using
          mul_le_mul (hlip (t⁻¹ • (y-x)) (t⁻¹ • (z-x))) (le_refl ((t^3)⁻¹))
            (by positivity) (mul_nonneg hL (norm_nonneg _))
    _ = (L/t^4)*‖y-z‖ := by
      rw [←smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
      field_simp
    _ = _ := rfl

theorem mixture_packet_band_bounds {n : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g)
    {B L c r₀ s τ : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hbound : ∀ z, |g z^2| ≤ B) (hlip : ∀ z v, |g z^2-g v^2| ≤ L*‖z-v‖)
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (hτ : 0 < τ)
    {S T : Set Position} (hS : MeasurableSet S)
    (hsp : ∀ y∈T,∀ x,packetKernel g c r₀ s x y ≠ 0 → x∈S)
    (hw : ∀ x∈S,τ ≤ packetWidth c r₀ s x) :
    (∀ y∈T,mixturePacketDensity ν g c r₀ s y ≤
      (B/τ^3)*(∫ x,rawCount S x ∂ν)) ∧
    (∀ y∈T,∀ z∈T,|mixturePacketDensity ν g c r₀ s y-mixturePacketDensity ν g c r₀ s z| ≤
      (L/τ^4)*‖y-z‖*(∫ x,rawCount S x ∂ν)) := by
  have hcount : Integrable (rawCount (n:=n) S) ν := by
    apply Integrable.of_bound (measurable_rawCount hS).aestronglyMeasurable (n:ℝ)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (rawCount_nonneg S x)]
    exact rawCount_le_number S x
  have hpoint (x y : Position) (hy : y∈T) :
      packetKernel g c r₀ s x y ≤ (B/τ^3)*S.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x∈S
    · rw [Set.indicator_of_mem hx,mul_one]
      apply (le_abs_self _).trans
      apply (packetKernel_fixed_amplitude hB hbound hc hr hs x y).trans
      exact div_le_div_of_nonneg_left hB (pow_pos hτ 3) (pow_le_pow_left₀ hτ.le (hw x hx) 3)
    · have hz : packetKernel g c r₀ s x y=0 := by by_contra hh; exact hx (hsp y hy x hh)
      simp only [hz,Set.indicator_of_notMem hx,mul_zero,le_refl]
  have hdiff (x y z : Position) (hy : y∈T) (hz : z∈T) :
      |packetKernel g c r₀ s x y-packetKernel g c r₀ s x z| ≤
        ((L/τ^4)*‖y-z‖)*S.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x∈S
    · rw [Set.indicator_of_mem hx,mul_one]
      apply (packetKernel_fixed_lipschitz hL hlip hc hr hs x y z).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact div_le_div_of_nonneg_left hL (pow_pos hτ 4) (pow_le_pow_left₀ hτ.le (hw x hx) 4)
    · have hy0 : packetKernel g c r₀ s x y=0 := by by_contra hh; exact hx (hsp y hy x hh)
      have hz0 : packetKernel g c r₀ s x z=0 := by by_contra hh; exact hx (hsp z hz x hh)
      simp only [hy0,hz0,sub_self,abs_zero,Set.indicator_of_notMem hx,mul_zero,le_refl]
  constructor
  · intro y hy
    have H := integral_mono (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y)
      (hcount.const_mul (B/τ^3)) (fun x => show rawPacketDensity g c r₀ s x y ≤ (B/τ^3)*rawCount S x from by
        unfold rawPacketDensity rawCount
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => hpoint (x i) y hy))
    simpa only [mixturePacketDensity,integral_const_mul] using H
  · intro y hy z hz
    have hi := (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y).sub
      (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν z)
    change |(∫ x,rawPacketDensity g c r₀ s x y ∂ν)-(∫ x,rawPacketDensity g c r₀ s x z ∂ν)| ≤ _
    rw [←integral_sub (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y)
      (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν z)]
    apply (abs_integral_le_integral_abs).trans
    have H := integral_mono hi.abs (hcount.const_mul ((L/τ^4)*‖y-z‖)) (fun x => show
      |rawPacketDensity g c r₀ s x y-rawPacketDensity g c r₀ s x z| ≤ ((L/τ^4)*‖y-z‖)*rawCount S x from by
        unfold rawPacketDensity rawCount
        rw [←Finset.sum_sub_distrib,Finset.mul_sum]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hdiff (x i) y z hy hz)))
    simpa only [integral_const_mul,Pi.sub_apply] using H
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_MeshInverseDeterministic
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma exists_height_brackets {hl hh ξ : ℝ} (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
    ∃ t : Finset ℝ,(∀ v∈t,v∈Icc (hl/2) (2*hh)) ∧
      ∀ h∈Icc hl hh,
        (∃ v∈t,h-ξ/4 ≤ v ∧ v ≤ h-ξ/8) ∧
        (∃ v∈t,h+ξ/8 ≤ v ∧ v ≤ h+ξ/4) := by
  obtain ⟨S,hSf,hS⟩ := Metric.totallyBounded_iff.mp
    (isCompact_Icc : IsCompact (Icc (hl-ξ) (hh+ξ))).totallyBounded (ξ/64) (by positivity)
  let t := hSf.toFinset.filter (fun v => v∈Icc (hl/2) (2*hh))
  refine ⟨t,fun v hv => (Finset.mem_filter.mp hv).2,?_⟩
  intro h hh'
  have H (a : ℝ) (ha : a∈Icc (hl-ξ) (hh+ξ)) : ∃ v∈S,|a-v| < ξ/64 := by
    obtain ⟨v,hv⟩ := mem_iUnion.mp (hS ha)
    obtain ⟨hvs,hva⟩ := mem_iUnion.mp hv
    exact ⟨v,hvs,by simpa only [Metric.mem_ball,Real.dist_eq] using hva⟩
  obtain ⟨u,hu,hu'⟩ := H (h-3*ξ/16) ⟨by linarith [hh'.1],by linarith [hh'.2]⟩
  obtain ⟨v,hv,hv'⟩ := H (h+3*ξ/16) ⟨by linarith [hh'.1],by linarith [hh'.2]⟩
  have huabs := abs_lt.mp hu'
  have hvabs := abs_lt.mp hv'
  constructor
  · refine ⟨u,Finset.mem_filter.mpr ⟨hSf.mem_toFinset.mpr hu,?_⟩,by linarith,by linarith⟩
    constructor <;> linarith [hh'.1,hh'.2]
  · refine ⟨v,Finset.mem_filter.mpr ⟨hSf.mem_toFinset.mpr hv,?_⟩,by linarith,by linarith⟩
    constructor <;> linarith [hh'.1,hh'.2]

lemma exists_density_mesh_margin {hl hh ξ : ℝ} (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
    ∃ ε : ℝ,0 < ε ∧ ∀ h∈Icc hl hh,
      Coulomb.tfScalarDensity (h-ξ/8)+ε < Coulomb.tfScalarDensity h ∧
      Coulomb.tfScalarDensity h+ε < Coulomb.tfScalarDensity (h+ξ/8) := by
  obtain ⟨ε,hε,hε1,H⟩ := Coulomb.exists_tf_response_margins
    (show 0 < ξ/8 by positivity) (show ξ/8 < hl by linarith) hlh
  refine ⟨ε,hε,?_⟩
  intro h hh'
  have HH := H (θ:=0) (δ:=0) (e:=ε) hh' le_rfl hε.le le_rfl hε.le hε.le le_rfl
  simp only [add_zero,mul_one,sub_zero] at HH
  constructor <;> linarith [HH.1,HH.2]

lemma negative_modulus_low_transfer {u v δ lam h ξ : ℝ}
    (hξ : 0 < ξ) (hh : ξ < h) (_ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδl : δ*lam ≤ ξ/8) (hmod : |v-u| ≤ δ*(lam+max (-u) 0)) (hu : u < h-ξ) :
    v < h-3*ξ/4 := by
  have H := (abs_le.mp hmod).2
  by_cases hu0 : 0 ≤ u
  · rw [max_eq_right (by linarith)] at H
    linarith
  · have hu0 : u < 0 := lt_of_not_ge hu0
    rw [max_eq_left (by linarith)] at H
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-δ) (neg_nonneg.mpr hu0.le)]

lemma negative_modulus_high_transfer {u v δ lam h ξ : ℝ}
    (hξ : 0 < ξ) (hh : 0 ≤ h) (hδl : δ*lam ≤ ξ/8)
    (hmod : |v-u| ≤ δ*(lam+max (-u) 0)) (hu : h+ξ < u) :
    h+3*ξ/4 < v := by
  have H := (abs_le.mp hmod).1
  rw [max_eq_right (by linarith)] at H
  linarith

theorem inverse_of_space_height_mesh {S : Set Position} {t : Finset Position}
    {heights : Finset ℝ} {u d : Position → ℝ} {hl hh ξ ε δ lam η : ℝ}
    (hξ : 0 < ξ) (hξl : ξ < hl) (_ : 0 < ε) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδl : δ*lam ≤ ξ/8) (hη : 0 < η) (hηξ : η ≤ ξ/4)
    (hheights : ∀ h∈Icc hl hh,
      (∃ v∈heights,h-ξ/4 ≤ v ∧ v ≤ h-ξ/8) ∧
      (∃ v∈heights,h+ξ/8 ≤ v ∧ v ≤ h+ξ/4))
    (hmargin : ∀ h∈Icc hl hh,
      Coulomb.tfScalarDensity (h-ξ/8)+ε < Coulomb.tfScalarDensity h ∧
      Coulomb.tfScalarDensity h+ε < Coulomb.tfScalarDensity (h+ξ/8))
    (hmesh : ∀ y∈S,∃ z∈t,|d z-d y| ≤ ε ∧
      |u z-u y| ≤ δ*(lam+max (-u y) 0))
    (hinv : ∀ z∈t,∀ h∈heights,
      (Coulomb.tfScalarDensity h ≤ d z → h-η < u z) ∧
      (d z ≤ Coulomb.tfScalarDensity h → u z < h+η)) :
    ∀ y∈S,∀ h∈Icc hl hh,
      (Coulomb.tfScalarDensity h ≤ d y → h-ξ ≤ u y) ∧
      (d y ≤ Coulomb.tfScalarDensity h → u y ≤ h+ξ) := by
  intro y hy h hh'
  obtain ⟨z,hz,hden,hfield⟩ := hmesh y hy
  obtain ⟨hlo,hhi⟩ := hheights h hh'
  obtain ⟨hmlo,hmhi⟩ := hmargin h hh'
  have hhξ : ξ < h := hξl.trans_le hh'.1
  have hden' := abs_le.mp hden
  constructor
  · intro hdy
    by_contra hn
    have hu : u y < h-ξ := lt_of_not_ge hn
    obtain ⟨v,hv,hv0,hv1⟩ := hlo
    have hdv : Coulomb.tfScalarDensity v ≤ d z := by
      have H := Coulomb.tfScalarDensity_mono hv1
      linarith
    have H := (hinv z hz v hv).1 hdv
    have H' := negative_modulus_low_transfer hξ hhξ hδ hδ1 hδl hfield hu
    linarith
  · intro hdy
    by_contra hn
    have hu : h+ξ < u y := lt_of_not_ge hn
    obtain ⟨v,hv,hv0,hv1⟩ := hhi
    have hdv : d z ≤ Coulomb.tfScalarDensity v := by
      have H := Coulomb.tfScalarDensity_mono hv0
      linarith
    have H := (hinv z hz v hv).2 hdv
    have H' := negative_modulus_high_transfer hξ (by linarith : 0 ≤ h) hδl hfield hu
    linarith
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_NormalizedBandModulus
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma norm_pow_difference_bound {R : ℝ} (hR : 0 ≤ R) {y z : Position}
    (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) (k : ℕ) :
    |‖z‖^k-‖y‖^k| ≤ ‖z-y‖*k*R^(k-1) := by
  have H := abs_pow_sub_pow_le (a:=‖z‖) (b:=‖y‖) (n:=k)
  simp only [abs_of_nonneg (norm_nonneg _)] at H
  apply H.trans
  exact mul_le_mul_of_nonneg
    (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z y) (Nat.cast_nonneg _))
    (pow_le_pow_left₀ (by positivity) (max_le hz hy) _)
    (by positivity) (pow_nonneg hR _)

lemma normalized_density_difference {ρ : Position → ℝ} {r L P Q : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {y z : Position} (_ : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hz0 : r ≤ ‖z‖) (hz1 : ‖z‖ ≤ 4*L*r)
    (hρ0 : 0 ≤ ρ y) (hρ : ρ y ≤ P/r^6)
    (hlip : |ρ z-ρ y| ≤ (Q/r^7)*‖z-y‖) :
    |‖z‖^6*ρ z-‖y‖^6*ρ y| ≤
      ((4*L)^6*Q+6*(4*L)^5*P)*(‖z-y‖/r) := by
  have he : ‖z‖^6*ρ z-‖y‖^6*ρ y=‖z‖^6*(ρ z-ρ y)+(‖z‖^6-‖y‖^6)*ρ y := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg z) 6),abs_of_nonneg hρ0]
  have hdist := norm_pow_difference_bound (by positivity : 0 ≤ 4*L*r) hy1 hz1 6
  norm_num only [Nat.cast_ofNat,Nat.reduceSub] at hdist
  calc
    _ ≤ (4*L*r)^6*((Q/r^7)*‖z-y‖)+(‖z-y‖*6*(4*L*r)^5)*(P/r^6) :=
      add_le_add
        (mul_le_mul_of_nonneg (pow_le_pow_left₀ (hr.le.trans hz0) hz1 6) hlip
          (pow_nonneg (norm_nonneg z) 6)
          (mul_nonneg (div_nonneg hQ (pow_nonneg hr.le _)) (norm_nonneg _)))
        (mul_le_mul_of_nonneg hdist hρ (abs_nonneg _)
          (div_nonneg hP (pow_nonneg hr.le _)))
    _ = _ := by field_simp

lemma normalized_field_difference {F : Position → ℝ} {r L C M lam : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M) (hlam : 1 ≤ lam)
    {y z : Position} (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (_ : r ≤ ‖z‖) (hz1 : ‖z‖ ≤ 4*L*r)
    (hcap : ‖y‖^4*F y ≤ M)
    (hosc : |F z-F y| ≤ C*(‖z-y‖/r)*(lam/r^4+max (-F y) 0)) :
    |‖z‖^4*F z-‖y‖^4*F y| ≤
      ((4*L)^4*C+4*(4*L)^3*max M 1)*(‖z-y‖/r)*(lam+max (-(‖y‖^4*F y)) 0) := by
  let N := max (-(‖y‖^4*F y)) 0
  have hN : 0 ≤ N := le_max_right _ _
  have hyn : 0 < ‖y‖ := hr.trans_le hy0
  have hFy : F y ≤ M/r^4 := by
    calc
      _ ≤ M/‖y‖^4 := (le_div_iff₀ (pow_pos hyn 4)).mpr (by simpa only [mul_comm] using hcap)
      _ ≤ M/r^4 := div_le_div_of_nonneg_left hM (pow_pos hr 4) (pow_le_pow_left₀ hr.le hy0 4)
  have hneg : max (-F y) 0 ≤ N/r^4 := by
    apply (le_div_iff₀ (pow_pos hr 4)).mpr
    have he : N=‖y‖^4*max (-F y) 0 := by
      dsimp [N]
      rw [mul_max_of_nonneg _ _ (pow_nonneg (norm_nonneg y) 4),mul_zero,mul_neg]
    rw [he]
    calc
      max (-F y) 0 * r^4 = r^4 * max (-F y) 0 := mul_comm _ _
      _ ≤ ‖y‖^4 * max (-F y) 0 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hy0 4) (le_max_right _ _)
  have habs : |F y| ≤ (M+N)/r^4 := by
    rw [abs_le]
    constructor
    · have H := (le_max_left (-F y) 0).trans hneg
      have hMN : N/r^4 ≤ (M+N)/r^4 := div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le 4)
      linarith
    · exact hFy.trans (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le 4))
  have hFdiff : |F z-F y| ≤ C*(‖z-y‖/r)*((lam+N)/r^4) := by
    apply hosc.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [add_div]
    gcongr
  have hdist := norm_pow_difference_bound (by positivity : 0 ≤ 4*L*r) hy1 hz1 4
  norm_num only [Nat.cast_ofNat,Nat.reduceSub] at hdist
  have hMN : M+N ≤ max M 1*(lam+N) := by
    have hm0 : 0 ≤ max M 1 := le_trans (by norm_num) (le_max_right _ _)
    have hm1 := le_max_right M (1:ℝ)
    have H := mul_le_mul_of_nonneg_left hlam hm0
    have HN := mul_le_mul_of_nonneg_right hm1 hN
    nlinarith [le_max_left M (1:ℝ)]
  have he : ‖z‖^4*F z-‖y‖^4*F y=‖z‖^4*(F z-F y)+(‖z‖^4-‖y‖^4)*F y := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg z) 4)]
  calc
    _ ≤ (4*L*r)^4*(C*(‖z-y‖/r)*((lam+N)/r^4))+
        (‖z-y‖*4*(4*L*r)^3)*((M+N)/r^4) :=
      add_le_add
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz1 4) hFdiff (abs_nonneg _) (by positivity))
        (mul_le_mul hdist habs (abs_nonneg _) (by positivity))
    _ ≤ (4*L*r)^4*(C*(‖z-y‖/r)*((lam+N)/r^4))+
        (‖z-y‖*4*(4*L*r)^3)*((max M 1*(lam+N))/r^4) := by gcongr
    _ = _ := by field_simp; ring
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace NeutralAtom

lemma mesh_width_ratio_formula {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    r/(c*(r/3)*(r/3)^packetExponent) =
      (3^(1+packetExponent)/c)*r^(-packetExponent) := by
  rw [Real.div_rpow hr.le (by norm_num : (0:ℝ) ≤ 3),
    Real.rpow_add (by norm_num : (0:ℝ) < 3),Real.rpow_one,
    Real.rpow_neg hr.le]
  field_simp

lemma mesh_width_power_tendsto {c : ℝ} (hc : 0 < c) (k : ℕ)
    (hk : (k:ℝ)*packetExponent < 1) :
    Tendsto (fun r : ℝ => r*(r/(c*(r/3)*(r/3)^packetExponent))^k) (𝓝[>] 0) (𝓝 0) := by
  have H := (tendsto_positive_rpow_zero (show 0 < 1-(k:ℝ)*packetExponent by linarith)).const_mul
    ((3^(1+packetExponent)/c)^k)
  simp only [mul_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  rw [mesh_width_ratio_formula hc hr,mul_pow,←Real.rpow_natCast (r^(-packetExponent)) k,
    ←Real.rpow_mul hr.le]
  have he : 1-(k:ℝ)*packetExponent=1+(-packetExponent*(k:ℝ)) := by ring
  rw [he,Real.rpow_add hr,Real.rpow_one]
  ring

lemma mesh_normalized_density_bound {r L τ B D K : ℝ} {ρ : Position → ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hτ : 0 < τ) (hτr : τ ≤ r)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K)
    {y z : Position} (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hz0 : r ≤ ‖z‖) (hz1 : ‖z‖ ≤ 4*L*r) (hdist : ‖z-y‖ ≤ r^2)
    (hρ0 : 0 ≤ ρ y) (hρ : ρ y ≤ (B/τ^3)*(K/r^3))
    (hlip : |ρ z-ρ y| ≤ (D/τ^4)*‖z-y‖*(K/r^3)) :
    |‖z‖^6*ρ z-‖y‖^6*ρ y| ≤
      ((4*L)^6*(D*K)+6*(4*L)^5*(B*K))*(r*(r/τ)^4) := by
  have ht : 1 ≤ r/τ := (le_div_iff₀ hτ).mpr (by simpa using hτr)
  have hρ' : ρ y ≤ (B*K*(r/τ)^3)/r^6 := hρ.trans_eq (by field_simp)
  have hlip' : |ρ z-ρ y| ≤ ((D*K*(r/τ)^4)/r^7)*‖z-y‖ := hlip.trans_eq (by field_simp)
  have H := normalized_density_difference hr hL (by positivity : 0 ≤ B*K*(r/τ)^3)
    (by positivity : 0 ≤ D*K*(r/τ)^4) hy0 hy1 hz0 hz1 hρ0 hρ' hlip'
  have hpow : (r/τ)^3 ≤ (r/τ)^4 := pow_le_pow_right₀ ht (by omega)
  have hd : ‖z-y‖/r ≤ r := (div_le_iff₀ hr).mpr (by nlinarith)
  calc
    _ ≤ ((4*L)^6*(D*K*(r/τ)^4)+6*(4*L)^5*(B*K*(r/τ)^3))*(‖z-y‖/r) := H
    _ ≤ ((4*L)^6*(D*K*(r/τ)^4)+6*(4*L)^5*(B*K*(r/τ)^4))*r := by gcongr
    _ = _ := by ring

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_NormalizedInversePoint
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma separated_mesh_volume_bound (t : Finset Position) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hball : ∀ x∈t,‖x‖ ≤ R)
    (hsep : ∀ x∈t,∀ y∈t,x≠y → ε < ‖x-y‖) :
    (t.card:ℝ)*(ε/3)^3 ≤ (R+ε/3)^3 := by
  have hdis : Set.PairwiseDisjoint (t:Set Position) (fun x => Metric.closedBall x (ε/3)) := by
    intro x hx y hy hxy
    apply Metric.closedBall_disjoint_closedBall
    rw [dist_eq_norm]
    linarith [hsep x hx y hy hxy]
  have hsub : (⋃ x∈t,Metric.closedBall x (ε/3)) ⊆ Metric.closedBall (0:Position) (R+ε/3) := by
    apply iUnion₂_subset
    intro x hx y hy
    rw [Metric.mem_closedBall,dist_zero_right]
    have hh : ‖y-x‖ ≤ ε/3 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
    have ht := norm_le_norm_add_norm_sub x y
    rw [norm_sub_rev x y] at ht
    linarith [hball x hx]
  have H := measureReal_mono (μ:=volume) hsub (isCompact_closedBall (0:Position) (R+ε/3)).measure_ne_top
  rw [measureReal_biUnion_finset hdis (fun _ _ => measurableSet_closedBall)
    (fun x _ => (isCompact_closedBall x (ε/3)).measure_ne_top),
    Coulomb.volume_closedBall_three _ (by positivity : 0 ≤ R+ε/3)] at H
  simp_rw [Coulomb.volume_closedBall_three _ (by positivity : 0 ≤ ε/3)] at H
  simp only [Finset.sum_const,nsmul_eq_mul] at H
  have he : (t.card:ℝ)*(4*Real.pi/3*(ε/3)^3)=(4*Real.pi/3)*((t.card:ℝ)*(ε/3)^3) := by ring
  rw [he] at H
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi/3)).mp H

theorem exists_quantitative_mesh (S : Set Position) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hball : ∀ x∈S,‖x‖ ≤ R) :
    ∃ t : Finset Position,(↑t:Set Position) ⊆ S ∧
      (∀ y∈S,∃ x∈t,‖y-x‖ ≤ ε) ∧
      (t.card:ℝ)*(ε/3)^3 ≤ (R+ε/3)^3 := by
  let P := fun t : Finset Position => (↑t:Set Position) ⊆ S ∧
    (∀ x∈t,∀ y∈t,x≠y → ε < ‖x-y‖)
  let A := {k : ℕ | ∃ t : Finset Position,t.card=k ∧ P t}
  have hb (k : ℕ) (hk : k∈A) : k ≤ ⌈(R+ε/3)^3/(ε/3)^3⌉₊ := by
    obtain ⟨t,rfl,ht⟩ := hk
    have H := separated_mesh_volume_bound t hR hε (fun x hx => hball x (ht.1 hx)) ht.2
    have hh : (t.card:ℝ) ≤ (R+ε/3)^3/(ε/3)^3 := (le_div_iff₀ (by positivity)).mpr H
    exact_mod_cast hh.trans (Nat.le_ceil _)
  have hAf : A.Finite := (Set.finite_Iic ⌈(R+ε/3)^3/(ε/3)^3⌉₊).subset hb
  have hAn : A.Nonempty := ⟨0,∅,by simp,by simp [P]⟩
  obtain ⟨k,hkf,hmaxf⟩ := hAf.toFinset.exists_max_image (fun k : ℕ => k)
    (by simpa only [Set.Finite.toFinset_nonempty] using hAn)
  have hk : k∈A := hAf.mem_toFinset.mp hkf
  have hmax (l : ℕ) (hl : l∈A) : l ≤ k := hmaxf l (hAf.mem_toFinset.mpr hl)
  obtain ⟨t,htk,ht⟩ := hk
  refine ⟨t,ht.1,?_,separated_mesh_volume_bound t hR hε (fun x hx => hball x (ht.1 hx)) ht.2⟩
  intro y hy
  by_contra hh
  push Not at hh
  have hyn : y∉t := by
    intro hyt
    have H := hh y hyt
    simp only [sub_self,norm_zero] at H
    linarith
  have hP : P (insert y t) := by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact hy
      · exact ht.1 hx
    · intro x hx z hz hxz
      by_cases hxy : x=y
      · subst x
        have hz' : z∈t := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hxz)
        exact hh z hz'
      · have hx' : x∈t := (Finset.mem_insert.mp hx).resolve_left hxy
        by_cases hzy : z=y
        · subst z
          simpa only [norm_sub_rev] using hh x hx'
        · have hz' : z∈t := (Finset.mem_insert.mp hz).resolve_left hzy
          exact ht.2 x hx' z hz' hxz
  have HM := hmax (insert y t).card ⟨insert y t,rfl,hP⟩
  simp only [Finset.card_insert_of_notMem hyn,←htk] at HM
  omega

theorem exists_atomic_band_mesh {L r : ℝ} (hL : 1 ≤ L) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ t : Finset Position,(∀ y∈t,r ≤ ‖y‖ ∧ ‖y‖ ≤ 4*L*r) ∧
      (∀ y : Position,r ≤ ‖y‖ → ‖y‖ ≤ 4*L*r → ∃ z∈t,‖y-z‖ ≤ r^2) ∧
      (t.card:ℝ) ≤ (12*L+1)^3/r^3 := by
  let S := {y : Position | r ≤ ‖y‖ ∧ ‖y‖ ≤ 4*L*r}
  obtain ⟨t,ht,hcover,hcard⟩ := exists_quantitative_mesh S (R:=4*L*r) (ε:=r^2)
    (by positivity) (by positivity) (fun _ h => h.2)
  refine ⟨t,fun y hy => ht hy,fun y hy0 hy1 => hcover y ⟨hy0,hy1⟩,?_⟩
  have hroot : 4*L*r+r^2/3 ≤ r*(4*L+1/3) := by nlinarith
  have Hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 4*L*r+r^2/3) hroot 3
  have H : (t.card:ℝ)*(r^2/3)^3 ≤ (r*(4*L+1/3))^3 := hcard.trans Hpow
  apply (le_div_iff₀ (pow_pos hr 3)).mpr
  nlinarith [pow_pos hr 3]
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketBandGeometry
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

lemma packet_band_center_support {g : Position → ℝ}
    (hg : ∀ z,1 < ‖z‖ → g z=0) {c r₀ s r L : ℝ}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hr : 0 < r)
    (hL : 1 ≤ L) (hr₀r : r₀ ≤ r)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/4)
    (hwidth : c*s^packetExponent ≤ 1/100)
    {y : Position} (hy0 : r/2 ≤ ‖y‖) (hy1 : ‖y‖ ≤ 8*L*r)
    {x : Position} (hK : packetKernel g c r₀ s x y ≠ 0) :
    r/3 ≤ ‖x‖ ∧ ‖x‖ ≤ 10*L*r := by
  have hsp := packetKernel_support g hg hc hr₀ hs x y hK
  have ht := packetWidth_lipschitz hc.le hr₀ hs x y
  have hn : ‖y-x‖=‖x-y‖ := norm_sub_rev _ _
  have he : packetWidth c r₀ s x-packetWidth c r₀ s y ≤ ‖y-x‖/4 := by
    apply (le_abs_self _).trans
    apply ht.trans
    rw [←hn]
    have hh := mul_le_mul_of_nonneg_right hscale (norm_nonneg (y-x))
    linarith
  have hp := packetWidth_le c r₀ s hc.le hr₀ hs y
  have hxmax : max ‖y‖ r₀ ≤ 2*‖y‖ := max_le (by linarith [norm_nonneg y]) (by linarith)
  have hsize : packetWidth c r₀ s y ≤ ‖y‖/50 := by
    calc
      _ ≤ (c*s^packetExponent)*max ‖y‖ r₀ := hp
      _ ≤ (1/100)*(2*‖y‖) := mul_le_mul hwidth hxmax
        (le_max_of_le_left (norm_nonneg y)) (by norm_num)
      _ = _ := by ring
  have hdist : ‖y-x‖ ≤ ‖y‖/25 := by linarith
  have hny := norm_le_norm_add_norm_sub y x
  have hnx := norm_le_norm_add_norm_sub x y
  rw [←hn] at hnx
  constructor
  · nlinarith
  · calc
      ‖x‖ ≤ (26/25:ℝ)*‖y‖ := by linarith
      _ ≤ (26/25:ℝ)*(8*L*r) := mul_le_mul_of_nonneg_left hy1 (by norm_num)
      _ ≤ 10*L*r := by
        nlinarith only [mul_nonneg (zero_le_one.trans hL) hr.le]

lemma packet_band_width_lower {c r₀ s r : ℝ}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hr : 0 < r) (hrs : r ≤ s)
    {x : Position} (hx : r/3 ≤ ‖x‖) :
    c*(r/3)*(r/3)^packetExponent ≤ packetWidth c r₀ s x := by
  have hmax : r/3 ≤ max ‖x‖ r₀ := hx.trans (le_max_left _ _)
  have hm : r/3 ≤ min (max ‖x‖ r₀) s := le_min hmax (by linarith)
  unfold packetWidth
  exact mul_le_mul (mul_le_mul_of_nonneg_left hmax hc.le)
    (Real.rpow_le_rpow (by positivity) hm (by norm_num [packetExponent]))
    (Real.rpow_nonneg (by positivity) _) (by positivity)

lemma packet_band_observation_support {r L d : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hd : d ≤ r/12)
    {x y : Position} (hx : r/3 ≤ ‖x‖ ∧ ‖x‖ ≤ 10*L*r)
    (hdist : ‖x-y‖ ≤ d) : r/4 ≤ ‖y‖ ∧ ‖y‖ ≤ 12*L*r := by
  have hx' := norm_le_norm_add_norm_sub x y
  have hy' := norm_le_norm_add_norm_sub y x
  rw [norm_sub_rev y x] at hy'
  have hrL := mul_le_mul_of_nonneg_right hL hr.le
  constructor <;> nlinarith
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_SimultaneousInverseScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace NeutralAtom

lemma exists_simultaneous_inverse_scale {c L D A B ξ ε : ℝ}
    (hc : 0 < c) (hξ : 0 < ξ) (hε : 0 < ε) :
    ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1/16 ∧ ∀ {r : ℝ},0 < r → r < s₀ →
      c*(1+packetExponent)*r^packetExponent ≤ 1/4 ∧
      c*r^packetExponent ≤ 1/10000 ∧
      (8*L/100000)*r ≤ 1 ∧ D*((8*L/100000)*r)^7 ≤ 1 ∧
      Real.sqrt 3*r^(101/100:ℝ) ≤ r/12 ∧
      c*(r/3)*(r/3)^packetExponent ≤ r ∧
      A*r ≤ 1 ∧ A*r*(r/(c*(r/3)*(r/3)^packetExponent))^3 ≤ ξ/8 ∧
      B*(r*(r/(c*(r/3)*(r/3)^packetExponent))^4) ≤ ε := by
  have hw : 0 < packetExponent := by norm_num [packetExponent]
  have h1 := (tendsto_positive_rpow_zero hw).const_mul (c*(1+packetExponent))
  have h2 := (tendsto_positive_rpow_zero hw).const_mul c
  have ht : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h3 := ht.const_mul (8*L/100000)
  have h4 := ((ht.const_mul (8*L/100000)).pow 7).const_mul D
  have h5 := (tendsto_positive_rpow_zero (by norm_num : (0:ℝ) < 1/100)).const_mul (Real.sqrt 3)
  have h6 := (tendsto_positive_rpow_zero hw).const_mul (c/(3^packetExponent))
  have h7 := ht.const_mul A
  have h8 := (mesh_width_power_tendsto hc 3 (by norm_num [packetExponent])).const_mul A
  have h9 := (mesh_width_power_tendsto hc 4 (by norm_num [packetExponent])).const_mul B
  simp only [mul_zero,zero_pow (by decide : 7≠0)] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0,
      c*(1+packetExponent)*r^packetExponent < 1/4 ∧
      c*r^packetExponent < 1/10000 ∧
      (8*L/100000)*r < 1 ∧ D*((8*L/100000)*r)^7 < 1 ∧
      Real.sqrt 3*r^(1/100:ℝ) < 1/12 ∧
      (c/(3^packetExponent))*r^packetExponent < 3 ∧
      A*r < 1 ∧ A*(r*(r/(c*(r/3)*(r/3)^packetExponent))^3) < ξ/8 ∧
      B*(r*(r/(c*(r/3)*(r/3)^packetExponent))^4) < ε := by
    filter_upwards [h1.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
      h2.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/10000)),
      h3.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
      h4.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
      h5.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/12)),
      h6.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 3)),
      h7.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
      h8.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ξ/8)),
      h9.eventually (gt_mem_nhds hε)] with r hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9
    exact ⟨hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9⟩
  obtain ⟨s,hs,Hs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨min s (1/16),lt_min hs (by norm_num),min_le_right _ _,?_⟩
  intro r hr hrs
  obtain ⟨H1,H2,H3,H4,H5,H6,H7,H8,H9⟩ := Hs ⟨hr,hrs.trans_le (min_le_left _ _)⟩
  refine ⟨H1.le,H2.le,H3.le,H4.le,?_,?_,H7.le,?_,H9.le⟩
  · have he : (101/100:ℝ)=1+1/100 := by norm_num
    rw [he,Real.rpow_add hr,Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left H5.le hr.le]
  · have ht : c*(r/3)^packetExponent < 3 := by
      rw [Real.div_rpow hr.le (by norm_num : (0:ℝ) ≤ 3)]
      convert H6 using 1
      all_goals try with_reducible_and_instances rfl
      ring
    nlinarith [mul_le_mul_of_nonneg_left ht.le (by positivity : 0 ≤ r/3)]
  · simpa only [mul_assoc] using H8.le
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma mesh_exception_probability_scale {r L C N M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hM : 0 ≤ M) (hMbound : M ≤ (12*L+1)^3/r^3) :
    r^40+C*r^249+2*M*N*r^42 ≤ (1+C+2*(12*L+1)^3*N)*r^25 := by
  have h40 : r^40 ≤ r^25 := pow_le_pow_of_le_one hr.le hr1 (by omega)
  have h249 : r^249 ≤ r^25 := pow_le_pow_of_le_one hr.le hr1 (by omega)
  have h39 : r^39 ≤ r^25 := pow_le_pow_of_le_one hr.le hr1 (by omega)
  have H : 2*M*N*r^42 ≤ 2*(12*L+1)^3*N*r^39 := by
    calc
      _ ≤ 2*((12*L+1)^3/r^3)*N*r^42 := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        apply mul_le_mul_of_nonneg_right ?_ hN
        exact mul_le_mul le_rfl hMbound hM (by norm_num)
      _ = _ := by field_simp
  calc
    _ ≤ r^25+C*r^25+2*(12*L+1)^3*N*r^25 :=
      add_le_add (add_le_add h40 (mul_le_mul_of_nonneg_left h249 hC))
        (H.trans (mul_le_mul_of_nonneg_left h39 (by positivity)))
    _ = _ := by ring
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_FiniteInverseEvent
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem finite_inverse_mesh_event {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (P : @Measure Ω m₀) [IsFiniteMeasure P] (t : Finset Position) (heights : Finset ℝ)
    (cnt : Ω → ℝ) (d u : Ω → Position → ℝ) {K η p : ℝ}
    (hc : Measurable[m] cnt) (hd : ∀ y,Measurable[m] (fun a => d a y))
    (hu : ∀ y,Measurable[m] (fun a => u a y))
    (hp : ∀ y∈t,∀ h∈heights,
      P.real {a | cnt a ≤ K ∧ Coulomb.tfScalarDensity h ≤ d a y ∧ u a y ≤ h-η} ≤ p ∧
      P.real {a | cnt a ≤ K ∧ d a y ≤ Coulomb.tfScalarDensity h ∧ h+η ≤ u a y} ≤ p) :
    ∃ G : Set Ω,(MeasurableSet[m₀] G ∧ MeasurableSet[m] G) ∧
      P.real Gᶜ ≤ 2*(t.card:ℝ)*(heights.card:ℝ)*p ∧
      ∀ a∈G,cnt a ≤ K → ∀ y∈t,∀ h∈heights,
        (Coulomb.tfScalarDensity h ≤ d a y → h-η < u a y) ∧
        (d a y ≤ Coulomb.tfScalarDensity h → u a y < h+η) := by
  let B := fun q : Position × ℝ =>
    {a | cnt a ≤ K ∧ Coulomb.tfScalarDensity q.2 ≤ d a q.1 ∧ u a q.1 ≤ q.2-η} ∪
    {a | cnt a ≤ K ∧ d a q.1 ≤ Coulomb.tfScalarDensity q.2 ∧ q.2+η ≤ u a q.1}
  let s := t.product heights
  have hBm (q : Position × ℝ) : MeasurableSet[m] (B q) := by
    exact ((measurableSet_le hc measurable_const).inter
      ((measurableSet_le measurable_const (hd q.1)).inter (measurableSet_le (hu q.1) measurable_const))).union
      ((measurableSet_le hc measurable_const).inter
        ((measurableSet_le (hd q.1) measurable_const).inter (measurableSet_le measurable_const (hu q.1))))
  let E := ⋃ q∈s,B q
  have hEm : MeasurableSet[m] E := MeasurableSet.biUnion (s.finite_toSet.countable) (fun q _ => hBm q)
  refine ⟨Eᶜ,⟨hm _ hEm.compl,hEm.compl⟩,?_,?_⟩
  · rw [compl_compl]
    calc
      P.real E ≤ ∑ q∈s,P.real (B q) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ q∈s,(2*p) := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hq0,hq1⟩ := Finset.mem_product.mp hq
        have H := hp q.1 hq0 q.2 hq1
        exact (measureReal_union_le _ _).trans (by linarith)
      _ = 2*(t.card:ℝ)*(heights.card:ℝ)*p := by simp [s]; ring
  · intro a ha hcnt y hy h hh
    have hnot : a∉B (y,h) := by
      intro hab
      exact ha (mem_iUnion.mpr ⟨(y,h),mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hy,hh⟩,hab⟩⟩)
    constructor
    · intro hden
      by_contra H
      exact hnot (Or.inl ⟨hcnt,hden,le_of_not_gt H⟩)
    · intro hden
      by_contra H
      exact hnot (Or.inr ⟨hcnt,hden,le_of_not_gt H⟩)
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorCount
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma rawCount_le_displaced {n : ℕ} {S T : Set Position}
    (x v : Configuration n) {d : ℝ}
    (hdisp : ∀ i,‖x i-v i‖ ≤ d)
    (hST : ∀ a∈S,∀ b,‖a-b‖ ≤ d → b∈T) : rawCount S x ≤ rawCount T v := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : x i∈S
  · simp only [Set.indicator_of_mem hi,Set.indicator_of_mem (hST _ hi _ (hdisp i)),le_refl]
  · rw [Set.indicator_of_notMem hi]
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _

lemma physical_observed_count_measurable {n J : ℕ} (r : Fin J → ℝ)
    (j : ℕ) (k : Fin J) (hk : j ≤ k.val) {S : Set Position} (hS : MeasurableSet S) :
    StronglyMeasurable[observationSigma (n:=n) r j]
      (fun sample => rawCount S (observedOrdered r k sample)) := by
  have H := unorderedSum_tail_stronglyMeasurable (n:=n) r j k
    (measurable_const.indicator hS : Measurable (S.indicator (fun _ => (1:ℝ))))
  simpa only [tailObservation,ite_eq_left hk,observedArray,unorderedSum_forgetOrder,rawCount] using H

lemma posterior_count_le_observed {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] (r : Fin J → ℝ) (hr : ∀ k,0 ≤ r k)
    {j : ℕ} (k : Fin J) (hk : j ≤ k.val) {S T : Set Position}
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : ∀ a∈S,∀ b,‖a-b‖ ≤ Real.sqrt 3*(r k)^(101/100:ℝ) → b∈T) :
    ∀ᵐ sample ∂observationLaw J ν,
      (∫ x,rawCount S x ∂ProbabilityTheory.condDistrib Prod.fst (tailObservation r j)
        (observationLaw J ν) (tailObservation r j sample)) ≤ rawCount T (observedOrdered r k sample) := by
  let P := observationLaw J ν
  let f := fun sample : ObservationSample n J => rawCount S sample.1
  let H := fun sample : ObservationSample n J => rawCount T (observedOrdered r k sample)
  have hfν : Integrable (rawCount (n:=n) S) ν := by
    apply Integrable.of_bound (measurable_rawCount hS).aestronglyMeasurable (n:ℝ)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (rawCount_nonneg S x)]
    exact rawCount_le_number S x
  have hf : Integrable f P := (observationLaw_rawProjection ν).integrable_comp_of_integrable hfν
  have hHm := physical_observed_count_measurable (n:=n) r j k hk hT
  have hH : Integrable H P := by
    apply Integrable.of_bound (hHm.mono (observationSigma_le r j)).aestronglyMeasurable (n:ℝ)
    filter_upwards [] with sample
    rw [Real.norm_of_nonneg (rawCount_nonneg T _)]
    exact rawCount_le_number T _
  have hle : ∀ᵐ sample ∂P,f sample ≤ H sample := by
    filter_upwards [observationLaw_ae_displacement ν r hr] with sample hh
    exact rawCount_le_displaced sample.1 (observedOrdered r k sample) (hh k) hST
  have Hle := condExp_mono hf hH hle (m:=observationSigma r j)
  rw [condExp_of_stronglyMeasurable (observationSigma_le r j) hHm hH] at Hle
  have He := ProbabilityTheory.condExp_ae_eq_integral_condDistrib
    (measurable_tailObservation r j) (observationLaw_rawProjection ν).measurable.aemeasurable
    (measurable_rawCount hS).stronglyMeasurable hf
  filter_upwards [Hle,He] with sample hh he
  rw [←he]
  exact hh
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_PhysicalCapMoment
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

lemma physicalFieldCapBase_ge_one : 1 ≤ physicalFieldCapBase := le_max_left _ _
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorSpatialCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma physicalSpatialCap_pos : 0<physicalSpatialCap := by
  unfold physicalSpatialCap
  linarith [physicalFieldCapBase_ge_one]

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalBandEvent
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_posterior_band_event (g : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g z=0) :
    ∃ B D : ℝ,0 ≤ B ∧ 0 ≤ D ∧
    ∀ {n J : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν],
    ∀ {c r₀ s r L : ℝ},0 < c → 0 < r₀ → 0 < s → 0 < r → 1 ≤ L → r₀ ≤ r → r ≤ s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 → c*s^packetExponent ≤ 1/100 →
    ∀ (rads : Fin J → ℝ),(∀ k,0 ≤ rads k) → ∀ {j : ℕ} (k : Fin J),j ≤ k.val →
    Real.sqrt 3*(rads k)^(101/100:ℝ) ≤ r/12 →
    ∃ G : Set (ObservationSample n J),
    (MeasurableSet G ∧ MeasurableSet[observationSigma rads j] G) ∧
    (observationLaw J ν) Gᶜ=0 ∧ ∀ sample∈G,
      let μ := conditionalPacketDensity (observationLaw J ν) Prod.fst (tailObservation rads j)
        g c r₀ s (tailObservation rads j sample)
      let m := rawCount {x : Position | r/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*r} (observedOrdered rads k sample)
      let τ := c*(r/3)*(r/3)^packetExponent
      (∀ y : Position,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r → μ y ≤ (B/τ^3)*m) ∧
      (∀ y z : Position,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r → r/2 ≤ ‖z‖ → ‖z‖ ≤ 8*L*r →
        |μ y-μ z| ≤ (D/τ^4)*‖y-z‖*m) := by
  obtain ⟨B,D,hB,hD,hbound,hlip⟩ := schwartz_square_bounded_lipschitz g
  refine ⟨B,D,hB,hD,?_⟩
  intro n J ν hν c r₀ s r L hc hr₀ hs hr hL hrr₀ hrs hscale hwidth rads hrads j k hk hnoise
  let S := {x : Position | r/3 ≤ ‖x‖ ∧ ‖x‖ ≤ 10*L*r}
  let T := {x : Position | r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 8*L*r}
  let O := {x : Position | r/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*r}
  have hS : MeasurableSet S := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hO : MeasurableSet O := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hgs : HasCompactSupport (g : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun z hz => hg z
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hpost := posterior_count_le_observed ν rads hrads k hk hS hO
    (fun x hx y hxy => packet_band_observation_support hr hL hnoise hx hxy)
  let obs := tailObservation (n:=n) rads j
  let P := observationLaw J ν
  let C := fun datum : Fin J → UnorderedArray n =>
    ∫ x,rawCount S x ∂ProbabilityTheory.condDistrib Prod.fst obs P datum
  let M := fun datum : Fin J → UnorderedArray n =>
    unorderedSum (O.indicator (fun _ => (1:ℝ))) (datum k)
  have hC : Measurable C := ((measurable_rawCount hS).stronglyMeasurable.integral_kernel
    (κ:=ProbabilityTheory.condDistrib Prod.fst obs P)).measurable
  have hM : Measurable M := (measurable_unorderedSum
    (measurable_const.indicator hO)).comp (measurable_pi_apply k)
  let G := obs ⁻¹' {datum | C datum ≤ M datum}
  have hM_eq (sample : ObservationSample n J) : M (obs sample)=
      rawCount O (observedOrdered rads k sample) := by
    exact unorderedSum_tailObservation rads k hk _ sample
  have hG : MeasurableSet G := (measurableSet_le hC hM).preimage (measurable_tailObservation rads j)
  have hGt : MeasurableSet[observationSigma rads j] G :=
    ⟨{datum | C datum ≤ M datum},measurableSet_le hC hM,rfl⟩
  have hGae : ∀ᵐ sample ∂P,sample∈G := by
    filter_upwards [hpost] with sample hh
    change C (obs sample) ≤ M (obs sample)
    rw [hM_eq]
    exact hh
  refine ⟨G,⟨hG,hGt⟩,by exact ae_iff.mp hGae,?_⟩
  intro sample hsamp
  have hh : C (obs sample) ≤ rawCount O (observedOrdered rads k sample) := by
    have hh : C (obs sample) ≤ M (obs sample) := hsamp
    rwa [hM_eq] at hh
  let ν' := ProbabilityTheory.condDistrib Prod.fst (tailObservation rads j) (observationLaw J ν)
    (tailObservation rads j sample)
  have hτ : 0 < c*(r/3)*(r/3)^packetExponent := by positivity
  have H := mixture_packet_band_bounds ν' g.continuous hgs hB hD hbound hlip hc hr₀ hs hτ hS
    (T:=T) (fun y hy x hx => packet_band_center_support hg hc hr₀ hs hr hL hrr₀ hscale hwidth hy.1 hy.2 hx)
    (fun x hx => packet_band_width_lower hc hr₀ hs hr hrs hx.1)
  dsimp only
  constructor
  · intro y hy0 hy1
    exact (H.1 y ⟨hy0,hy1⟩).trans (mul_le_mul_of_nonneg_left hh (by positivity))
  · intro y z hy0 hy1 hz0 hz1
    exact (H.2 y ⟨hy0,hy1⟩ z ⟨hz0,hz1⟩).trans (mul_le_mul_of_nonneg_left hh (by positivity))
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma posterior_mesh_modulus {Ω Data : Type*} [MeasurableSpace Ω] [MeasurableSpace Data]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (raw : Ω → Configuration n) (obs : Ω → Data) (g : Position → ℝ)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    (datum : Data) (Z : ℝ) {r L τ B D K C : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hτ : 0 < τ) (hτr : τ ≤ r)
    (hrsmall : r ≤ 1/16) (hB : 0 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hden : ∀ y,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r →
      conditionalPacketDensity P raw obs g c r₀ s datum y ≤ (B/τ^3)*(K/r^3))
    (hlip : ∀ y z,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r → r/2 ≤ ‖z‖ → ‖z‖ ≤ 8*L*r →
      |conditionalPacketDensity P raw obs g c r₀ s datum z-
        conditionalPacketDensity P raw obs g c r₀ s datum y| ≤ (D/τ^4)*‖z-y‖*(K/r^3))
    (hcap : ∀ y,3*r/4 ≤ ‖y‖ → ‖y‖ ≤ 6*L*r →
      ‖y‖^4*(Z*coulombKernel y-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) y) ≤ physicalSpatialCap)
    (hosc : ∀ y z,r ≤ ‖y‖ → ‖y‖ ≤ 4*L*r → ‖z-y‖ ≤ r/16 →
      let F := fun x => Z*coulombKernel x-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) x
      ‖F z-F y‖ ≤ C*(‖z-y‖/r)*((r/τ)^3/r^4+max (-F y) 0))
    {y z : Position} (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hz0 : r ≤ ‖z‖) (hz1 : ‖z‖ ≤ 4*L*r) (hdist : ‖z-y‖ ≤ r^2) :
    let ρ := conditionalPacketDensity P raw obs g c r₀ s datum
    let U := fun x => ‖x‖^4*(Z*coulombKernel x-potentialOf ρ x)
    |‖z‖^6*ρ z-‖y‖^6*ρ y| ≤
      ((4*L)^6*(D*K)+6*(4*L)^5*(B*K))*(r*(r/τ)^4) ∧
    |U z-U y| ≤ (((4*L)^4*C+4*(4*L)^3*max physicalSpatialCap 1)*r)*
      ((r/τ)^3+max (-U y) 0) := by
  let ρ := conditionalPacketDensity P raw obs g c r₀ s datum
  let F := fun x => Z*coulombKernel x-potentialOf ρ x
  have hLr : 0 ≤ L*r := mul_nonneg (by linarith) hr.le
  have hylo : r/2 ≤ ‖y‖ := by linarith
  have hyhi : ‖y‖ ≤ 8*L*r := by nlinarith
  have hzlo : r/2 ≤ ‖z‖ := by linarith
  have hzhi : ‖z‖ ≤ 8*L*r := by nlinarith
  dsimp only
  constructor
  · exact mesh_normalized_density_bound hr hL hτ hτr hB hD hK hy0 hy1 hz0 hz1 hdist
      (conditionalPacketDensity_nonneg P raw obs g hc hr₀ hs datum y)
      (hden y hylo hyhi) (hlip y z hylo hyhi hzlo hzhi)
  · have hd : ‖z-y‖ ≤ r/16 := hdist.trans (by nlinarith)
    have HH := normalized_field_difference (F:=F) (lam:=(r/τ)^3) hr hL hC physicalSpatialCap_pos.le
      (one_le_pow₀ ((le_div_iff₀ hτ).mpr (by simpa using hτr))) hy0 hy1 hz0 hz1
      (hcap y (by linarith) (by nlinarith)) (by simpa only [Real.norm_eq_abs] using hosc y z hy0 hy1 hd)
    apply HH.trans
    have hratio : ‖z-y‖/r ≤ r := (div_le_iff₀ hr).mpr (by nlinarith)
    gcongr
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma measurable_tailObservation_for_sigma {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    Measurable[observationSigma r j] (tailObservation (n:=n) r j) :=
  measurable_iff_comap_le.mpr le_rfl

lemma measurable_observed_count_tail {n J : ℕ} (r : Fin J → ℝ) {j : ℕ} (k : Fin J)
    (hk : j ≤ k.val) {S : Set Position} (hS : MeasurableSet S) :
    Measurable[observationSigma r j]
      (fun z : ObservationSample n J => rawCount S (observedOrdered r k z)) := by
  have HM : Measurable (fun datum : Fin J → UnorderedArray n =>
      unorderedSum (S.indicator (fun _ => (1:ℝ))) (datum k)) :=
    (measurable_unorderedSum (measurable_const.indicator hS)).comp (measurable_pi_apply k)
  have H := HM.comp (measurable_tailObservation_for_sigma r j)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact (unorderedSum_tailObservation r k hk _ z).symm

lemma measurable_normalized_posterior_density_tail {n J : ℕ}
    (P : Measure (ObservationSample n J)) [IsFiniteMeasure P]
    (r : Fin J → ℝ) (j : ℕ) {g : Position → ℝ} (hg : Continuous g)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable[observationSigma r j] (fun z => ‖y‖^6*
      conditionalPacketDensity P Prod.fst (tailObservation r j) g c r₀ s (tailObservation r j z) y) :=
  measurable_const.mul ((measurable_conditionalPacketDensity_data P Prod.fst
    (tailObservation r j) hg hc hr₀ hs y).comp (measurable_tailObservation_for_sigma r j))

lemma measurable_normalized_posterior_field_tail {n J : ℕ}
    (P : Measure (ObservationSample n J)) [IsFiniteMeasure P]
    (r : Fin J → ℝ) (j : ℕ) {g : Position → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (Z : ℝ) (y : Position) :
    Measurable[observationSigma r j] (fun z => ‖y‖^4*(Z*coulombKernel y-potentialOf
      (conditionalPacketDensity P Prod.fst (tailObservation r j) g c r₀ s (tailObservation r j z)) y)) :=
  measurable_const.mul (measurable_const.sub
    ((measurable_conditionalPacketPotential_data P Prod.fst (tailObservation r j) hg hgs hm hc hr₀ hs y).comp
      (measurable_tailObservation_for_sigma r j)))
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorBandOscillation
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem posterior_count_cap_oscillation {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ,0 < C ∧ ∀ {Ω Data : Type*} [MeasurableSpace Ω] [MeasurableSpace Data] {n : ℕ}
      (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → Data)
      (g : Position → ℝ),Continuous g → HasCompactSupport g → (∫ z,g z^2)=1 →
      ∀ {c r₀ s : ℝ},0 < c → 0 < r₀ → 0 < s → ∀ (datum : Data) (Z r L τ : ℝ),
      0 < r → 1 ≤ L → 0 < τ → τ ≤ r →
      (∀ y,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r →
        conditionalPacketDensity P raw obs g c r₀ s datum y ≤ (B/τ^3)*(K/r^3)) →
      (∀ y,3*r/4 ≤ ‖y‖ → ‖y‖ ≤ 6*L*r →
        ‖y‖^4*(Z*coulombKernel y-potentialOf
          (conditionalPacketDensity P raw obs g c r₀ s datum) y) ≤ physicalSpatialCap) →
      ∀ y z : Position,r ≤ ‖y‖ → ‖y‖ ≤ 4*L*r → ‖z-y‖ ≤ r/16 →
        let F := fun x => Z*coulombKernel x-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) x
        ‖F z-F y‖ ≤ C*(‖z-y‖/r)*((r/τ)^3/r^4+max (-F y) 0) := by
  obtain ⟨C,hC,H⟩ := atomic_band_negative_oscillation (mul_nonneg hB hK)
    (by have := physicalSpatialCap_pos; positivity : 0 ≤ 16*physicalSpatialCap)
  refine ⟨C,hC,?_⟩
  intro Ω Data mΩ mData n P hP raw obs g hg hgs hm c r₀ s hc hr₀ hs datum Z r L τ hr hL hτ hτr hden hcap y z hy0 hy1 hz
  let ρ := conditionalPacketDensity P raw obs g c r₀ s datum
  have hi : Integrable ρ := mixturePacketDensity_integrable hg hm hc hr₀ hs _
  have hmeas : Measurable ρ := mixturePacketDensity_measurable _ hg hc hr₀ hs
  have hp : ∀ x,0 ≤ ρ x := conditionalPacketDensity_nonneg P raw obs g hc hr₀ hs datum
  obtain ⟨A,hA,HA⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr₀ hs
  have hlam : 1 ≤ (r/τ)^3 := one_le_pow₀ ((le_div_iff₀ hτ).mpr (by simpa using hτr))
  have hρ (x) (hx0 : 3*r/4 ≤ ‖x‖) (hx1 : ‖x‖ ≤ 6*L*r) : ρ x ≤ (r/τ)^3*((B*K)/r^6) := by
    have hh := hden x (by linarith) (by nlinarith [mul_nonneg (by linarith : 0 ≤ L) hr.le])
    apply hh.trans_eq
    field_simp
  have hcapPos := physicalSpatialCap_pos
  have hF (x) (hx0 : 3*r/4 ≤ ‖x‖) (hx1 : ‖x‖ ≤ 6*L*r) :
      Z*coulombKernel x-potentialOf ρ x ≤ (r/τ)^3*((16*physicalSpatialCap)/r^4) := by
    have hxn : 0 < ‖x‖ := by linarith
    have hpow : (r/2)^4 ≤ ‖x‖^4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hhalf : physicalSpatialCap/‖x‖^4 ≤ physicalSpatialCap/(r/2)^4 :=
      div_le_div_of_nonneg_left physicalSpatialCap_pos.le (by positivity) hpow
    calc
      _ ≤ physicalSpatialCap/‖x‖^4 := (le_div_iff₀ (pow_pos hxn 4)).mpr (by simpa only [mul_comm] using hcap x hx0 hx1)
      _ ≤ physicalSpatialCap/(r/2)^4 := hhalf
      _ = (16*physicalSpatialCap)/r^4 := by ring
      _ ≤ (r/τ)^3*((16*physicalSpatialCap)/r^4) := le_mul_of_one_le_left (by positivity) hlam
  exact H ρ Z r L ((r/τ)^3) hi hmeas hp ⟨A,HA datum⟩
    (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr₀ hs datum)
    hr hL hlam hρ hF y z hy0 hy1 hz
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PhysicalSimultaneousInverse
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_simultaneous_inverse (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {c L hl hh ξ : ℝ} (hc : 0 < c) (hL : 1 ≤ L)
    (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
    ∃ C : ℝ,0 < C ∧ ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
    ∀ (j : Fin J),r₀*2^j.val ≤ s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun k : Fin J => r₀*2^k.val
    ∃ G : Set (ObservationSample (N+1) J),
      (MeasurableSet G ∧ MeasurableSet[observationSigma r j.val] G) ∧
      P.real Gᶜ ≤ C*(r j)^25 ∧ ∀ a∈G,∀ y : Position,r j ≤ ‖y‖ → ‖y‖ ≤ 4*L*(r j) →
      ∀ h∈Icc hl hh,
        let μ := conditionalPacketDensity P Prod.fst (tailObservation r j.val) g₀ c r₀ s
          (tailObservation r j.val a)
        let F := (Z:ℝ)*coulombKernel y-potentialOf μ y
        (Coulomb.tfScalarDensity h ≤ ‖y‖^6*μ y → h-ξ ≤ ‖y‖^4*F) ∧
        (‖y‖^6*μ y ≤ Coulomb.tfScalarDensity h → ‖y‖^4*F ≤ h+ξ) := by
  obtain ⟨K,hK,Hcount⟩ := physical_observed_small_annular_count_tail
    (by norm_num : (0:ℝ) < 1/8) (by norm_num : (1/8:ℝ) < 1/4)
    (by linarith : (1/4:ℝ) < 12*L) (by linarith : 12*L < 13*L)
  obtain ⟨B,T,hB,hT,Hreg⟩ := physical_posterior_band_event g₀ hg
  obtain ⟨Co,hCo,Hosc⟩ := posterior_count_cap_oscillation hB hK.le
  obtain ⟨heights,hhband,hheights⟩ := exists_height_brackets hξ hξl hlh
  obtain ⟨ε,hε,hmargin⟩ := exists_density_mesh_margin hξ hξl hlh
  obtain ⟨Cp,hCp,Hcap⟩ := physical_retained_spatial_cap hL
  let A := (4*L)^4*Co+4*(4*L)^3*max physicalSpatialCap 1
  let B' := (4*L)^6*(T*K)+6*(4*L)^5*(B*K)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  let C := 1+Cp+2*(12*L+1)^3*(heights.card:ℝ)
  have hC : 0 < C := by
    change 0 < 1+Cp+2*(12*L+1)^3*(heights.card:ℝ)
    have hlast : 0 ≤ 2*(12*L+1)^3*(heights.card:ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _)) (Nat.cast_nonneg _)
    linarith
  refine ⟨C,hC,?_⟩
  intro D hD
  obtain ⟨sc,hsc,Hc⟩ := Hcount D hD
  obtain ⟨sp,hsp,hsp1,Hp⟩ := physical_normalized_inverse_point g₀ hg hm hrad hD hc hL hK.le
    (by positivity : 0 < ξ/2) (show ξ/2 < hl/2 by linarith)
    (show hl/2 ≤ 2*hh by linarith)
  obtain ⟨sn,hsn,hsn16,Hn⟩ := exists_simultaneous_inverse_scale (L:=L) (D:=D) (A:=A) (B:=B') hc hξ hε
  let s₀ := min sc (min sp sn)
  have hs₀sc : s₀ ≤ sc := min_le_left _ _
  have hs₀sp : s₀ ≤ sp := (min_le_right _ _).trans (min_le_left _ _)
  have hs₀sn : s₀ ≤ sn := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨s₀,lt_min hsc (lt_min hsp hsn),(hs₀sn.trans hsn16).trans (by norm_num),?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss j hrs
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun k => r₀*2^k.val
  let R := r j
  have hR : 0 < R := by dsimp [R,r]; positivity
  have hR₀ : r₀ ≤ R := le_mul_of_one_le_right hr₀.le (one_le_pow₀ (by norm_num))
  have hRs : R ≤ s := hrs
  have hsns : s < sn := hss.trans_le hs₀sn
  have hRn : R < sn := hRs.trans_lt hsns
  have hR16 : R ≤ 1/16 := hRn.le.trans hsn16
  have hR1 : R ≤ 1 := hR16.trans (by norm_num)
  obtain ⟨hscale,hwidth,hsA,hsD,_,_,_,_,_⟩ := Hn hs hsns
  obtain ⟨_,_,_,_,hnoise,hτr,hAr,hAl,hBD⟩ := Hn hR hRn
  have hw100 : c*s^packetExponent ≤ 1/100 := by linarith
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun z hz => hg z
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  let obs := tailObservation (n:=N+1) r j.val
  let μ := fun a => conditionalPacketDensity P Prod.fst obs g₀ c r₀ s (obs a)
  let d := fun a y => ‖y‖^6*μ a y
  let u := fun a y => ‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf (μ a) y)
  let O := {x : Position | R/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*R}
  let cnt : ObservationSample (N+1) J → ℝ := fun a => rawCount O (observedOrdered r j a)
  have hO : MeasurableSet O := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hcnt : Measurable[observationSigma r j.val] cnt := measurable_observed_count_tail r j le_rfl hO
  have hdmeas : ∀ y,Measurable[observationSigma r j.val] (fun a => d a y) :=
    measurable_normalized_posterior_density_tail P r j.val g₀.continuous hc hr₀ hs
  have humeas : ∀ y,Measurable[observationSigma r j.val] (fun a => u a y) :=
    measurable_normalized_posterior_field_tail P r j.val g₀.continuous hgs hm hc hr₀ hs (Z:ℝ)
  obtain ⟨t,ht,hcover,hcard⟩ := exists_atomic_band_mesh hL hR hR1
  have hp (y : Position) (hy : y∈t) (h : ℝ) (hh' : h∈heights) :
      P.real {a | cnt a ≤ K/R^3 ∧ Coulomb.tfScalarDensity h ≤ d a y ∧ u a y ≤ h-(ξ/2)/4} ≤ R^42 ∧
      P.real {a | cnt a ≤ K/R^3 ∧ d a y ≤ Coulomb.tfScalarDensity h ∧ h+(ξ/2)/4 ≤ u a y} ≤ R^42 := by
    exact Hp Z hZ hd hn hmin hE hbase hr₀ hs (hss.trans_le hs₀sp) hscale hw100
      (by nlinarith only [hsA,hL,hs] : (4*L/100000)*s ≤ 1) j hrs hnoise y (ht y hy).1 (ht y hy).2 h (hhband h hh')
  obtain ⟨Gm,hGm,hmp,Hm⟩ := finite_inverse_mesh_event (observationSigma r j.val)
    (observationSigma_le r j.val) P t heights cnt d u hcnt hdmeas humeas hp
  obtain ⟨Gr,hGr,hrp,Hr⟩ := Hreg (rawLaw ψ) hc hr₀ hs hR hL hR₀ hRs hscale hw100
    r (fun k => by dsimp [r]; positivity) j le_rfl hnoise
  obtain ⟨Gp,hGp,hpp,Hp'⟩ := Hcap g₀ hg hm hrad Z hZ hd hn hmin hE hbase hD hc hr₀ hs
    (by linarith only [hscale]) (by nlinarith only [hwidth]) hsA hsD j.val hrs
  let Gc := {a | cnt a ≤ K/R^3}
  have hGct : MeasurableSet[observationSigma r j.val] Gc := measurableSet_le hcnt measurable_const
  have hGc : MeasurableSet Gc := (observationSigma_le r j.val) _ hGct
  have hcp : P.real Gcᶜ ≤ R^40 := by
    have H := Hc Z hZ hd hn hmin hE hbase r j hR (hRs.trans_lt (hss.trans_le hs₀sc))
    simpa only [Gc,Set.compl_ofPred,not_le,cnt,O,R,P,one_div_mul_eq_div] using H
  let G := Gc ∩ (Gp ∩ (Gr ∩ Gm))
  refine ⟨G,⟨hGc.inter (hGp.1.inter (hGr.1.inter hGm.1)),
    hGct.inter (hGp.2.inter (hGr.2.inter hGm.2))⟩,?_,?_⟩
  · have hrp' : P.real Grᶜ=0 := by
      change ((observationLaw J (rawLaw ψ)) Grᶜ).toReal=0
      rw [hrp,ENNReal.toReal_zero]
    have HU (A B : Set (ObservationSample (N+1) J)) :
        P.real (A∩B)ᶜ ≤ P.real Aᶜ+P.real Bᶜ := by
      rw [compl_inter]
      exact measureReal_union_le _ _
    have H := (HU Gc (Gp ∩ (Gr ∩ Gm))).trans
      (add_le_add hcp ((HU Gp (Gr ∩ Gm)).trans
        (add_le_add hpp ((HU Gr Gm).trans (add_le_add (le_of_eq hrp') hmp)))))
    have H' : P.real Gᶜ ≤ R^40+Cp*R^249+2*(t.card:ℝ)*(heights.card:ℝ)*R^42 := by
      simpa only [zero_add,←add_assoc] using H
    exact H'.trans (mesh_exception_probability_scale hR hR1 hL hCp.le
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcard)
  · intro a ha y hy0 hy1 h hh'
    have hcnta : cnt a ≤ K/R^3 := ha.1
    have hrega := Hr a ha.2.2.1
    let τ := c*(R/3)*(R/3)^packetExponent
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have hden : ∀ y,R/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*R → μ a y ≤ (B/τ^3)*(K/R^3) := by
      intro y hy0 hy1
      exact (hrega.1 y hy0 hy1).trans (mul_le_mul_of_nonneg_left hcnta (by positivity))
    have hlip : ∀ y z,R/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*R → R/2 ≤ ‖z‖ → ‖z‖ ≤ 8*L*R →
        |μ a z-μ a y| ≤ (T/τ^4)*‖z-y‖*(K/R^3) := by
      intro y z hy0 hy1 hz0 hz1
      exact (hrega.2 z y hz0 hz1 hy0 hy1).trans (mul_le_mul_of_nonneg_left hcnta (by positivity))
    have hcapa := Hp' a ha.2.1
    have hosca := Hosc P Prod.fst obs g₀ g₀.continuous hgs hm hc hr₀ hs (obs a) (Z:ℝ) R L τ
      hR hL hτ hτr hden hcapa
    have hmesh (y : Position) (hy : y∈{y : Position | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4*L*R}) :
        ∃ z∈t,|d a z-d a y| ≤ ε ∧ |u a z-u a y| ≤ (A*R)*((R/τ)^3+max (-u a y) 0) := by
      obtain ⟨z,hz,hdist⟩ := hcover y hy.1 hy.2
      have hdist' : ‖z-y‖ ≤ R^2 := by simpa only [norm_sub_rev] using hdist
      have HH := posterior_mesh_modulus P Prod.fst obs g₀ hc hr₀ hs (obs a) (Z:ℝ)
        hR hL hτ hτr hR16 hB hT hK.le hCo.le hden hlip hcapa hosca
        hy.1 hy.2 (ht z hz).1 (ht z hz).2 hdist'
      exact ⟨z,hz,HH.1.trans hBD,HH.2⟩
    exact inverse_of_space_height_mesh hξ hξl hε (mul_nonneg hA hR.le) hAr hAl
      (by positivity : 0 < (ξ/2)/4) (by linarith) hheights hmargin hmesh
      (Hm a ha.2.2.2 hcnta) y ⟨hy0,hy1⟩ h hh'
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationConstants
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
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

theorem physical_propagation_good_events_oai (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1<‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {c B C : ℝ} (hc : 0 < c) (hB : 0<B) (hBC : B ≤ C) (hcapC : physicalSpatialCap ≤ C)
    (k : PropagationConstants B C) :
    ∃ K : ℝ,0<K ∧ ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ {s : ℝ},0 < s → s < s₀ → c*(1+packetExponent)*s^packetExponent ≤ 1/2 ∧
        c*s^packetExponent ≤ 1/4 ∧ D*s^7 ≤ 1) ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
    ∀ (j : Fin J),r₀*2^j.val  ≤  s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let rs := fun l : Fin J => r₀*2^l.val
    ∃ G : Set (ObservationSample (N+1) J),
      (MeasurableSet G ∧ MeasurableSet[observationSigma rs j.val] G) ∧
      P.real Gᶜ ≤ K*(rs j)^24 ∧
      ∀ o∈G,∀ x : Position,rs j ≤ ‖x‖ → ‖x‖ ≤ 4*k.L*(rs j) →
        let μ := conditionalPacketDensity P Prod.fst (tailObservation rs j.val) g₀ c r₀ s (tailObservation rs j.val o)
        let F := (Z:ℝ)*coulombKernel x-potentialOf μ x
        F ≤ C/‖x‖^4 ∧ ∀ h∈Icc (B/2) C,
          (Coulomb.tfScalarDensity h ≤ ‖x‖^6*μ x → h-k.ξ ≤ ‖x‖^4*F) ∧
          (‖x‖^6*μ x ≤ Coulomb.tfScalarDensity h → ‖x‖^4*F ≤ h+k.ξ) := by
  have hL : 1 ≤ k.L := by linarith [k.L_large]
  obtain ⟨Ki,hKi,Hi⟩ := physical_simultaneous_inverse g₀ hg hm hrad hc hL k.xi_pos k.xi_lt_height
    (show B/2 ≤ C by linarith)
  obtain ⟨Kc,hKc,Hc⟩ := physical_retained_spatial_cap hL
  refine ⟨Ki+Kc,add_pos hKi hKc,?_⟩
  intro D hD
  obtain ⟨si,hsi,hsi1,Hi⟩ := Hi D hD
  obtain ⟨sn,hsn,hsn16,Hn⟩ := exists_simultaneous_inverse_scale (L:=k.L) (D:=D) (A:=0) (B:=0)
    hc k.xi_pos (by norm_num : (0:ℝ)<1)
  have ht : Tendsto (fun s : ℝ => D*s^7) (𝓝[>] 0) (𝓝 0) := by
    convert ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 7).const_mul D using 1 <;> simp
  obtain ⟨sd,hsd,Hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)))
  let s₀ := min si (min sn sd)
  have hsi' : s₀ ≤ si := min_le_left _ _
  have hsn' : s₀ ≤ sn := (min_le_right _ _).trans (min_le_left _ _)
  have hsd' : s₀ ≤ sd := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨s₀,lt_min hsi (lt_min hsn hsd),hsi'.trans hsi1,?_,?_⟩
  · intro s hs hss
    obtain ⟨h1,h2,-⟩ := Hn hs (hss.trans_le hsn')
    exact ⟨h1.trans (by norm_num),h2.trans (by norm_num),(Hd ⟨hs,hss.trans_le hsd'⟩).le⟩
  intro N J Z hZ ψ g hd hn hmin E hE he r₀ s hr₀ hs hss j hrjs
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let rs := fun l : Fin J => r₀*2^l.val
  have hrj : 0 < rs j := by dsimp [rs]; positivity
  have hrj1 : rs j ≤ 1 := hrjs.trans (hss.le.trans (hsi'.trans hsi1))
  obtain ⟨h1,h2,h3,h4,-⟩ := Hn hs (hss.trans_le hsn')
  obtain ⟨Gi,hGi,hPi,HI⟩ := Hi Z hZ hd hn hmin hE he hr₀ hs (hss.trans_le hsi') j hrjs
  obtain ⟨Gc,hGc,hPc,HC⟩ := Hc g₀ hg hm hrad Z hZ hd hn hmin hE he hD hc hr₀ hs
    (h1.trans (by norm_num)) (by linarith only [h2]) h3 h4 j.val hrjs
  refine ⟨Gi∩Gc,⟨hGi.1.inter hGc.1,hGi.2.inter hGc.2⟩,?_,?_⟩
  · rw [compl_inter]
    calc
      _ ≤ P.real Giᶜ+P.real Gcᶜ := measureReal_union_le _ _
      _ ≤ Ki*(rs j)^25+Kc*(rs j)^249 := add_le_add hPi hPc
      _ ≤ Ki*(rs j)^24+Kc*(rs j)^24 := add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hrj.le hrj1 (by decide)) hKi.le)
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hrj.le hrj1 (by decide)) hKc.le)
      _=(Ki+Kc)*(rs j)^24 := by ring
  · intro o ho x hx hx'
    refine ⟨?_,HI o ho.1 x hx hx'⟩
    have H := HC o ho.2 x (by linarith) (by
      have hpos : 0 ≤ k.L*(rs j) := mul_nonneg (by linarith [k.L_large]) hrj.le
      dsimp only [rs] at hx' hpos ⊢; linarith only [hx',hpos])
    apply (le_div_iff₀ (pow_pos (hrj.trans_le hx) 4)).mpr
    simpa only [mul_comm] using H.trans hcapC
end NeutralAtom
end

end

end OAI
end

theorem solution : type_of% @OAI.NeutralAtom.physical_propagation_good_events_oai := @OAI.NeutralAtom.physical_propagation_good_events_oai
