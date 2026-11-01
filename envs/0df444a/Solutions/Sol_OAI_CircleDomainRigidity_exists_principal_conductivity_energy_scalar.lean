-- Prove2me | solution 1 for OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:49:54.583276+00:00
-- url     : https://prove2.me/submissions/e7d61c05-0d79-4909-b3d8-d5184565b86f

import Mathlib
import Definitions.Def_Q146C008
import Theorems.Thm_OAI_CircleDomainRigidity_PlaneLocalWeakComplex_jacobian_area_limit

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundCircleParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positively sized round disk and its once-traversed regular
boundary, used to specialize the published Green identity to a disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem roundDiskChart_interior (R : ℝ) (hR : 0 < R) :
    jordanInterior (roundDiskChart R hR) = ball (0 : ℂ) R := by
  have hn : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ball, dist_zero_right]
    change ‖(R : ℂ)*w‖ < R
    rw [norm_mul, hn]
    have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    nlinarith
  · intro hz
    have hz' : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
    refine ⟨z/(R : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      change ‖z/(R : ℂ)‖ < 1
      rw [norm_div, hn]
      exact (div_lt_one hR).mpr hz'
    · change (R : ℂ)*(z/(R : ℂ)) = z
      exact mul_div_cancel₀ z hRc

 theorem unitCircleParam_hasDerivAt (R t : ℝ) :
    HasDerivAt (unitCircleParam 0 R)
      (circleMap 0 R (2*Real.pi*t) * Complex.I * (2*Real.pi)) t := by
  change HasDerivAt (fun s : ℝ => circleMap 0 R (2*Real.pi*s)) _ t
  convert (hasDerivAt_circleMap 0 R (2*Real.pi*t)).scomp t
    ((hasDerivAt_id t).const_mul (2*Real.pi)) using 1 <;>
    (try simp only [Function.comp_def, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_one]) <;>
    first | rfl | ring


 theorem unitCircleParam_regular (R : ℝ) (hR : 0 < R) :
    RegularJordanParametrization (roundDiskChart R hR) (unitCircleParam 0 R) := by
  have hp : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_circleMap 0 R).comp (contDiff_const.mul contDiff_id)
  · intro t
    change circleMap 0 R (2*Real.pi*(t+1)) = circleMap 0 R (2*Real.pi*t)
    rw [show 2*Real.pi*(t+1) = 2*Real.pi*t + 2*Real.pi by ring]
    exact periodic_circleMap 0 R _
  · intro a ha b hb heq
    apply (mul_left_cancel₀ hp.ne')
    apply injOn_circleMap_of_abs_sub_le' hR.ne' (a := 0) (b := 2*Real.pi) (by simp)
    · exact ⟨mul_nonneg hp.le ha.1, by nlinarith [ha.2]⟩
    · exact ⟨mul_nonneg hp.le hb.1, by nlinarith [hb.2]⟩
    · exact heq
  · intro t
    rw [(unitCircleParam_hasDerivAt R t).deriv]
    exact mul_ne_zero (mul_ne_zero (circleMap_ne_center hR.ne') Complex.I_ne_zero)
      (by exact_mod_cast hp.ne')
  · rw [roundDiskChart_interior, frontier_ball (0 : ℂ) hR.ne']
    apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      have hm : unitCircleParam 0 R t ∈ range (circleMap 0 R) := ⟨2*Real.pi*t, rfl⟩
      simpa only [range_circleMap, abs_of_pos hR] using hm
    · intro z hz
      have hz' : z ∈ circleMap 0 R '' Ioc 0 (2*Real.pi) := by
        simpa only [image_circleMap_Ioc, abs_of_pos hR] using hz
      obtain ⟨t, ht, rfl⟩ := hz'
      refine ⟨t/(2*Real.pi), ⟨le_of_lt (div_pos ht.1 hp), (div_le_one hp).mpr ht.2⟩, ?_⟩
      change circleMap 0 R (2*Real.pi*(t/(2*Real.pi))) = circleMap 0 R t
      rw [mul_div_cancel₀ t hp.ne']

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CircleFluxStability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform perturbation of the boundary values changes vertical flux
by at most the circle length times that perturbation. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem unitCircleParam_deriv_norm {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    ‖deriv (unitCircleParam 0 R) t‖ = 2*Real.pi*R := by
  rw [(unitCircleParam_hasDerivAt R t).deriv]
  simp only [norm_mul, norm_circleMap_zero, abs_of_nonneg hR, Complex.norm_I,
    mul_one, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

 theorem unitCircleParam_deriv_continuous (R : ℝ) :
    Continuous (deriv (unitCircleParam 0 R)) := by
  have heq : deriv (unitCircleParam 0 R) =
      fun t => circleMap 0 R (2*Real.pi*t) * Complex.I * (2*Real.pi) := by
    funext t
    exact (unitCircleParam_hasDerivAt R t).deriv
  rw [heq]
  exact (((continuous_circleMap 0 R).comp (continuous_const.mul continuous_id)).mul
    continuous_const).mul continuous_const

 theorem vertical_circle_flux_stability {F G : ℂ → ℂ} {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hF : Continuous (fun t => F (unitCircleParam 0 R t)))
    (hG : Continuous (fun t => G (unitCircleParam 0 R t)))
    (hbound : ∀ t : ℝ, ‖F (unitCircleParam 0 R t) - G (unitCircleParam 0 R t)‖ ≤ ε) :
    |planarFormIntegral (fun z => -(F z).im) (fun _ => 0) (unitCircleParam 0 R) -
      planarFormIntegral (fun z => -(G z).im) (fun _ => 0) (unitCircleParam 0 R)| ≤
      2*Real.pi*R*ε := by
  have hd := Complex.continuous_re.comp (unitCircleParam_deriv_continuous R)
  have hf : IntervalIntegrable (fun t => -(F (unitCircleParam 0 R t)).im *
      (deriv (unitCircleParam 0 R) t).re) volume 0 1 :=
    ((Complex.continuous_im.comp hF).neg.mul hd).intervalIntegrable 0 1
  have hg : IntervalIntegrable (fun t => -(G (unitCircleParam 0 R t)).im *
      (deriv (unitCircleParam 0 R) t).re) volume 0 1 :=
    ((Complex.continuous_im.comp hG).neg.mul hd).intervalIntegrable 0 1
  simp only [planarFormIntegral, zero_mul, add_zero]
  rw [← intervalIntegral.integral_sub hf hg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := 2*Real.pi*R*ε) (fun t _ht => show
      ‖-(F (unitCircleParam 0 R t)).im * (deriv (unitCircleParam 0 R) t).re -
        -(G (unitCircleParam 0 R t)).im * (deriv (unitCircleParam 0 R) t).re‖ ≤ _ from by
      have heq : -(F (unitCircleParam 0 R t)).im * (deriv (unitCircleParam 0 R) t).re -
          -(G (unitCircleParam 0 R t)).im * (deriv (unitCircleParam 0 R) t).re =
          -(F (unitCircleParam 0 R t)-G (unitCircleParam 0 R t)).im *
            (deriv (unitCircleParam 0 R) t).re := by
        simp only [Complex.sub_im]
        ring
      rw [heq, norm_mul, norm_neg]
      have h1 := mul_le_mul (Complex.abs_im_le_norm (F (unitCircleParam 0 R t)-G (unitCircleParam 0 R t)))
        (Complex.abs_re_le_norm (deriv (unitCircleParam 0 R) t))
        (abs_nonneg _) (norm_nonneg _)
      have h2 := mul_le_mul (hbound t) (le_of_eq (unitCircleParam_deriv_norm hR t))
        (norm_nonneg _) hε
      exact h1.trans (h2.trans_eq (by ring)))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, one_mul, mul_one] using hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityAlgebra
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and complex forms of the two-dimensional conductivity system.
These pointwise identities retain the signs and normalization used in the
Dirichlet-energy argument. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem conductivity_jacobian {k aX aY vX vY : ℝ}
    (hx : aX = k * vY) (hy : aY = -k * vX) :
    aX * vY - aY * vX = k * (vX ^ 2 + vY ^ 2) := by
  rw [hx, hy]
  ring

 theorem conductivity_energy_identity {k aX aY vX vY : ℝ}
    (hx : aX = k * vY) (hy : aY = -k * vX) :
    vX ^ 2 + (vY - 1) ^ 2 + (k - 1) * (vX ^ 2 + vY ^ 2) =
      (aX * vY - aY * vX) - 2 * vY + 1 := by
  rw [conductivity_jacobian hx hy]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityLocalEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite-disk energy balance for the constructed conductivity
system. The Jacobian and the vertical boundary flux remain explicit;
neither is replaced by an assumed energy estimate. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace PlaneLocalWeakComplex

 theorem conductivity_local_energy_balance {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) (R : ℝ) {F : Set EuclideanPlane}
    (hF : MeasurableSet F) (n : ℕ)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) :
    (∫ x in Metric.ball 0 R,
      (D.imagGradient x 0) ^ 2 + (D.imagGradient x 1 - 1) ^ 2) +
      ((n : ℝ) - 1) * (∫ x in Metric.ball 0 R ∩ F,
        (D.imagGradient x 0) ^ 2 + (D.imagGradient x 1) ^ 2) =
    (∫ x in Metric.ball 0 R,
      D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0) -
      2 * (∫ x in Metric.ball 0 R, D.imagGradient x 1) +
      (volume (Metric.ball (0 : EuclideanPlane) R)).toReal := by
  classical
  let B : Set EuclideanPlane := Metric.ball 0 R
  let μ := volume.restrict B
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let E : EuclideanPlane → ℝ := fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2
  let H : EuclideanPlane → ℝ := fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2
  let J : EuclideanPlane → ℝ := fun x =>
    D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0
  have hE : Integrable E μ := (D.imag_memLp R 0).integrable_sq.add
    (D.imag_memLp R 1).integrable_sq
  have hH : Integrable H μ := (D.imag_memLp R 0).integrable_sq.add
    ((D.imag_memLp R 1).sub (memLp_const 1)).integrable_sq
  have hI : Integrable (F.indicator E) μ := hE.indicator hF
  have hv : Integrable (fun x => D.imagGradient x 1) μ :=
    (D.imag_memLp R 1).integrable (by norm_num)
  have he : J =ᵐ[μ] fun x => H x + ((n : ℝ)-1) * F.indicator E x +
      2 * D.imagGradient x 1 - 1 := by
    filter_upwards [ae_restrict_of_ae hsys] with x hx
    have hh := conductivity_energy_identity hx.1 hx.2
    have ht : (conductivityValue F n x - 1) * E x = ((n : ℝ)-1) * F.indicator E x := by
      by_cases hxF : x ∈ F <;> simp [conductivityValue, hxF]
    change H x + (conductivityValue F n x - 1) * E x = J x - 2 * D.imagGradient x 1 + 1 at hh
    rw [ht] at hh
    linarith
  have hJI : (∫ x, J x ∂μ) = (∫ x, H x ∂μ) + ((n : ℝ)-1) *
      (∫ x, F.indicator E x ∂μ) + 2 * (∫ x, D.imagGradient x 1 ∂μ) -
      (volume B).toReal := by
    have hsum₁ : Integrable (fun x => H x + ((n : ℝ)-1) * F.indicator E x) μ :=
      hH.add (hI.const_mul ((n : ℝ)-1))
    have hsum₂ : Integrable (fun x => H x + ((n : ℝ)-1) * F.indicator E x +
        2 * D.imagGradient x 1) μ := hsum₁.add (hv.const_mul 2)
    rw [integral_congr_ae he, integral_sub hsum₂ (integrable_const 1),
      integral_add hsum₁ (hv.const_mul 2),
      integral_add hH (hI.const_mul ((n : ℝ)-1)), integral_const_mul, integral_const_mul]
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real, μ, Measure.restrict_apply_univ]
  have hIeq : (∫ x, F.indicator E x ∂μ) = ∫ x in B ∩ F, E x := by
    rw [integral_indicator hF, Measure.restrict_restrict hF]
    rw [inter_comm]
  change (∫ x, H x ∂μ) + ((n : ℝ)-1) * (∫ x in B ∩ F, E x) =
    (∫ x, J x ∂μ) - 2 * (∫ x, D.imagGradient x 1 ∂μ) + (volume B).toReal
  rw [hJI, hIeq]
  ring

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityGlobalEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passage from the exact finite-ball conductivity identity to its
whole-plane version. The two geometric inputs remain separately visible:
the Jacobian area defect tends to zero, and the vertical flux defect tends
to minus pi times the real Laurent coefficient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace PlaneLocalWeakComplex

 theorem imag_energy_integrableOn_compact {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) {F : Set EuclideanPlane} (hF : IsCompact F) :
    IntegrableOn (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) F := by
  obtain ⟨R, hR⟩ := hF.isBounded.subset_ball 0
  have hh : IntegrableOn (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2)
      (Metric.ball 0 R) := (D.imag_memLp R 0).integrable_sq.add (D.imag_memLp R 1).integrable_sq
  exact hh.mono_set hR

 theorem conductivity_global_energy {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) {F : Set EuclideanPlane} (hF : IsCompact F)
    (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0)
    (harea : Tendsto (fun R : ℝ =>
      (∫ x in Metric.ball 0 R,
        D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0) -
        (volume (Metric.ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 0))
    (hflux : Tendsto (fun R : ℝ =>
      (∫ x in Metric.ball 0 R, D.imagGradient x 1) -
        (volume (Metric.ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 (-Real.pi * c))) :
    Integrable (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) ∧
    (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) +
      ((n : ℝ)-1) * (∫ x in F, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) =
        2 * Real.pi * c := by
  classical
  let H : EuclideanPlane → ℝ := fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2
  let E : EuclideanPlane → ℝ := fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2
  let A : EuclideanPlane → ℝ := fun x => H x + ((n : ℝ)-1) * F.indicator E x
  have hEF : IntegrableOn E F := D.imag_energy_integrableOn_compact hF
  have hI : Integrable (F.indicator E) := (integrable_indicator_iff hF.measurableSet).mpr hEF
  have hH (R : ℝ) : IntegrableOn H (Metric.ball 0 R) := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanPlane) R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact (D.imag_memLp R 0).integrable_sq.add
      ((D.imag_memLp R 1).sub (memLp_const 1)).integrable_sq
  have hA (R : ℝ) : IntegrableOn A (Metric.ball 0 R) :=
    (hH R).add ((hI.restrict).const_mul _)
  have hAn : ∀ x, 0 ≤ A x := by
    intro x
    have hi : 0 ≤ F.indicator E x := indicator_nonneg (fun y _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) x
    have hc : 0 ≤ (n : ℝ)-1 := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg hc hi)
  have heq (R : ℝ) : (∫ x in Metric.ball 0 R, A x) =
      ((∫ x in Metric.ball 0 R,
        D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0) -
        (volume (Metric.ball (0 : EuclideanPlane) R)).toReal) -
      2 * ((∫ x in Metric.ball 0 R, D.imagGradient x 1) -
        (volume (Metric.ball (0 : EuclideanPlane) R)).toReal) := by
    have hh := D.conductivity_local_energy_balance R hF.measurableSet n hsys
    change (∫ x in Metric.ball 0 R, H x) + ((n : ℝ)-1) * (∫ x in Metric.ball 0 R ∩ F, E x) = _ at hh
    change (∫ x in Metric.ball 0 R, H x + ((n : ℝ)-1) * F.indicator E x) = _
    rw [integral_add (hH R) ((hI.restrict).const_mul _), integral_const_mul,
      integral_indicator hF.measurableSet, Measure.restrict_restrict hF.measurableSet, inter_comm F]
    linarith [hh]
  have ht : Tendsto (fun R : ℝ => ∫ x in Metric.ball 0 R, A x) atTop
      (𝓝 (2 * Real.pi * c)) := by
    have hh := harea.sub (hflux.const_mul 2)
    simp only [zero_sub] at hh
    convert hh using 1
    · funext R
      exact heq R
    · congr 1
      ring
  have hcover : AECover volume atTop (fun R : ℝ => Metric.ball (0 : EuclideanPlane) R) :=
    aecover_ball tendsto_id
  have hAI : Integrable A := hcover.integrable_of_integral_tendsto_of_nonneg_ae
    (2 * Real.pi * c) hA (Eventually.of_forall hAn) ht
  have htotal : (∫ x, A x) = 2 * Real.pi * c := hcover.integral_eq_of_tendsto _ hAI ht
  have hHI : Integrable H := by
    have hh := hAI.sub (hI.const_mul ((n : ℝ)-1))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change H x = (H x + ((n : ℝ)-1) * F.indicator E x) - ((n : ℝ)-1) * F.indicator E x
    ring
  refine ⟨hHI, ?_⟩
  change (∫ x, H x) + ((n : ℝ)-1) * (∫ x in F, E x) = _
  rw [show (∫ x in F, E x) = ∫ x, F.indicator E x from (integral_indicator hF.measurableSet).symm]
  rw [← integral_const_mul, ← integral_add hHI (hI.const_mul _)]
  exact htotal

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalExteriorGerm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A holomorphic exterior map tending to the identity has an actual
principal Laurent germ. The first two divided differences give the
coefficient and the analytic remainder; no Laurent estimate is assumed. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem invertedPrincipalRemainder_analytic {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    AnalyticAt ℂ (invertedPrincipalRemainder F) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hd := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).eventually hF
    filter_upwards [hd, self_mem_nhdsWithin] with w hw hw0
    have hn : w ≠ 0 := hw0
    have hi : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := differentiableAt_inv hn
    have hh := (hw.comp w hi).sub hi
    apply hh.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hn] with z hz
    exact Function.update_of_ne hz _ _
  · exact continuousAt_update_same.mpr
      (ht.comp (tendsto_inv₀_nhdsNE_zero (α := ℂ)))

 theorem principal_exterior_expansion {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    ∃ (c : ℂ) (T : ℂ → ℂ), AnalyticAt ℂ T 0 ∧
      ∀ z : ℂ, z ≠ 0 → F z - z = c * z⁻¹ + z⁻¹ ^ 2 * T z⁻¹ := by
  let u := invertedPrincipalRemainder F
  have hu : AnalyticAt ℂ u 0 := invertedPrincipalRemainder_analytic hF ht
  have hu0 : u 0 = 0 := Function.update_self _ _ _
  let v := dslope u 0
  let T := dslope v 0
  have hv : AnalyticAt ℂ v 0 := analyticAt_dslope_zero hu
  refine ⟨v 0, T, analyticAt_dslope_zero hv, ?_⟩
  intro z hz
  have h1 : z⁻¹ * v z⁻¹ = u z⁻¹ := by
    simpa only [sub_zero, smul_eq_mul, hu0] using sub_smul_dslope u 0 z⁻¹
  have h2 : z⁻¹ * T z⁻¹ = v z⁻¹ - v 0 := by
    simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope v 0 z⁻¹
  have he : u z⁻¹ = F z - z := by
    dsimp only [u, invertedPrincipalRemainder]
    rw [Function.update_of_ne (inv_ne_zero hz), inv_inv]
  rw [he] at h1
  linear_combination -h1 - z⁻¹ * h2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactMollifierSampling
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform sampling control on compact sets, including exact preservation
of constant regions and smooth cutoffs equal to one near a compact set. -/

open Set Filter MeasureTheory Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem planarMollifier_samples_eventually
    {K V : Set EuclideanPlane} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∀ᶠ n in atTop, ∀x ∈ K,
      ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn x hx y hy
  apply hδV
  exact mem_cthickening_of_dist_le y x δ K hx
    ((mem_ball.1 hy).le.trans hn.le)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalMollificationCongruence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local almost-everywhere equality is preserved by mollification
where the actual averaging ball stays inside the equality region. -/
open Set Filter MeasureTheory Metric Function
open scoped Topology Convolution
noncomputable section
namespace CircleDomainRigidity

 theorem planarMollification_congr_on_ball {u v : EuclideanPlane → ℝ}
    {U : Set EuclideanPlane} (huv : ∀ᵐ y ∂volume, y ∈ U → u y = v y)
    (n : ℕ) (x : EuclideanPlane)
    (hball : ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut ⊆ U) :
    planarMollification u n x = planarMollification v n x := by
  let κ := (DeGiorgi.shrinkingBump (d := 2) n).normed volume
  have hflip (f : EuclideanPlane → ℝ) : planarMollification f n x =
      ∫ y, f y * κ (x-y) := by
    rw [planarMollification, ← convolution_flip]
    change (∫ y, κ (x-y) * f y) = _
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => mul_comm _ _)
  rw [hflip u, hflip v]
  apply integral_congr_ae
  filter_upwards [huv] with y hy
  by_cases hk : κ (x-y) = 0
  · rw [hk, mul_zero, mul_zero]
  · have hm : x-y ∈ support κ := hk
    rw [(DeGiorgi.shrinkingBump (d := 2) n).support_normed_eq] at hm
    have hd : y ∈ ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut := by
      simpa only [mem_ball, dist_eq_norm, sub_zero, norm_sub_rev] using hm
    rw [hy (hball hd)]

 theorem planarMollification_neg (u : EuclideanPlane → ℝ) (n : ℕ) :
    planarMollification (fun x => -u x) n = fun x => -planarMollification u n x := by
  funext x
  simp only [planarMollification, convolution, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_neg, integral_neg]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCauchyRiemann
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real Cauchy–Riemann equations in the actual physical plane
coordinates imply complex differentiability. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

 theorem differentiableAt_complex_of_real_linear {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z)
    (hI : fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1) :
    DifferentiableAt ℂ f z := by
  let A : ℂ →L[ℂ] ℂ := (fderiv ℝ f z 1) • ContinuousLinearMap.id ℂ ℂ
  apply (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt (f' := A) ?_).differentiableAt
  ext w
  change fderiv ℝ f z 1 * w = fderiv ℝ f z w
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_rhs => rw [hw, map_add, map_smul, map_smul, hI]
  simp only [Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im w]
  ring

 theorem complexifyPair_differentiableAt {a b : EuclideanPlane → ℝ} {x : EuclideanPlane}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hX : fderiv ℝ a x (EuclideanSpace.single 0 1) =
      fderiv ℝ b x (EuclideanSpace.single 1 1))
    (hY : fderiv ℝ a x (EuclideanSpace.single 1 1) =
      -fderiv ℝ b x (EuclideanSpace.single 0 1)) :
    DifferentiableAt ℂ (complexifyPair a b) (complexPlaneCoordinates x) := by
  have haa : HasFDerivAt a (fderiv ℝ a x)
      (complexPlaneCoordinates.symm (complexPlaneCoordinates x)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using ha.hasFDerivAt
  have hbb : HasFDerivAt b (fderiv ℝ b x)
      (complexPlaneCoordinates.symm (complexPlaneCoordinates x)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hb.hasFDerivAt
  have hax := haa.comp (complexPlaneCoordinates x) complexPlaneCoordinates.symm.hasFDerivAt
  have hbx := hbb.comp (complexPlaneCoordinates x) complexPlaneCoordinates.symm.hasFDerivAt
  have har := Complex.ofRealCLM.hasFDerivAt.comp _ hax
  have hbr := Complex.ofRealCLM.hasFDerivAt.comp _ hbx
  have hd := har.add (hbr.const_mul Complex.I)
  apply differentiableAt_complex_of_real_linear hd.differentiableAt
  rw [hd.fderiv]
  have h0 : complexPlaneCoordinates.symm (1 : ℂ) = EuclideanSpace.single 0 1 := by
    apply complexPlaneCoordinates.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    apply Complex.ext <;> simp [complexPlaneCoordinates_apply]
  have h1 : complexPlaneCoordinates.symm Complex.I = EuclideanSpace.single 1 1 := by
    apply complexPlaneCoordinates.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    apply Complex.ext <;> simp [complexPlaneCoordinates_apply]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearEquiv.coe_coe,
    Complex.ofRealCLM_apply, smul_eq_mul, h0, h1]
  rw [hX, hY]
  apply Complex.ext <;> simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalComplexWeyl
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Weyl lemma for the actual weak complex differential. Positive
mollification preserves the Cauchy–Riemann equations on smaller compact
sets, and locally uniform convergence identifies the holomorphic limit. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology Convolution
noncomputable section
namespace CircleDomainRigidity

 theorem complexifyPair_mollification_tendsto {a b : EuclideanPlane → ℝ}
    (ha : Continuous a) (hb : Continuous b) :
    TendstoLocallyUniformly
      (fun n => complexifyPair (planarMollification a n) (planarMollification b n))
      (complexifyPair a b) atTop := by
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hKi : IsCompact (complexPlaneCoordinates.symm '' K) := hK.image
    complexPlaneCoordinates.symm.continuous
  have hpa := planarMollification_uniform_on_compact ha.aestronglyMeasurable hKi
    isOpen_univ (subset_univ _) ha.continuousOn (half_pos hε)
  have hpb := planarMollification_uniform_on_compact hb.aestronglyMeasurable hKi
    isOpen_univ (subset_univ _) hb.continuousOn (half_pos hε)
  filter_upwards [hpa, hpb] with n hnA hnB z hz
  have hzi : complexPlaneCoordinates.symm z ∈ complexPlaneCoordinates.symm '' K :=
    mem_image_of_mem _ hz
  have he : complexifyPair a b z - complexifyPair (planarMollification a n)
      (planarMollification b n) z =
      ((a (complexPlaneCoordinates.symm z) - planarMollification a n (complexPlaneCoordinates.symm z) : ℝ) : ℂ) +
      Complex.I * ((b (complexPlaneCoordinates.symm z) - planarMollification b n (complexPlaneCoordinates.symm z) : ℝ) : ℂ) := by
    simp only [complexifyPair, Complex.ofReal_sub]
    ring
  rw [dist_eq_norm, he]
  apply lt_of_le_of_lt (norm_add_le _ _)
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (a _), abs_sub_comm (b _)]
  linarith [hnA _ hzi, hnB _ hzi]

namespace PlaneLocalWeakComplex

 theorem mollified_differentiableAt {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) (hf : Continuous f) {U : Set EuclideanPlane}
    (hcr : ∀ᵐ x ∂volume, x ∈ U →
      D.realGradient x 0 = D.imagGradient x 1 ∧ D.realGradient x 1 = -D.imagGradient x 0)
    (n : ℕ) (x : EuclideanPlane)
    (hball : ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut ⊆ U) :
    DifferentiableAt ℂ
      (complexifyPair (planarMollification (fun y => (f y).re) n)
        (planarMollification (fun y => (f y).im) n)) (complexPlaneCoordinates x) := by
  have ha : LocallyIntegrable (fun y => (f y).re) volume :=
    (Complex.continuous_re.comp hf).locallyIntegrable
  have hb : LocallyIntegrable (fun y => (f y).im) volume :=
    (Complex.continuous_im.comp hf).locallyIntegrable
  apply complexifyPair_differentiableAt
    ((planarMollification_smooth ha n).differentiable (by simp) x)
    ((planarMollification_smooth hb n).differentiable (by simp) x)
  · rw [planarMollification_derivative_of_weak ha 0 (D.real_weak 0),
      planarMollification_derivative_of_weak hb 1 (D.imag_weak 1)]
    exact planarMollification_congr_on_ball (hcr.mono fun y hy hyU => (hy hyU).1) n x hball
  · rw [planarMollification_derivative_of_weak ha 1 (D.real_weak 1),
      planarMollification_derivative_of_weak hb 0 (D.imag_weak 0)]
    change planarMollification (fun y => D.realGradient y 1) n x =
      -planarMollification (fun y => D.imagGradient y 0) n x
    calc
      _ = planarMollification (fun y => -D.imagGradient y 0) n x :=
        planarMollification_congr_on_ball (hcr.mono fun y hy hyU => (hy hyU).2) n x hball
      _ = _ := congrFun (planarMollification_neg (fun y => D.imagGradient y 0) n) x

 theorem holomorphic_on_of_cauchyRiemann {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) (hf : Continuous f) {U : Set EuclideanPlane} (hU : IsOpen U)
    (hcr : ∀ᵐ x ∂volume, x ∈ U →
      D.realGradient x 0 = D.imagGradient x 1 ∧ D.realGradient x 1 = -D.imagGradient x 0) :
    DifferentiableOn ℂ (fun z => f (complexPlaneCoordinates.symm z))
      (complexPlaneCoordinates '' U) := by
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let K := closedBall x (r/2)
  let V := complexPlaneCoordinates '' ball x (r/2)
  have hK : IsCompact K := isCompact_closedBall x (r/2)
  have hKU : K ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hsub
  have hV : IsOpen V := complexPlaneCoordinates.toHomeomorph.isOpenMap _ isOpen_ball
  have hxV : complexPlaneCoordinates x ∈ V :=
    mem_image_of_mem _ (mem_ball_self (half_pos hr))
  let fn (n : ℕ) := complexifyPair (planarMollification (fun y => (f y).re) n)
    (planarMollification (fun y => (f y).im) n)
  have hfn : ∀ᶠ n in atTop, DifferentiableOn ℂ (fn n) V := by
    filter_upwards [planarMollifier_samples_eventually hK hU hKU] with n hn
    rintro w ⟨y, hy, rfl⟩
    exact (D.mollified_differentiableAt hf hcr n y (hn y (ball_subset_closedBall hy))).differentiableWithinAt
  have hlim : TendstoLocallyUniformly fn (fun z => f (complexPlaneCoordinates.symm z)) atTop := by
    have hh := complexifyPair_mollification_tendsto
      (Complex.continuous_re.comp hf) (Complex.continuous_im.comp hf)
    apply hh.congr_right
    intro w
    apply Complex.ext <;> simp [complexifyPair]
  have hlimV : TendstoLocallyUniformlyOn fn (fun z => f (complexPlaneCoordinates.symm z)) atTop V :=
    (tendstoLocallyUniformlyOn_univ.mpr hlim).mono (subset_univ V)
  have hd := hlimV.differentiableOn hfn hV
  exact (hd.differentiableAt (hV.mem_nhds hxV)).differentiableWithinAt

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityExterior
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed principal conductivity homeomorphism is holomorphic
off its coefficient support. Its principal Laurent germ and uniform
exterior decay follow from the proved local Weyl lemma. -/
open Set Filter Function MeasureTheory Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.conductivity_holomorphic_off
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hφ : Continuous φ) {F : Set EuclideanPlane} (hF : IsClosed F) (n : ℕ)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) :
    DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ := by
  have hcr : ∀ᵐ x ∂volume, x ∈ Fᶜ →
      D.realGradient x 0 = D.imagGradient x 1 ∧ D.realGradient x 1 = -D.imagGradient x 0 := by
    filter_upwards [hsys] with x hx hxF
    simpa only [conductivityValue, ite_eq_right hxF, one_mul, neg_mul, one_mul] using hx
  have hh := D.holomorphic_on_of_cauchyRiemann (hφ.comp complexPlaneCoordinates.continuous)
    hF.isOpen_compl hcr
  simpa only [ContinuousLinearEquiv.apply_symm_apply,
    image_compl_eq complexPlaneCoordinates.bijective] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundDiskGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing signed Green input specializes to the positively
parametrized round disk. Its sign is determined by the radial one-form,
whose boundary integral and area integral are computed here. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem radial_form_unitCircleParam (R : ℝ) :
    planarFormIntegral (fun z => -z.im) (fun z => z.re) (unitCircleParam 0 R) =
      2 * Real.pi * R^2 := by
  have hi (t : ℝ) :
      -(unitCircleParam 0 R t).im * (deriv (unitCircleParam 0 R) t).re +
      (unitCircleParam 0 R t).re * (deriv (unitCircleParam 0 R) t).im = 2*Real.pi*R^2 := by
    rw [(unitCircleParam_hasDerivAt R t).deriv]
    simp only [unitCircleParam, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, mul_one, sub_zero, add_zero,
      zero_add, circleMap_zero_re, circleMap_zero_im]
    calc
      _ = 2*Real.pi*R^2 * (Real.cos (2*Real.pi*t)^2 + Real.sin (2*Real.pi*t)^2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
  simp only [planarFormIntegral, hi, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]

 theorem round_disk_green (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) (O : Set ℂ) (hO : IsOpen O) (hRO : closedBall (0 : ℂ) R ⊆ O)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ (⊤ : ℕ∞) P O)
    (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q O) :
    planarFormIntegral P Q (unitCircleParam 0 R) =
      ∫ z in ball (0 : ℂ) R, fderiv ℝ Q z 1 - fderiv ℝ P z Complex.I := by
  obtain ⟨e, _he, hg⟩ := hgreen (roundDiskChart R hR) (unitCircleParam 0 R)
    (unitCircleParam_regular R hR)
  have specialize (O : Set ℂ) (hO : IsOpen O) (hsub : closedBall (0 : ℂ) R ⊆ O)
      (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ (⊤ : ℕ∞) P O)
      (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q O) :
      e * planarFormIntegral P Q (unitCircleParam 0 R) =
        ∫ z in ball (0 : ℂ) R, fderiv ℝ Q z 1 - fderiv ℝ P z Complex.I := by
    simpa only [roundDiskChart_interior, iUnion_of_empty, sdiff_empty, Finset.univ_eq_empty,
      Finset.sum_empty, sub_zero] using
      hg 0 Fin.elim0 Fin.elim0 (by intro i; exact Fin.elim0 i)
        (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
        O hO (by simpa only [roundDiskChart_interior, iUnion_of_empty, sdiff_empty,
          closure_ball (0 : ℂ) hR.ne'] using hsub) P Q hP hQ
  have he1 : e = 1 := by
    have hh := specialize univ isOpen_univ (subset_univ _) (fun z => -z.im) (fun z => z.re)
      Complex.imCLM.contDiff.neg.contDiffOn Complex.reCLM.contDiff.contDiffOn
    have hd (z : ℂ) : fderiv ℝ (fun w : ℂ => w.re) z 1 -
        fderiv ℝ (fun w : ℂ => -w.im) z Complex.I = 2 := by
      rw [fderiv_fun_neg]
      change fderiv ℝ Complex.reCLM z 1 - -(fderiv ℝ Complex.imCLM z Complex.I) = 2
      rw [Complex.reCLM.fderiv, Complex.imCLM.fderiv]
      norm_num
    simp_rw [hd] at hh
    rw [radial_form_unitCircleParam, integral_const] at hh
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
      real_volume_ball 0 hR.le] at hh
    have hpos : 0 < 2*Real.pi*R^2 := by positivity
    nlinarith
  simpa only [he1, one_mul] using specialize O hO hRO P Q hP hQ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalCircleFlux
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading principal Laurent terms give the exact first-order
outward flux on a round circle. Higher-order terms are estimated separately. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integral_unit_sin_sq :
    (∫ t in (0 : ℝ)..1, Real.sin (2*Real.pi*t)^2) = 1/2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x^2)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  simp only [mul_zero, mul_one, integral_sin_sq, Real.sin_zero, zero_mul,
    Real.sin_two_pi, sub_zero, mul_zero, zero_add, smul_eq_mul]
  field_simp

 theorem integral_unit_sin_cos :
    (∫ t in (0 : ℝ)..1, Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x*Real.cos x)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  simp [integral_sin_mul_cos₁, Real.sin_two_pi]

 theorem principal_leading_circle_flux (R : ℝ) (hR : 0 < R) (c : ℂ) :
    planarFormIntegral (fun z => -(z+c/z).im) (fun _ => 0) (unitCircleParam 0 R) =
      Real.pi*R^2-Real.pi*c.re := by
  have hnorm (t : ℝ) : Complex.normSq (circleMap 0 R t) = R^2 := by
    rw [Complex.normSq_eq_norm_sq]
    simp only [norm_circleMap_zero, abs_of_pos hR]
  have hi (t : ℝ) :
      -(unitCircleParam 0 R t + c/unitCircleParam 0 R t).im *
        (deriv (unitCircleParam 0 R) t).re + 0 * (deriv (unitCircleParam 0 R) t).im =
      2*Real.pi*R^2 * Real.sin (2*Real.pi*t)^2 +
        2*Real.pi*c.im * (Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) -
        2*Real.pi*c.re * Real.sin (2*Real.pi*t)^2 := by
    rw [(unitCircleParam_hasDerivAt R t).deriv]
    simp only [unitCircleParam, Complex.add_im, Complex.div_im, hnorm, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add,
      circleMap_zero_re, circleMap_zero_im]
    field_simp [hR.ne']
    ring
  have hs : IntervalIntegrable (fun t : ℝ => Real.sin (2*Real.pi*t)^2) volume 0 1 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2 |>.intervalIntegrable _ _
  have hc : IntervalIntegrable (fun t : ℝ => Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) volume 0 1 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  simp only [planarFormIntegral, hi]
  rw [intervalIntegral.integral_sub ((hs.const_mul _).add (hc.const_mul _)) (hs.const_mul _),
    intervalIntegral.integral_add (hs.const_mul _) (hc.const_mul _)]
  simp only [intervalIntegral.integral_const_mul, integral_unit_sin_sq,
    integral_unit_sin_cos, mul_zero, add_zero]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalCircleFluxLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual analytic principal germ gives the limiting vertical
boundary flux. No boundary estimate is assumed: continuity of the
analytic remainder supplies a uniform bound on inverse circles. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem inverse_circle_remainder_bound {T : ℂ → ℂ} (hT : ContinuousAt T 0) :
    ∃ B R₀ : ℝ, 0 ≤ B ∧ ∀ R ≥ R₀, 0 < R ∧
      ∀ t : ℝ, ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B := by
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hT 1 zero_lt_one
  refine ⟨‖T 0‖+1, max 1 (δ⁻¹+1), by positivity, ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  refine ⟨hRp, ?_⟩
  intro t
  have hn : ‖(unitCircleParam 0 R t)⁻¹‖ < δ := by
    rw [norm_inv]
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
    apply (inv_lt_comm₀ hRp hδ).mpr
    have hh := (le_max_right 1 (δ⁻¹+1)).trans hR
    linarith
  have he := hd (show dist ((unitCircleParam 0 R t)⁻¹) 0 < δ by
    simpa only [dist_zero_right] using hn)
  have hl : ‖T (unitCircleParam 0 R t)⁻¹-T 0‖ < 1 := by
    simpa only [dist_eq_norm] using he
  have ht := norm_add_le (T (unitCircleParam 0 R t)⁻¹-T 0) (T 0)
  rw [sub_add_cancel] at ht
  linarith

 theorem principal_circle_flux_estimate {F : ℂ → ℂ} (hF : Continuous F)
    {c : ℂ} {T : ℂ → ℂ}
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹)
    {B R : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    (hT : ∀ t : ℝ, ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B) :
    |planarFormIntegral (fun z => -(F z).im) (fun _ => 0) (unitCircleParam 0 R) -
      Real.pi*R^2 + Real.pi*c.re| ≤ 2*Real.pi*B/R := by
  have hn (t : ℝ) : ‖unitCircleParam 0 R t‖ = R := by
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
  have hne (t : ℝ) : unitCircleParam 0 R t ≠ 0 := by
    intro he
    have hh := hn t
    rw [he, norm_zero] at hh
    linarith
  have hb (t : ℝ) : ‖F (unitCircleParam 0 R t) -
      (unitCircleParam 0 R t+c/unitCircleParam 0 R t)‖ ≤ B/R^2 := by
    have he := hexp _ (hne t)
    have heq : F (unitCircleParam 0 R t) -
        (unitCircleParam 0 R t+c/unitCircleParam 0 R t) =
        (unitCircleParam 0 R t)⁻¹^2*T (unitCircleParam 0 R t)⁻¹ := by
      rw [div_eq_mul_inv]
      linear_combination he
    rw [heq, norm_mul, norm_pow, norm_inv, hn]
    calc
      _ ≤ R⁻¹^2*B := mul_le_mul_of_nonneg_left (hT t) (sq_nonneg _)
      _ = _ := by field_simp
  have hγ : Continuous (unitCircleParam 0 R) :=
    (continuous_circleMap 0 R).comp (continuous_const.mul continuous_id)
  have hfl := vertical_circle_flux_stability (G := fun z => z+c/z) hR.le (div_nonneg hB (sq_nonneg R))
    (hF.comp hγ) (hγ.add (continuous_const.div hγ hne)) hb
  rw [principal_leading_circle_flux R hR c] at hfl
  have heq : 2*Real.pi*R*(B/R^2) = 2*Real.pi*B/R := by field_simp
  rw [heq] at hfl
  convert hfl using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

 theorem principal_circle_flux_limit {F : ℂ → ℂ} (hF : Continuous F)
    {c : ℂ} {T : ℂ → ℂ} (hT : ContinuousAt T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
    Tendsto (fun R : ℝ =>
      planarFormIntegral (fun z => -(F z).im) (fun _ => 0) (unitCircleParam 0 R) -
        Real.pi*R^2) atTop (𝓝 (-Real.pi*c.re)) := by
  obtain ⟨B, R₀, hB, hb⟩ := inverse_circle_remainder_bound hT
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max R₀ (2*Real.pi*B/ε+1), ?_⟩
  intro R hR
  have hRR : R₀ ≤ R := (le_max_left _ _).trans hR
  obtain ⟨hRp, hTbound⟩ := hb R hRR
  have he := principal_circle_flux_estimate hF hexp hB hRp hTbound
  have hRlarge := (le_max_right R₀ (2*Real.pi*B/ε+1)).trans hR
  have hlt : 2*Real.pi*B/R < ε := by
    apply (div_lt_iff₀ hRp).mpr
    have hh : 2*Real.pi*B/ε < R := by linarith
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  rw [dist_eq_norm, Real.norm_eq_abs]
  calc
    _ = |planarFormIntegral (fun z => -(F z).im) (fun _ => 0) (unitCircleParam 0 R) -
        Real.pi*R^2 + Real.pi*c.re| := by congr 1; ring
    _ ≤ _ := he
    _ < _ := hlt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevJacobianLocality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Sobolev replacements agreeing outside a closed region have
the same Jacobian integral over that region. This is the interior
replacement step in the conductivity area computation. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakGradient_eq_on_open {u v : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hv : DeGiorgi.MemW1pWitness 2 v univ)
    {U : Set EuclideanPlane} (hU : IsOpen U) (heq : EqOn u v U) (i : Fin 2) :
    (fun x => hu.weakGrad x i) =ᵐ[volume.restrict U] fun x => hv.weakGrad x i := by
  let huU := hu.restrict hU (subset_univ U)
  let hvU := hv.restrict hU (subset_univ U)
  have hh := weakPartial_congrOn hU (huU.isWeakGrad i) heq
  exact hh.ae_eq hU (hvU.isWeakGrad i)
    ((huU.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hvU.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactWeakDerivativeIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Sobolev perturbations contribute zero total first derivative.
The support and integrability of the actual weak derivative are proved,
so the boundary-flux replacement does not assume an unproved trace fact. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_weakGradient_zero_off {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ x ∂volume, x ∉ tsupport u → hu.weakGrad x i = 0 := by
  have heq : EqOn u (fun x => (0 : ℝ) * u x) (tsupport u)ᶜ := by
    intro x hx
    simp only [zero_mul]
    exact image_eq_zero_of_notMem_tsupport hx
  have hh := weakGradient_eq_on_open hu (hu.smul 0) isClosed_closure.isOpen_compl heq i
  have hh' := (ae_restrict_iff' isClosed_closure.measurableSet.compl).mp hh
  filter_upwards [hh'] with x hx hxU
  simpa only [DeGiorgi.MemW1pWitness.smul, zero_smul, PiLp.zero_apply] using hx hxU

 theorem integral_compact_weakGradient_eq_zero {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hs : HasCompactSupport u) (i : Fin 2) :
    (∫ x, hu.weakGrad x i) = 0 := by
  obtain ⟨η, V, hη, hsη, _hunit, _hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hs.isCompact isOpen_univ (subset_univ _)
  have hd (x : EuclideanPlane) (hx : x ∈ tsupport u) : fderiv ℝ η x = 0 := by
    have hh : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.mem_of_superset (hV.mem_nhds (hKV hx)) (fun y hy => hone y hy)
    rw [hh.fderiv_eq]
    exact fderiv_const_apply (1 : ℝ)
  have hleft : (∫ x, u x * fderiv ℝ η x (EuclideanSpace.single i 1)) = 0 := by
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro x
    change u x * fderiv ℝ η x (EuclideanSpace.single i 1) = 0
    by_cases hx : x ∈ tsupport u
    · rw [hd x hx, _root_.zero_apply, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hright : (∫ x, hu.weakGrad x i * η x) = ∫ x, hu.weakGrad x i := by
    apply integral_congr_ae
    filter_upwards [compact_weakGradient_zero_off hu i] with x hx
    by_cases hxU : x ∈ tsupport u
    · rw [hone x (hKV hxU), mul_one]
    · rw [hx hxU, zero_mul]
  have hw := hu.isWeakGrad i η hη hsη (subset_univ _)
  simp only [Measure.restrict_univ] at hw
  rw [hleft, hright] at hw
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothExteriorReplacement
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local Sobolev scalar smooth off a compact set can be replaced by a
smooth scalar without changing it near an exterior boundary. The removed
part is an actual compactly supported global Sobolev function. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_smooth_exterior_replacement {K : Set EuclideanPlane} (hK : IsCompact K)
    {R : ℝ} (hKR : K ⊆ Metric.ball 0 R) {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball 0 R))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ) :
    ∃ (v e : EuclideanPlane → ℝ) (_ : DeGiorgi.MemW1pWitness 2 e univ),
      ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport e ∧
      tsupport e ⊆ Metric.ball 0 R ∧ (∀ x, u x = v x + e x) ∧ EqOn v u (Metric.ball 0 R)ᶜ := by
  obtain ⟨η, V, hη, hsη, _hunit, hηsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK Metric.isOpen_ball hKR
  let v : EuclideanPlane → ℝ := fun x => (1-η x) * u x
  let e : EuclideanPlane → ℝ := fun x => η x * u x
  obtain ⟨he⟩ := exists_global_compact_cutoff_witness Metric.isOpen_ball hu.memW1p hη hsη hηsub
  refine ⟨v, e, he, ?_, hsη.mul_right, tsupport_mul_subset_left.trans hηsub, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ K
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      change (1-η y) * u y = 0
      rw [hone y hy, sub_self, zero_mul]
    · exact (contDiffAt_const.sub hη.contDiffAt).mul
        (hsmooth.contDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx))
  · intro x
    dsimp only [v, e]
    ring
  · intro x hx
    have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hηsub ht))
    change (1-η x) * u x = u x
    rw [hz, sub_zero, one_mul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SmoothReplacementFlux
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine compact Sobolev correction has zero derivative integral.
Consequently a smooth exterior replacement preserves the finite-ball
vertical flux of the original weak coordinate. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integral_weakGradient_eq_smooth_replacement {u v e : EuclideanPlane → ℝ}
    {R : ℝ} (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball 0 R))
    (he : DeGiorgi.MemW1pWitness 2 e univ)
    (hs : HasCompactSupport e) (hsub : tsupport e ⊆ Metric.ball 0 R)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hue : ∀ x, u x = v x + e x) (i : Fin 2) :
    (∫ x in Metric.ball 0 R, hu.weakGrad x i) =
      ∫ x in Metric.ball 0 R, fderiv ℝ v x (EuclideanSpace.single i 1) := by
  let V : DeGiorgi.MemW1pWitness 2 v (Metric.ball 0 R) :=
    smoothPlaneSobolevWitness Metric.isOpen_ball (hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn
      (continuous_memLp_ball hv.continuous R)
      (fun j => continuous_memLp_ball
        ((hv.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuous_const) R)
  have hdiff : (fun x => u x-v x) =ᵐ[volume.restrict (Metric.ball 0 R)] e :=
    Eventually.of_forall (fun x => by change u x-v x = e x; rw [hue x]; ring)
  let W := (hu.sub V).congr_ae hdiff
  let E : DeGiorgi.MemW1pWitness 2 e (Metric.ball 0 R) :=
    he.restrict Metric.isOpen_ball (subset_univ _)
  have hg := (W.isWeakGrad i).ae_eq Metric.isOpen_ball (E.isWeakGrad i)
    ((W.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((E.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  have hg' : (fun x => hu.weakGrad x i - fderiv ℝ v x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict (Metric.ball 0 R)] fun x => he.weakGrad x i := by
    simpa [W, E, V, DeGiorgi.MemW1pWitness.sub, DeGiorgi.MemW1pWitness.congr_ae,
      DeGiorgi.MemW1pWitness.add, DeGiorgi.MemW1pWitness.smul,
      DeGiorgi.MemW1pWitness.restrict, smoothPlaneSobolevWitness, sub_eq_add_neg] using hg
  have he0 : (∫ x in Metric.ball 0 R, he.weakGrad x i) = 0 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
    · exact integral_compact_weakGradient_eq_zero he hs i
    · filter_upwards [compact_weakGradient_zero_off he i] with x hx hxB
      exact hx (fun ht => hxB (hsub ht))
  have huint : IntegrableOn (fun x => hu.weakGrad x i) (Metric.ball 0 R) := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanPlane) R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact (hu.weakGrad_component_memLp i).integrable (by norm_num)
  have hvint : IntegrableOn (fun x => fderiv ℝ v x (EuclideanSpace.single i 1))
      (Metric.ball 0 R) := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanPlane) R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact (V.weakGrad_component_memLp i).integrable (by norm_num)
  have hh := integral_congr_ae hg'
  rw [integral_sub huint hvint, he0] at hh
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothDiskGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two concrete Green identities used for the conductivity map:
its smooth Jacobian is an actual boundary integral, and its vertical
partial derivative is the corresponding outward flux. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_disk_vertical_flux (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) {v : ℂ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    (∫ z in ball (0 : ℂ) R, fderiv ℝ v z Complex.I) =
      planarFormIntegral (fun z => -v z) (fun _ => 0) (unitCircleParam 0 R) := by
  rw [round_disk_green hgreen R hR univ isOpen_univ (subset_univ _)
    _ _ hv.neg.contDiffOn contDiff_const.contDiffOn]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  simp only [fderiv_const_apply, fderiv_fun_neg, zero_apply, neg_apply, zero_sub, neg_neg]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalRoundIntegrals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of round-disk integrals and smooth partial derivatives
between the physical Euclidean plane and the complex plane. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complexPlaneCoordinates_integral_ball (R : ℝ) (g : ℂ → ℝ) :
    (∫ x in ball (0 : EuclideanPlane) R, g (complexPlaneCoordinates x)) =
      ∫ z in ball (0 : ℂ) R, g z := by
  rw [← complexPlaneCoordinates_preimage_ball]
  exact complexPlaneCoordinates_measurePreserving.setIntegral_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding g _

 theorem physical_real_volume_ball (R : ℝ) (hR : 0 ≤ R) :
    (volume (ball (0 : EuclideanPlane) R)).toReal = Real.pi*R^2 := by
  have hh := complexPlaneCoordinates_integral_ball R (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply_univ] at hh
  rw [hh, real_volume_ball 0 hR]

 theorem physical_complex_partial {a : EuclideanPlane → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (x v : EuclideanPlane) :
    fderiv ℝ (fun z => a (complexPlaneCoordinates.symm z)) (complexPlaneCoordinates x)
      (complexPlaneCoordinates v) = fderiv ℝ a x v := by
  change fderiv ℝ (a ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)
    (complexPlaneCoordinates v) = _
  rw [fderiv_comp (complexPlaneCoordinates x) (ha.differentiable (by simp)).differentiableAt
      complexPlaneCoordinates.symm.differentiableAt, complexPlaneCoordinates.symm.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

 theorem smooth_physical_disk_vertical_flux (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) {a : EuclideanPlane → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    (∫ x in ball (0 : EuclideanPlane) R, fderiv ℝ a x (EuclideanSpace.single 1 1)) =
      planarFormIntegral (fun z => -a (complexPlaneCoordinates.symm z))
        (fun _ => 0) (unitCircleParam 0 R) := by
  calc
    _ = ∫ x in ball (0 : EuclideanPlane) R,
        fderiv ℝ (fun z => a (complexPlaneCoordinates.symm z))
          (complexPlaneCoordinates x) Complex.I := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [← complexPlaneCoordinates_one, physical_complex_partial ha]
    _ = ∫ z in ball (0 : ℂ) R, fderiv ℝ (fun w => a (complexPlaneCoordinates.symm w)) z Complex.I :=
      complexPlaneCoordinates_integral_ball R (fun z => fderiv ℝ (fun w => a (complexPlaneCoordinates.symm w)) z Complex.I)
    _ = _ := by
      simpa only [Function.comp_def] using smooth_disk_vertical_flux hgreen R hR (ha.comp complexPlaneCoordinates.symm.contDiff)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityFlux
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual weak conductivity height has the principal boundary flux.
The interior correction is constructed, its derivative integral vanishes,
and the smooth Green calculation retains the exact exterior values. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphic_physical_im_smooth {φ : ℂ → ℂ} {F : Set EuclideanPlane}
    (hF : IsClosed F) (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (φ (complexPlaneCoordinates x)).im) Fᶜ := by
  have hO : IsOpen (complexPlaneCoordinates '' F)ᶜ :=
    (complexPlaneCoordinates.toHomeomorph.isClosedMap _ hF).isOpen_compl
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) φ (complexPlaneCoordinates '' F)ᶜ :=
    (hh.contDiffOn hO).restrict_scalars ℝ
  have hp := hc.comp complexPlaneCoordinates.contDiff.contDiffOn
    (show MapsTo complexPlaneCoordinates Fᶜ (complexPlaneCoordinates '' F)ᶜ from by
      intro x hx hm
      obtain ⟨y, hy, heq⟩ := hm
      exact hx (complexPlaneCoordinates.injective heq ▸ hy))
  exact Complex.imCLM.contDiff.contDiffOn.comp hp (mapsTo_univ _ _)

 theorem PlaneLocalWeakComplex.vertical_flux_boundary
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ R : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀) (hR : r₀ < R) :
    (∫ x in ball (0 : EuclideanPlane) R, D.imagGradient x 1) =
      planarFormIntegral (fun z => -(φ z).im) (fun _ => 0) (unitCircleParam 0 R) := by
  have hcont := hφ.comp complexPlaneCoordinates.continuous
  obtain ⟨v, e, he, hv, hs, hsub, hue, hext⟩ := exists_smooth_exterior_replacement hF hFr
    (D.imagWitness hcont r₀) (holomorphic_physical_im_smooth hF.isClosed hh)
  have hRpos : 0 < R := hr₀.trans hR
  have hflux := integral_weakGradient_eq_smooth_replacement (D.imagWitness hcont R)
    he hs (hsub.trans (ball_subset_ball hR.le)) hv hue 1
  change (∫ x in ball (0 : EuclideanPlane) R, D.imagGradient x 1) = _ at hflux
  rw [hflux, smooth_physical_disk_vertical_flux hgreen R hRpos hv]
  unfold planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _ht
  have hn : ‖complexPlaneCoordinates.symm (unitCircleParam 0 R t)‖ = R := by
    rw [← complexPlaneCoordinates_norm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRpos]
  have hout : complexPlaneCoordinates.symm (unitCircleParam 0 R t) ∉ ball 0 r₀ := by
    simp only [mem_ball, dist_zero_right, hn]
    exact not_lt_of_gt hR
  have hvv := hext hout
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hvv
  simp only [hvv]

 theorem PlaneLocalWeakComplex.vertical_flux_limit
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀)
    {c : ℂ} {T : ℂ → ℂ} (hT : ContinuousAt T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
    Tendsto (fun R : ℝ => (∫ x in ball (0 : EuclideanPlane) R, D.imagGradient x 1) -
      (volume (ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 (-Real.pi*c.re)) := by
  apply (principal_circle_flux_limit hφ hT hexp).congr'
  filter_upwards [eventually_gt_atTop r₀] with R hR
  rw [D.vertical_flux_boundary hgreen hφ hF hh hr₀ hFr hR,
    physical_real_volume_ball R (hr₀.trans hR).le]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact global conductivity energy identity follows from the
constructed principal solution and the proved boundary limits. No area,
flux or energy estimate is an additional input. -/
open Set Filter Function MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.conductivity_energy_of_principal_expansion
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀)
    {c : ℂ} {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹)
    (n : ℕ) (hn : 2 ≤ n)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) :
    Integrable (fun x => (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ∧
    (∫ x, (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) +
      ((n : ℝ)-1)*(∫ x in F, (D.imagGradient x 0)^2+(D.imagGradient x 1)^2) =
        2*Real.pi*c.re :=
  D.conductivity_global_energy hF n (by omega) c.re hsys
    (D.jacobian_area_limit hgreen hφ hF hh hr₀ hFr hT hexp)
    (D.vertical_flux_limit hgreen hφ hF hh hr₀ hFr hT.continuousAt hexp)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalScalarEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the constructed compact scalar transport when deriving the
principal conductivity energy identity. -/
open Set Filter Function MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_principal_conductivity_energy_scalar_oai
    (hsolver : PrincipalConductivityScalarSolver)
    (hgreen : UnorientedFiniteCircleGreenFormula) {F : Set EuclideanPlane}
    (hF : IsCompact F) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
      (c : ℂ) (T : ℂ → ℂ),
      AnalyticAt ℂ T 0 ∧
      Tendsto (fun z => φ z-z) (cobounded ℂ) (𝓝 0) ∧
      (∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) ∧
      DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ ∧
      Integrable (fun x => (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ∧
      (∫ x, (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) +
        ((n : ℝ)-1)*(∫ x in F, (D.imagGradient x 0)^2+(D.imagGradient x 1)^2) =
          2*Real.pi*c.re ∧ CompactScalarPullback φ := by
  obtain ⟨φ, D, ht, hsys, hscalar⟩ := hsolver F hF n (by omega)
  have hh := D.conductivity_holomorphic_off φ.continuous hF.isClosed n hsys
  have hFc := hF.image complexPlaneCoordinates.continuous
  have hdiff : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ φ z := by
    have hmem : ∀ᶠ z in cobounded ℂ, z ∈ (complexPlaneCoordinates '' F)ᶜ := by
      rw [Metric.cobounded_eq_cocompact]
      exact hFc.compl_mem_cocompact
    exact hmem.mono fun z hz => hh.differentiableAt (hFc.isClosed.isOpen_compl.mem_nhds hz)
  obtain ⟨c, T, hT, hexp⟩ := principal_exterior_expansion hdiff ht
  obtain ⟨R, hFR⟩ := hF.isBounded.subset_ball (0 : EuclideanPlane)
  have hr₀ : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFr₀ : F ⊆ ball 0 (max R 1) := hFR.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨hI, hE⟩ := D.conductivity_energy_of_principal_expansion hgreen φ.continuous
    hF hh hr₀ hFr₀ hT hexp n hn hsys
  exact ⟨φ, D, c, T, hT, ht, hexp, hsys, hh, hI, hE, hscalar⟩

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar_oai := @OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar_oai
