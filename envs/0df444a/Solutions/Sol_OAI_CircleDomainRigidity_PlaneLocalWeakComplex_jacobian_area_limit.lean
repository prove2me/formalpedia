-- Prove2me | solution 1 for OAI.CircleDomainRigidity.PlaneLocalWeakComplex.jacobian_area_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:39:33.089215+00:00
-- url     : https://prove2.me/submissions/99c0642e-db01-47d5-863d-52fd6d2d8c16

import Mathlib
import Definitions.Def_Q146C005

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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactSobolevJacobian
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral of the Jacobian of two compact Sobolev scalars is zero.
Only one scalar is mollified. Its two differentiated test functions have
commuting mixed derivatives, and strong L2 convergence passes the pairing
to the original gradients. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem tendsto_integral_mul_of_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → X → ℝ} {G φ : X → ℝ}
    (hg : ∀ n, MemLp (g n) 2 μ) (hG : MemLp G 2 μ) (hφ : MemLp φ 2 μ)
    (hl : Tendsto (fun n => eLpNorm (fun x => g n x-G x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, g n x * φ x ∂μ) atTop (𝓝 (∫ x, G x * φ x ∂μ)) := by
  have ht := tendsto_integral_bounded_mul_L2 hg hG hφ hl
    (h := fun _ _ => (1 : ℝ)) (H := fun _ => (1 : ℝ))
    (fun _ => aestronglyMeasurable_const) (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ => Eventually.of_forall (fun _ => by norm_num))
    (Eventually.of_forall (fun _ => tendsto_const_nhds))
  simpa only [one_mul] using ht

 theorem smooth_partial_commute {v : EuclideanPlane → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : EuclideanPlane) (i j : Fin 2) :
    fderiv ℝ (fun y => fderiv ℝ v y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    ((hv.contDiffAt.fderiv_right (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by norm_num))
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact hv.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _ _

 theorem integral_compact_sobolev_jacobian_zero {u v : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hv : DeGiorgi.MemW1pWitness 2 v univ)
    (hsv : HasCompactSupport v) :
    (∫ x, hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) = 0 := by
  have hvL : MemLp v 2 volume := by simpa only [Measure.restrict_univ] using hv.memLp
  let vₙ := planarMollification v
  have hsm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (vₙ n) :=
    planarMollification_smooth (hvL.locallyIntegrable (by norm_num)) n
  have hs (n : ℕ) : HasCompactSupport (vₙ n) := planarMollification_hasCompactSupport hsv n
  have htest (n : ℕ) (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ (vₙ n) x (EuclideanSpace.single i 1)) :=
    (((hsm n).fderiv_right (m := (⊤ : ℕ∞)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)
  have hidentity (n : ℕ) :
      (∫ x, hu.weakGrad x 0 * fderiv ℝ (vₙ n) x (EuclideanSpace.single 1 1)) =
      ∫ x, hu.weakGrad x 1 * fderiv ℝ (vₙ n) x (EuclideanSpace.single 0 1) := by
    have h0 := hu.isWeakGrad 0 _ (htest n 1) ((hs n).fderiv_apply (𝕜 := ℝ) _) (subset_univ _)
    have h1 := hu.isWeakGrad 1 _ (htest n 0) ((hs n).fderiv_apply (𝕜 := ℝ) _) (subset_univ _)
    simp only [Measure.restrict_univ] at h0 h1
    have he (x : EuclideanPlane) :
        fderiv ℝ (fun y => fderiv ℝ (vₙ n) y (EuclideanSpace.single 1 1)) x (EuclideanSpace.single 0 1) =
        fderiv ℝ (fun y => fderiv ℝ (vₙ n) y (EuclideanSpace.single 0 1)) x (EuclideanSpace.single 1 1) :=
      smooth_partial_commute (hsm n) x 0 1
    simp_rw [he] at h0
    linarith [h0, h1]
  have huG (i : Fin 2) : MemLp (fun x => hu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp i
  have hvG (i : Fin 2) : MemLp (fun x => hv.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hv.weakGrad_component_memLp i
  have ht (i j : Fin 2) := tendsto_integral_mul_of_L2
    (fun n => planarMollification_partial_memLp hv hsv n j) (hvG j) (huG i)
    (planarMollification_tendsto_gradient_L2 hv j)
  have ht' (i j : Fin 2) : Tendsto
      (fun n => ∫ x, hu.weakGrad x i * fderiv ℝ (vₙ n) x (EuclideanSpace.single j 1))
      atTop (𝓝 (∫ x, hu.weakGrad x i * hv.weakGrad x j)) := by
    simpa only [mul_comm] using ht i j
  have heq : (∫ x, hu.weakGrad x 0 * hv.weakGrad x 1) =
      ∫ x, hu.weakGrad x 1 * hv.weakGrad x 0 := by
    apply tendsto_nhds_unique (ht' 0 1)
    convert ht' 1 0 using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact hidentity n
  have h01 : Integrable (fun x => hu.weakGrad x 0 * hv.weakGrad x 1) :=
    (huG 0).integrable_mul (hvG 1)
  have h10 : Integrable (fun x => hu.weakGrad x 1 * hv.weakGrad x 0) :=
    (huG 1).integrable_mul (hvG 0)
  rw [integral_sub h01 h10, heq, sub_self]

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

 theorem sobolev_jacobian_integral_locality {u v a b : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hv : DeGiorgi.MemW1pWitness 2 v univ)
    (ha : DeGiorgi.MemW1pWitness 2 a univ) (hb : DeGiorgi.MemW1pWitness 2 b univ)
    (hsv : HasCompactSupport v) (hsb : HasCompactSupport b)
    {K : Set EuclideanPlane} (hK : IsClosed K) (hua : EqOn u a Kᶜ) (hvb : EqOn v b Kᶜ) :
    (∫ x in K, hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) =
    ∫ x in K, ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0 := by
  have h0 := integral_compact_sobolev_jacobian_zero hu hv hsv
  have h1 := integral_compact_sobolev_jacobian_zero ha hb hsb
  have huG (i : Fin 2) : MemLp (fun x => hu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp i
  have hvG (i : Fin 2) : MemLp (fun x => hv.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hv.weakGrad_component_memLp i
  have haG (i : Fin 2) : MemLp (fun x => ha.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using ha.weakGrad_component_memLp i
  have hbG (i : Fin 2) : MemLp (fun x => hb.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hb.weakGrad_component_memLp i
  have hI : Integrable (fun x => hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) :=
    ((huG 0).integrable_mul (hvG 1)).sub ((huG 1).integrable_mul (hvG 0))
  have hJ : Integrable (fun x => ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0) :=
    ((haG 0).integrable_mul (hbG 1)).sub ((haG 1).integrable_mul (hbG 0))
  have hcomp : (∫ x in Kᶜ, hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) =
      ∫ x in Kᶜ, ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0 := by
    apply integral_congr_ae
    filter_upwards [weakGradient_eq_on_open hu ha hK.isOpen_compl hua 0,
      weakGradient_eq_on_open hu ha hK.isOpen_compl hua 1,
      weakGradient_eq_on_open hv hb hK.isOpen_compl hvb 0,
      weakGradient_eq_on_open hv hb hK.isOpen_compl hvb 1] with x hu0 hu1 hv0 hv1
    rw [hu0, hu1, hv0, hv1]
  have hsum0 := integral_add_compl hK.measurableSet hI
  have hsum1 := integral_add_compl hK.measurableSet hJ
  rw [h0] at hsum0
  rw [h1] at hsum1
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

 theorem smooth_complex_partial_commute {v : ℂ → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (z p q : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ v w q) z p =
      fderiv ℝ (fun w => fderiv ℝ v w p) z q := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) z :=
    ((hv.contDiffAt.fderiv_right (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by norm_num))
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact hv.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _ _

 theorem smooth_disk_jacobian (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) {a b : ℂ → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    (∫ z in ball (0 : ℂ) R,
      fderiv ℝ a z 1 * fderiv ℝ b z Complex.I -
        fderiv ℝ a z Complex.I * fderiv ℝ b z 1) =
      planarFormIntegral (fun z => a z * fderiv ℝ b z 1)
        (fun z => a z * fderiv ℝ b z Complex.I) (unitCircleParam 0 R) := by
  have hb' (p : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ b z p) :=
    (hb.fderiv_right (m := (⊤ : ℕ∞)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  rw [round_disk_green hgreen R hR univ isOpen_univ (subset_univ _)
    _ _ (ha.mul (hb' 1)).contDiffOn (ha.mul (hb' Complex.I)).contDiffOn]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [fderiv_fun_mul (ha.differentiable (by simp)).differentiableAt
      ((hb' Complex.I).differentiable (by simp)).differentiableAt,
    fderiv_fun_mul (ha.differentiable (by simp)).differentiableAt
      ((hb' 1).differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [smooth_complex_partial_commute hb z 1 Complex.I]
  ring

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

 theorem smooth_physical_disk_jacobian (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) {a b : EuclideanPlane → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    (∫ x in ball (0 : EuclideanPlane) R,
      fderiv ℝ a x (EuclideanSpace.single 0 1) * fderiv ℝ b x (EuclideanSpace.single 1 1) -
        fderiv ℝ a x (EuclideanSpace.single 1 1) * fderiv ℝ b x (EuclideanSpace.single 0 1)) =
      planarFormIntegral
        (fun z => a (complexPlaneCoordinates.symm z) *
          fderiv ℝ (fun w => b (complexPlaneCoordinates.symm w)) z 1)
        (fun z => a (complexPlaneCoordinates.symm z) *
          fderiv ℝ (fun w => b (complexPlaneCoordinates.symm w)) z Complex.I)
        (unitCircleParam 0 R) := by
  let A := fun z => a (complexPlaneCoordinates.symm z)
  let B := fun z => b (complexPlaneCoordinates.symm z)
  calc
    _ = ∫ x in ball (0 : EuclideanPlane) R,
        fderiv ℝ A (complexPlaneCoordinates x) 1 *
          fderiv ℝ B (complexPlaneCoordinates x) Complex.I -
        fderiv ℝ A (complexPlaneCoordinates x) Complex.I *
          fderiv ℝ B (complexPlaneCoordinates x) 1 := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only [A, B]
      rw [← complexPlaneCoordinates_zero, ← complexPlaneCoordinates_one,
        physical_complex_partial ha, physical_complex_partial hb,
        physical_complex_partial ha, physical_complex_partial hb]
    _ = ∫ z in ball (0 : ℂ) R, fderiv ℝ A z 1 * fderiv ℝ B z Complex.I -
        fderiv ℝ A z Complex.I * fderiv ℝ B z 1 :=
      complexPlaneCoordinates_integral_ball R (fun z => fderiv ℝ A z 1 * fderiv ℝ B z Complex.I -
        fderiv ℝ A z Complex.I * fderiv ℝ B z 1)
    _ = _ := by
      simpa only [Function.comp_def] using smooth_disk_jacobian hgreen R hR
        (ha.comp complexPlaneCoordinates.symm.contDiff) (hb.comp complexPlaneCoordinates.symm.contDiff)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityFlux
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevJacobianReplacement
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Sobolev Jacobians are unchanged by compact interior replacements.
A common compact cutoff reduces the assertion to the proved whole-plane
null Lagrangian, while its plateau preserves all four original gradients. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_jacobian_integral_locality
    {U K : Set EuclideanPlane} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {u v a b : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u U) (hv : DeGiorgi.MemW1pWitness 2 v U)
    (ha : DeGiorgi.MemW1pWitness 2 a U) (hb : DeGiorgi.MemW1pWitness 2 b U)
    (hua : EqOn u a (U \ K)) (hvb : EqOn v b (U \ K)) :
    (∫ x in K, hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) =
    ∫ x in K, ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0 := by
  obtain ⟨η, V, hη, hsη, _hunit, hηU, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hU hKU
  have hVU : V ⊆ U := by
    intro x hx
    apply hηU
    apply subset_tsupport η
    change η x ≠ 0
    rw [hone x hx]
    exact one_ne_zero
  obtain ⟨hu'⟩ := exists_global_compact_cutoff_witness hU hu.memW1p hη hsη hηU
  obtain ⟨hv'⟩ := exists_global_compact_cutoff_witness hU hv.memW1p hη hsη hηU
  obtain ⟨ha'⟩ := exists_global_compact_cutoff_witness hU ha.memW1p hη hsη hηU
  obtain ⟨hb'⟩ := exists_global_compact_cutoff_witness hU hb.memW1p hη hsη hηU
  have heq {f g : EuclideanPlane → ℝ} (hfg : EqOn f g (U \ K)) :
      EqOn (fun x => η x*f x) (fun x => η x*g x) Kᶜ := by
    intro x hx
    change η x*f x = η x*g x
    by_cases hxU : x ∈ U
    · rw [hfg ⟨hxU, hx⟩]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxU (hηU ht)), zero_mul, zero_mul]
  have hj := sobolev_jacobian_integral_locality hu' hv' ha' hb'
    hsη.mul_right hsη.mul_right hK.isClosed (heq hua) (heq hvb)
  have huG (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVU hu hu' hone i)
  have hvG (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVU hv hv' hone i)
  have haG (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVU ha ha' hone i)
  have hbG (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVU hb hb' hone i)
  calc
    _ = ∫ x in K, hu'.weakGrad x 0 * hv'.weakGrad x 1 -
        hu'.weakGrad x 1 * hv'.weakGrad x 0 := by
      apply integral_congr_ae
      filter_upwards [huG 0, huG 1, hvG 0, hvG 1] with x hu0 hu1 hv0 hv1
      rw [hu0, hu1, hv0, hv1]
    _ = _ := hj
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [haG 0, haG 1, hbG 0, hbG 1] with x ha0 ha1 hb0 hb1
      rw [ha0, ha1, hb0, hb1]

 theorem volume_restrict_closedBall_eq_ball (R : ℝ) :
    volume.restrict (Metric.closedBall (0 : EuclideanPlane) R) =
      volume.restrict (Metric.ball (0 : EuclideanPlane) R) := by
  apply Measure.restrict_congr_set
  have hs : ∀ᵐ x ∂(volume : Measure EuclideanPlane), x ∉ Metric.sphere 0 R := by
    exact compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (0 : EuclideanPlane) R)
  filter_upwards [hs] with x hx
  apply propext
  constructor
  · intro hxC
    have hle : dist x 0 ≤ R := hxC
    have hne : dist x 0 ≠ R := hx
    exact lt_of_le_of_ne hle hne
  · intro hx
    exact Metric.ball_subset_closedBall hx

 theorem local_sobolev_jacobian_ball_replacement {R S : ℝ} (hRS : R < S)
    {u v a b : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball 0 S))
    (hv : DeGiorgi.MemW1pWitness 2 v (Metric.ball 0 S))
    (ha : DeGiorgi.MemW1pWitness 2 a (Metric.ball 0 S))
    (hb : DeGiorgi.MemW1pWitness 2 b (Metric.ball 0 S))
    (hua : EqOn u a (Metric.ball 0 S \ Metric.ball 0 R))
    (hvb : EqOn v b (Metric.ball 0 S \ Metric.ball 0 R)) :
    (∫ x in Metric.ball 0 R,
      hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) =
    ∫ x in Metric.ball 0 R,
      ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0 := by
  have he := local_sobolev_jacobian_integral_locality Metric.isOpen_ball
    (isCompact_closedBall (0 : EuclideanPlane) R) (Metric.closedBall_subset_ball hRS)
    hu hv ha hb
    (fun x hx => hua ⟨hx.1, fun hxB => hx.2 (Metric.ball_subset_closedBall hxB)⟩)
    (fun x hx => hvb ⟨hx.1, fun hxB => hx.2 (Metric.ball_subset_closedBall hxB)⟩)
  simpa only [volume_restrict_closedBall_eq_ball R] using he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothImageArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Jacobian boundary integral is the signed area of the
actual image curve, expressed using its real and imaginary coordinates. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complex_real_linear_decomposition (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = L 1 * z.re + L Complex.I * z.im := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

 theorem signedCurveArea_smooth_image {F : ℂ → ℂ} {γ : ℝ → ℂ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) :
    signedCurveArea (F ∘ γ) =
      planarFormIntegral (fun z => (F z).re * fderiv ℝ (fun w => (F w).im) z 1)
        (fun z => (F z).re * fderiv ℝ (fun w => (F w).im) z Complex.I) γ := by
  unfold signedCurveArea planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [Function.comp_def]
  have hf := (hF.differentiable (by simp)).differentiableAt (x := γ t)
  have hg := (hγ.differentiable (by simp)).differentiableAt (x := t)
  have hd := hf.hasFDerivAt.comp_hasDerivAt t hg.hasDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp (γ t) hf.hasFDerivAt
  have hie (v : ℂ) : fderiv ℝ (fun w => (F w).im) (γ t) v =
      (fderiv ℝ F (γ t) v).im := by
    change fderiv ℝ (Complex.imCLM ∘ F) (γ t) v = _
    rw [hi.fderiv]
    rfl
  have hde : deriv (fun x => F (γ x)) t = fderiv ℝ F (γ t) (deriv γ t) := by
    simpa only [Function.comp_def] using hd.deriv
  rw [hde]
  rw [← hie]
  rw [complex_real_linear_decomposition]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityJacobianBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weak conductivity Jacobian has the signed area of the actual
image circle. The two interior replacements are constructed; locality
removes their compact errors before applying the smooth Green identity. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphic_physical_re_smooth {φ : ℂ → ℂ} {F : Set EuclideanPlane}
    (hF : IsClosed F) (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (φ (complexPlaneCoordinates x)).re) Fᶜ := by
  have hO : IsOpen (complexPlaneCoordinates '' F)ᶜ :=
    (complexPlaneCoordinates.toHomeomorph.isClosedMap _ hF).isOpen_compl
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) φ (complexPlaneCoordinates '' F)ᶜ :=
    (hh.contDiffOn hO).restrict_scalars ℝ
  have hp := hc.comp complexPlaneCoordinates.contDiff.contDiffOn
    (show MapsTo complexPlaneCoordinates Fᶜ (complexPlaneCoordinates '' F)ᶜ from by
      intro x hx hm
      obtain ⟨y, hy, heq⟩ := hm
      exact hx (complexPlaneCoordinates.injective heq ▸ hy))
  exact Complex.reCLM.contDiff.contDiffOn.comp hp (mapsTo_univ _ _)

 theorem PlaneLocalWeakComplex.jacobian_boundary
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ R : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀) (hR : r₀ < R) :
    (∫ x in ball (0 : EuclideanPlane) R,
      D.realGradient x 0 * D.imagGradient x 1 -
        D.realGradient x 1 * D.imagGradient x 0) =
      signedCurveArea (φ ∘ unitCircleParam 0 R) := by
  have hcont := hφ.comp complexPlaneCoordinates.continuous
  obtain ⟨a, e, _he, ha, _hse, _hsube, _hue, hexta⟩ := exists_smooth_exterior_replacement hF hFr
    (D.realWitness hcont r₀) (holomorphic_physical_re_smooth hF.isClosed hh)
  obtain ⟨b, f, _hf, hb, _hsf, _hsubf, _huf, hextb⟩ := exists_smooth_exterior_replacement hF hFr
    (D.imagWitness hcont r₀) (holomorphic_physical_im_smooth hF.isClosed hh)
  have hRpos : 0 < R := hr₀.trans hR
  let A : DeGiorgi.MemW1pWitness 2 a (ball 0 (R+1)) :=
    smoothPlaneSobolevWitness isOpen_ball (ha.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn
      (continuous_memLp_ball ha.continuous (R+1))
      (fun i => continuous_memLp_ball
        ((ha.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuous_const) (R+1))
  let B : DeGiorgi.MemW1pWitness 2 b (ball 0 (R+1)) :=
    smoothPlaneSobolevWitness isOpen_ball (hb.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn
      (continuous_memLp_ball hb.continuous (R+1))
      (fun i => continuous_memLp_ball
        ((hb.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuous_const) (R+1))
  have houtside {x : EuclideanPlane} (hx : x ∉ ball 0 R) : x ∉ ball 0 r₀ :=
    fun hm => hx (ball_subset_ball hR.le hm)
  have hj := local_sobolev_jacobian_ball_replacement (show R < R+1 by linarith)
    (D.realWitness hcont (R+1)) (D.imagWitness hcont (R+1)) A B
    (fun x hx => (hexta (houtside hx.2)).symm)
    (fun x hx => (hextb (houtside hx.2)).symm)
  change (∫ x in ball (0 : EuclideanPlane) R,
      D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0) =
    (∫ x in ball (0 : EuclideanPlane) R,
      fderiv ℝ a x (EuclideanSpace.single 0 1) * fderiv ℝ b x (EuclideanSpace.single 1 1) -
        fderiv ℝ a x (EuclideanSpace.single 1 1) * fderiv ℝ b x (EuclideanSpace.single 0 1)) at hj
  rw [hj, smooth_physical_disk_jacobian hgreen R hRpos ha hb]
  let Ψ : ℂ → ℂ := fun z => (a (complexPlaneCoordinates.symm z) : ℂ) +
    Complex.I * (b (complexPlaneCoordinates.symm z) : ℂ)
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ :=
    (Complex.ofRealCLM.contDiff.comp (ha.comp complexPlaneCoordinates.symm.contDiff)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (hb.comp complexPlaneCoordinates.symm.contDiff)))
  have hre : (fun z => (Ψ z).re) = fun z => a (complexPlaneCoordinates.symm z) := by
    funext z
    simp [Ψ]
  have him : (fun z => (Ψ z).im) = fun z => b (complexPlaneCoordinates.symm z) := by
    funext z
    simp [Ψ]
  have hcurve : Ψ ∘ unitCircleParam 0 R = φ ∘ unitCircleParam 0 R := by
    funext t
    have hn : ‖complexPlaneCoordinates.symm (unitCircleParam 0 R t)‖ = R := by
      rw [← complexPlaneCoordinates_norm, ContinuousLinearEquiv.apply_symm_apply]
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRpos]
    have hout : complexPlaneCoordinates.symm (unitCircleParam 0 R t) ∉ ball 0 r₀ := by
      simp only [mem_ball, dist_zero_right, hn]
      exact not_lt_of_gt hR
    have haeq := hexta hout
    have hbeq := hextb hout
    simp only [ContinuousLinearEquiv.apply_symm_apply] at haeq hbeq
    apply Complex.ext <;> simp [Ψ, haeq, hbeq]
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (unitCircleParam 0 R) :=
    (contDiff_circleMap 0 R).comp (contDiff_const.mul contDiff_id)
  rw [← hcurve, signedCurveArea_smooth_image hΨ hγ]
  simp only [him]
  congr 1 <;> funext z <;> rw [congrFun hre z]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalCircleArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed area of the first two principal Laurent terms is computed
exactly; the term linear in the first coefficient cancels. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principalLeadingCurve_hasDerivAt (R : ℝ) (hR : 0 < R) (c : ℂ) (t : ℝ) :
    HasDerivAt (principalLeadingCurve R c)
      ((unitCircleParam 0 R t-c/unitCircleParam 0 R t)*Complex.I*(2*Real.pi)) t := by
  have hn : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  have hd := unitCircleParam_hasDerivAt R t
  have he := hd.add ((hd.inv hn).const_mul c)
  refine (he.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp only [principalLeadingCurve, div_eq_mul_inv, Pi.add_apply, Pi.inv_apply]
  · simp only [unitCircleParam]
    field_simp
    ring

 theorem integral_unit_cos_sq :
    (∫ t in (0 : ℝ)..1, Real.cos (2*Real.pi*t)^2) = 1/2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x^2)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  simp only [mul_zero, mul_one, integral_cos_sq, Real.sin_zero, mul_zero,
    Real.sin_two_pi, sub_zero, zero_add, smul_eq_mul]
  field_simp

 theorem principal_leading_circle_area (R : ℝ) (hR : 0 < R) (c : ℂ) :
    signedCurveArea (principalLeadingCurve R c) = Real.pi*R^2-Real.pi*‖c‖^2/R^2 := by
  have hn (t : ℝ) : Complex.normSq (circleMap 0 R t) = R^2 := by
    rw [Complex.normSq_eq_norm_sq, norm_circleMap_zero, abs_of_pos hR]
  have hi (t : ℝ) :
      (principalLeadingCurve R c t).re * (deriv (principalLeadingCurve R c) t).im =
      (2*Real.pi*(R^2-c.re^2/R^2)) * Real.cos (2*Real.pi*t)^2 -
        (4*Real.pi*c.re*c.im/R^2) * (Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) -
        (2*Real.pi*c.im^2/R^2) * Real.sin (2*Real.pi*t)^2 := by
    rw [(principalLeadingCurve_hasDerivAt R hR c t).deriv]
    simp only [principalLeadingCurve, unitCircleParam, Complex.add_re, Complex.sub_re,
      Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.div_re, hn,
      mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add,
      circleMap_zero_re, circleMap_zero_im]
    field_simp [hR.ne']
    ring
  have hs : IntervalIntegrable (fun t : ℝ => Real.sin (2*Real.pi*t)^2) volume 0 1 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun t : ℝ => Real.cos (2*Real.pi*t)^2) volume 0 1 :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2).intervalIntegrable _ _
  have hsc : IntervalIntegrable (fun t : ℝ => Real.sin (2*Real.pi*t)*Real.cos (2*Real.pi*t)) volume 0 1 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  simp only [signedCurveArea, hi]
  rw [intervalIntegral.integral_sub ((hc.const_mul _).sub (hsc.const_mul _)) (hs.const_mul _),
    intervalIntegral.integral_sub (hc.const_mul _) (hsc.const_mul _)]
  simp only [intervalIntegral.integral_const_mul, integral_unit_cos_sq,
    integral_unit_sin_sq, integral_unit_sin_cos, mul_zero, sub_zero]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalLeadingBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Size, derivative and smoothness bounds for the leading principal
curve. These estimates isolate its contribution from the analytic remainder. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principalLeadingCurve_norm {R : ℝ} (hR : 1 ≤ R) (c : ℂ) (t : ℝ) :
    ‖principalLeadingCurve R c t‖ ≤ (1+‖c‖)*R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hn : ‖unitCircleParam 0 R t‖ = R := by
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
  have hq : ‖c/unitCircleParam 0 R t‖ ≤ ‖c‖*R := by
    rw [norm_div, hn, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left ((inv_le_one_of_one_le₀ hR).trans hR) (norm_nonneg c)
  calc
    _ ≤ ‖unitCircleParam 0 R t‖+‖c/unitCircleParam 0 R t‖ := norm_add_le _ _
    _ ≤ R+‖c‖*R := add_le_add (le_of_eq hn) hq
    _ = _ := by ring

 theorem principalLeadingCurve_deriv_norm {R : ℝ} (hR : 1 ≤ R) (c : ℂ) (t : ℝ) :
    ‖deriv (principalLeadingCurve R c) t‖ ≤ 2*Real.pi*(1+‖c‖)*R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hn : ‖unitCircleParam 0 R t‖ = R := by
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
  have hq : ‖c/unitCircleParam 0 R t‖ ≤ ‖c‖*R := by
    rw [norm_div, hn, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left ((inv_le_one_of_one_le₀ hR).trans hR) (norm_nonneg c)
  rw [(principalLeadingCurve_hasDerivAt R hRp c t).deriv, norm_mul, norm_mul,
    Complex.norm_I, mul_one]
  have hc : ‖(2*Real.pi : ℂ)‖ = 2*Real.pi := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hc]
  calc
    _ ≤ (‖unitCircleParam 0 R t‖+‖c/unitCircleParam 0 R t‖)*(2*Real.pi) :=
      mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
    _ ≤ (R+‖c‖*R)*(2*Real.pi) :=
      mul_le_mul_of_nonneg_right (add_le_add (le_of_eq hn) hq) (by positivity)
    _ = _ := by ring

 theorem principalLeadingCurve_smooth {R : ℝ} (hR : 0 < R) (c : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (principalLeadingCurve R c) := by
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (unitCircleParam 0 R) :=
    (contDiff_circleMap 0 R).comp (contDiff_const.mul contDiff_id)
  have hn (t : ℝ) : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  change ContDiff ℝ (⊤ : ℕ∞) (fun t => unitCircleParam 0 R t+c*(unitCircleParam 0 R t)⁻¹)
  exact hγ.add (contDiff_const.mul (hγ.inv hn))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CurveAreaStability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative signed-area stability for two smooth closed-curve
parametrizations. Values and first derivatives are controlled explicitly. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem signedCurveArea_stability {F G : ℝ → ℂ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    {A B ε η : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (hε : 0 ≤ ε) (_hη : 0 ≤ η)
    (hGval : ∀ t, ‖G t‖ ≤ A) (hGder : ∀ t, ‖deriv G t‖ ≤ B)
    (hval : ∀ t, ‖F t-G t‖ ≤ ε) (hder : ∀ t, ‖deriv F t-deriv G t‖ ≤ η) :
    |signedCurveArea F-signedCurveArea G| ≤ ε*B+(A+ε)*η := by
  have hFi : IntervalIntegrable (fun t => (F t).re*(deriv F t).im) volume 0 1 :=
    ((Complex.continuous_re.comp hF.continuous).mul
      (Complex.continuous_im.comp hF.continuous_deriv_one)).intervalIntegrable _ _
  have hGi : IntervalIntegrable (fun t => (G t).re*(deriv G t).im) volume 0 1 :=
    ((Complex.continuous_re.comp hG.continuous).mul
      (Complex.continuous_im.comp hG.continuous_deriv_one)).intervalIntegrable _ _
  unfold signedCurveArea
  rw [← intervalIntegral.integral_sub hFi hGi]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ε*B+(A+ε)*η) (fun t _ht => show
      ‖(F t).re*(deriv F t).im-(G t).re*(deriv G t).im‖ ≤ _ from by
      have hFn : ‖F t‖ ≤ A+ε := by
        calc
          _ = ‖(F t-G t)+G t‖ := by rw [sub_add_cancel]
          _ ≤ ‖F t-G t‖+‖G t‖ := norm_add_le _ _
          _ ≤ ε+A := add_le_add (hval t) (hGval t)
          _ = _ := add_comm _ _
      have heq : (F t).re*(deriv F t).im-(G t).re*(deriv G t).im =
          (F t-G t).re*(deriv G t).im+(F t).re*(deriv F t-deriv G t).im := by
        simp only [Complex.sub_re, Complex.sub_im]
        ring
      rw [heq]
      calc
        _ ≤ ‖(F t-G t).re*(deriv G t).im‖+‖(F t).re*(deriv F t-deriv G t).im‖ := norm_add_le _ _
        _ ≤ ‖F t-G t‖*‖deriv G t‖+‖F t‖*‖deriv F t-deriv G t‖ := by
          simp only [norm_mul, Real.norm_eq_abs]
          exact add_le_add
            (mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
              (abs_nonneg _) (norm_nonneg _))
            (mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
              (abs_nonneg _) (norm_nonneg _))
        _ ≤ _ := add_le_add
          (mul_le_mul (hval t) (hGder t) (norm_nonneg _) hε)
          (mul_le_mul hFn (hder t) (norm_nonneg _) (add_nonneg hA hε)))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrincipalCircleRemainder
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives of the actual analytic remainder on large circles.
The bounds will make its contribution to signed area tend to zero. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principalCircleRemainder_hasDerivAt {R : ℝ} (hR : 0 < R)
    {T : ℂ → ℂ} (t : ℝ) (hT : DifferentiableAt ℂ T (unitCircleParam 0 R t)⁻¹) :
    HasDerivAt (principalCircleRemainder R T)
      (2*(unitCircleParam 0 R t)⁻¹ *
          (-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2) *
          T (unitCircleParam 0 R t)⁻¹ +
        (unitCircleParam 0 R t)⁻¹^2 * (deriv T (unitCircleParam 0 R t)⁻¹ *
          (-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2))) t := by
  have hn : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  have hd : HasDerivAt (unitCircleParam 0 R) (deriv (unitCircleParam 0 R) t) t :=
    (unitCircleParam_hasDerivAt R t).differentiableAt.hasDerivAt
  have hi := hd.inv hn
  have ht := hT.hasDerivAt.comp t hi
  refine ((hi.pow 2).mul ht).congr_deriv (Eq.symm ?_)
  · norm_num


 theorem principalCircleRemainder_deriv_bound {R B C : ℝ} (hR : 1 ≤ R)
    (_hB : 0 ≤ B) (hC : 0 ≤ C) {T : ℂ → ℂ} (t : ℝ)
    (hT : DifferentiableAt ℂ T (unitCircleParam 0 R t)⁻¹)
    (hb : ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B)
    (hc : ‖deriv T (unitCircleParam 0 R t)⁻¹‖ ≤ C) :
    ‖deriv (principalCircleRemainder R T) t‖ ≤ 2*Real.pi*(2*B+C)/R^2 := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hn : ‖unitCircleParam 0 R t‖ = R := by
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
  have hi : ‖(unitCircleParam 0 R t)⁻¹‖ = R⁻¹ := by rw [norm_inv, hn]
  have hd : ‖-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2‖ = 2*Real.pi/R := by
    rw [norm_div, norm_neg, unitCircleParam_deriv_norm hRp.le, norm_pow, hn]
    field_simp
  rw [(principalCircleRemainder_hasDerivAt hRp t hT).deriv]
  calc
    _ ≤ ‖2*(unitCircleParam 0 R t)⁻¹ *
          (-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2) *
          T (unitCircleParam 0 R t)⁻¹‖ +
        ‖(unitCircleParam 0 R t)⁻¹^2 * (deriv T (unitCircleParam 0 R t)⁻¹ *
          (-(deriv (unitCircleParam 0 R) t)/(unitCircleParam 0 R t)^2))‖ := norm_add_le _ _
    _ = 2*R⁻¹*(2*Real.pi/R)*‖T (unitCircleParam 0 R t)⁻¹‖ +
        R⁻¹^2*(‖deriv T (unitCircleParam 0 R t)⁻¹‖*(2*Real.pi/R)) := by
      simp only [norm_mul, Complex.norm_ofNat, hi, hd, norm_pow]
    _ ≤ 2*R⁻¹*(2*Real.pi/R)*B + R⁻¹^2*(C*(2*Real.pi/R)) := by gcongr
    _ = 2*Real.pi*(2*B*R⁻¹^2+C*R⁻¹^3) := by field_simp
    _ ≤ 2*Real.pi*(2*B*R⁻¹^2+C*R⁻¹^2) := by
      have hri : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
      have hh : R⁻¹^3 ≤ R⁻¹^2 := by
        calc
          _ = R⁻¹^2*R⁻¹ := by ring
          _ ≤ R⁻¹^2*1 := mul_le_mul_of_nonneg_left hri (sq_nonneg _)
          _ = _ := mul_one _
      gcongr
    _ = _ := by field_simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_InverseCircleAnalytic
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic germ supplies one common large-circle range for
smoothness and bounds of both the remainder and its derivative. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem analyticAt_on_inverse_circles {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0) :
    ∀ᶠ R : ℝ in atTop, 1 ≤ R ∧ ∀ t : ℝ, AnalyticAt ℂ T (unitCircleParam 0 R t)⁻¹ := by
  obtain ⟨r, hr, hball⟩ := hT.exists_ball_analyticOnNhd
  filter_upwards [eventually_gt_atTop (max 1 r⁻¹)] with R hR
  have hRp : 0 < R := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hR)
  refine ⟨((le_max_left _ _).trans hR.le), ?_⟩
  intro t
  apply hball
  change dist (unitCircleParam 0 R t)⁻¹ 0 < r
  rw [dist_zero_right, norm_inv]
  simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
  exact (inv_lt_comm₀ hRp hr).mpr ((le_max_right _ _).trans_lt hR)

 theorem analytic_inverse_circle_bounds {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ᶠ R : ℝ in atTop,
      1 ≤ R ∧ ∀ t : ℝ, AnalyticAt ℂ T (unitCircleParam 0 R t)⁻¹ ∧
        ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B ∧
        ‖deriv T (unitCircleParam 0 R t)⁻¹‖ ≤ C := by
  obtain ⟨B, RB, hB, hb⟩ := inverse_circle_remainder_bound hT.continuousAt
  obtain ⟨C, RC, hC, hc⟩ := inverse_circle_remainder_bound hT.deriv.continuousAt
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [analyticAt_on_inverse_circles hT, eventually_ge_atTop RB,
    eventually_ge_atTop RC] with R hA hRB hRC
  refine ⟨hA.1, ?_⟩
  intro t
  exact ⟨hA.2 t, (hb R hRB).2 t, (hc R hRC).2 t⟩

 theorem principalCircleRemainder_smooth {R : ℝ} (hR : 0 < R) {T : ℂ → ℂ}
    (hT : ∀ t : ℝ, AnalyticAt ℂ T (unitCircleParam 0 R t)⁻¹) :
    ContDiff ℝ (⊤ : ℕ∞) (principalCircleRemainder R T) := by
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (unitCircleParam 0 R) :=
    (contDiff_circleMap 0 R).comp (contDiff_const.mul contDiff_id)
  have hn (t : ℝ) : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun t => (unitCircleParam 0 R t)⁻¹) := hγ.inv hn
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (hi.contDiffAt.pow 2).mul
    (((hT t).contDiffAt.restrict_scalars ℝ).comp t hi.contDiffAt)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalCircleAreaEstimate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic remainder contributes vanishing signed area. All
bounds here come from its actual values and first derivatives. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_area_budget_le {R K B C : ℝ} (hR : 1 ≤ R)
    (_hK : 0 ≤ K) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (B/R^2)*(2*Real.pi*K*R)+(K*R+B/R^2)*(2*Real.pi*(2*B+C)/R^2) ≤
      principalAreaErrorBudget K B C/R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hri : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hri0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hRp.le
  have hp : R⁻¹^4 ≤ R⁻¹ := by
    calc
      _ = R⁻¹*R⁻¹^3 := by ring
      _ ≤ R⁻¹*1^3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hri0 hri 3) hri0
      _ = _ := by ring
  calc
    _ = 2*Real.pi*K*(3*B+C)*R⁻¹+2*Real.pi*B*(2*B+C)*R⁻¹^4 := by
      field_simp
      ring
    _ ≤ 2*Real.pi*K*(3*B+C)*R⁻¹+2*Real.pi*B*(2*B+C)*R⁻¹ :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hp
        (show 0 ≤ 2*Real.pi*B*(2*B+C) by positivity))
    _ = _ := by unfold principalAreaErrorBudget; rw [div_eq_mul_inv]; ring

 theorem principal_circle_decomposition {F : ℂ → ℂ} {c : ℂ} {T : ℂ → ℂ}
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹)
    {R : ℝ} (hR : 0 < R) :
    (fun t => F (unitCircleParam 0 R t)) =
      principalLeadingCurve R c + principalCircleRemainder R T := by
  funext t
  have hn : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  have hh := hexp _ hn
  change F (unitCircleParam 0 R t) = unitCircleParam 0 R t+c/unitCircleParam 0 R t +
    (unitCircleParam 0 R t)⁻¹^2*T (unitCircleParam 0 R t)⁻¹
  rw [div_eq_mul_inv]
  linear_combination hh

 theorem principal_circle_area_estimate {F : ℂ → ℂ} {c : ℂ} {T : ℂ → ℂ}
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹)
    {R B C : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : ∀ t : ℝ, AnalyticAt ℂ T (unitCircleParam 0 R t)⁻¹)
    (hb : ∀ t : ℝ, ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B)
    (hc : ∀ t : ℝ, ‖deriv T (unitCircleParam 0 R t)⁻¹‖ ≤ C) :
    |signedCurveArea (fun t => F (unitCircleParam 0 R t)) -
      (Real.pi*R^2-Real.pi*‖c‖^2/R^2)| ≤ principalAreaErrorBudget (1+‖c‖) B C/R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let γ : ℝ → ℂ := fun t => F (unitCircleParam 0 R t)
  let G := principalLeadingCurve R c
  let E := principalCircleRemainder R T
  have heq : γ = G+E := principal_circle_decomposition hexp hRp
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := principalLeadingCurve_smooth hRp c
  have hE : ContDiff ℝ (⊤ : ℕ∞) E := principalCircleRemainder_smooth hRp hT
  have hγ : ContDiff ℝ (⊤ : ℕ∞) γ := by rw [heq]; exact hG.add hE
  have hval (t : ℝ) : ‖γ t-G t‖ ≤ B/R^2 := by
    rw [heq]
    simp only [Pi.add_apply, add_sub_cancel_left]
    change ‖(unitCircleParam 0 R t)⁻¹^2*T (unitCircleParam 0 R t)⁻¹‖ ≤ _
    rw [norm_mul, norm_pow, norm_inv]
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
    calc
      _ ≤ R⁻¹^2*B := mul_le_mul_of_nonneg_left (hb t) (sq_nonneg _)
      _ = _ := by field_simp
  have hder (t : ℝ) : ‖deriv γ t-deriv G t‖ ≤ 2*Real.pi*(2*B+C)/R^2 := by
    rw [heq, deriv_add (hG.differentiable (by simp)).differentiableAt
      (hE.differentiable (by simp)).differentiableAt, add_sub_cancel_left]
    exact principalCircleRemainder_deriv_bound hR hB hC t (hT t).differentiableAt (hb t) (hc t)
  have hs := signedCurveArea_stability (hγ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hG.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (show 0 ≤ (1+‖c‖)*R by positivity)
    (show 0 ≤ 2*Real.pi*(1+‖c‖)*R by positivity)
    (show 0 ≤ B/R^2 by positivity) (show 0 ≤ 2*Real.pi*(2*B+C)/R^2 by positivity)
    (principalLeadingCurve_norm hR c) (principalLeadingCurve_deriv_norm hR c) hval hder
  dsimp only [γ, G] at hs
  rw [principal_leading_circle_area R hRp c] at hs
  exact hs.trans (principal_area_budget_le hR (by positivity) hB hC)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalCircleAreaLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The principal exterior germ determines the limiting signed image area. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_circle_area_limit {F : ℂ → ℂ} {c : ℂ} {T : ℂ → ℂ}
    (hT : AnalyticAt ℂ T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
    Tendsto (fun R : ℝ => signedCurveArea (fun t => F (unitCircleParam 0 R t)) -
      Real.pi*R^2) atTop (𝓝 0) := by
  obtain ⟨B, C, hB, hC, hbounds⟩ := analytic_inverse_circle_bounds hT
  let M := principalAreaErrorBudget (1+‖c‖) B C
  have hlim : Tendsto (fun R : ℝ => M/R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)))
  have herr : Tendsto (fun R : ℝ => signedCurveArea (fun t => F (unitCircleParam 0 R t)) -
      signedCurveArea (principalLeadingCurve R c)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hbounds] with R hR
    rw [Real.norm_eq_abs, principal_leading_circle_area R
      (lt_of_lt_of_le zero_lt_one hR.1) c]
    exact principal_circle_area_estimate hexp hR.1 hB hC
      (fun t => (hR.2 t).1) (fun t => (hR.2 t).2.1) (fun t => (hR.2 t).2.2)
  have hbase : Tendsto (fun R : ℝ => signedCurveArea (principalLeadingCurve R c) -
      Real.pi*R^2) atTop (𝓝 0) := by
    have hh : Tendsto (fun R : ℝ => (-Real.pi*‖c‖^2)*(R⁻¹)^2) atTop (𝓝 0) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
        ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).pow 2).const_mul
          (-Real.pi*‖c‖^2)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [principal_leading_circle_area R hR c]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have hh := herr.add hbase
  convert hh using 1
  · funext R
    ring
  · simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityJacobianLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual weak Jacobian has vanishing area defect at infinity. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.jacobian_area_limit_oai
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀)
    {c : ℂ} {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
    Tendsto (fun R : ℝ =>
      (∫ x in ball (0 : EuclideanPlane) R,
        D.realGradient x 0 * D.imagGradient x 1 -
          D.realGradient x 1 * D.imagGradient x 0) -
        (volume (ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 0) := by
  apply (principal_circle_area_limit hT hexp).congr'
  filter_upwards [eventually_gt_atTop r₀] with R hR
  rw [D.jacobian_boundary hgreen hφ hF hh hr₀ hFr hR,
    physical_real_volume_ball R (hr₀.trans hR).le]
  rfl

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.PlaneLocalWeakComplex.jacobian_area_limit_oai := @OAI.CircleDomainRigidity.PlaneLocalWeakComplex.jacobian_area_limit_oai
