-- Prove2me | solution 1 for OAI.CircleDomainRigidity.exteriorOmittedAreaTheorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:42:09.791105+00:00
-- url     : https://prove2.me/submissions/848bd6a8-0aff-4a46-a205-76177e300c21

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C008

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletionUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isConnected_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsConnected (openCompletedRegion H) := by
  let S : Set ℂ := (⋃ i, closure (jordanInterior (H i)))ᶜ
  have hS : IsPreconnected S := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hinf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    have hmem : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ∈ S := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_iUnion fun i => isCompact_closure_jordanInterior (H i)).compl_mem_cocompact
    exact mem_closure_of_tendsto OnePoint.tendsto_coe_infty
      (hmem.mono fun z hz => ⟨z, hz, rfl⟩)
  have hsub : ((↑) : ℂ → Sphere) '' S ⊆ openCompletedRegion H := by
    rintro _ ⟨z, hz, rfl⟩ hb
    obtain ⟨i, x, hx, heq⟩ := mem_iUnion.mp hb
    have hxz : x = z := OnePoint.coe_injective heq
    exact hz (mem_iUnion.mpr ⟨i, hxz ▸ hx⟩)
  have hupper : openCompletedRegion H ⊆ closure (((↑) : ℂ → Sphere) '' S) := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply subset_closure
      refine ⟨z, ?_, rfl⟩
      intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  refine ⟨⟨∞, ?_⟩, (hS.image _ OnePoint.continuous_coe.continuousOn).subset_closure hsub hupper⟩
  intro hb
  obtain ⟨i, z, _, heq⟩ := mem_iUnion.mp hb
  exact OnePoint.coe_ne_infty z heq

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LimitSphereExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extending a principally normalized limit across infinity

The uniform principal remainder does more than prevent a constant
limit: it gives continuity on the sphere and chart derivative one at
infinity. This step needs no further analytic input.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuousAt_extendAtInfinity_infty {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ContinuousAt (extendAtInfinity F) OnePoint.infty := by
  rw [OnePoint.continuousAt_infty']
  change Tendsto (fun z : ℂ => (F z : Sphere)) (coclosedCompact ℂ) (𝓝 OnePoint.infty)
  have hcoe : Tendsto ((↑) : ℂ → Sphere) (cobounded ℂ) (𝓝 OnePoint.infty) := by
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (OnePoint.tendsto_coe_infty (X := ℂ))
  rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  exact hcoe.comp (principal_tendsto_cobounded hF)

theorem hasDerivAt_extendAtInfinity_chart {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    HasDerivAt (fun u => chart OnePoint.infty
      (extendAtInfinity F (chartSymm OnePoint.infty u))) 1 0 := by
  let G : ℂ → ℂ := fun u => chart OnePoint.infty
    (extendAtInfinity F (chartSymm OnePoint.infty u))
  have hG0 : G 0 = 0 := by simp [G, chart, chartSymm, sphereInv, finiteCoord]
  have hGu (u : ℂ) (hu : u ≠ 0) : G u = (F u⁻¹)⁻¹ := by
    simp only [G, chart, chartSymm, ite_true, if_true]
    have hsu : sphereInv (u : Sphere) = (u⁻¹ : ℂ) := by simp [sphereInv, hu]
    rw [hsu, extendAtInfinity_coe, finiteCoord_sphereInv_coe]
  have hid : Tendsto (fun u : ℂ => u) (𝓝[≠] (0 : ℂ)) (𝓝 0) := nhdsWithin_le_nhds
  have he := hid.mul ((principal_remainder_tendsto_zero hF).comp
    (tendsto_inv₀_nhdsNE_zero (α := ℂ)))
  have hprod : Tendsto (fun u : ℂ => u * F u⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℂ))).add he
    simp only [zero_mul, add_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : u ≠ 0 := hu
    change 1 + u * (F u⁻¹ - u⁻¹) = u * F u⁻¹
    rw [mul_sub, mul_inv_cancel₀ hu']
    ring
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h := hprod.inv₀ one_ne_zero
  simp only [inv_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u ≠ 0 := hu
  change (u * F u⁻¹)⁻¹ = slope G 0 u
  rw [slope_def_field, hG0, sub_zero, sub_zero, hGu u hu', div_eq_mul_inv, mul_inv_rev]

theorem isConformalAt_extendAtInfinity_infty {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalAt (extendAtInfinity F) OnePoint.infty := by
  refine ⟨continuousAt_extendAtInfinity_infty hF, 1, one_ne_zero, ?_⟩
  simpa only [extendAtInfinity_infty, chart_infty_self] using hasDerivAt_extendAtInfinity_chart hF

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_LimitConformality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conformality of the normalized limit

`HurwitzZeroFreeLimit` records the zero-free form of the same published
Hurwitz theorem already used for injective limits: Ahlfors, *Complex
Analysis*, third edition (1979), Chapter 5, Theorem 2, p. 178. Applied
to the derivatives, it gives a nonzero limiting derivative unless the
limit is constant. The latter alternative is ruled out on each core.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isConformalOn_extendAtInfinity
    {D : Set ℂ} {F : ℂ → ℂ} (hD : IsOpen D) (hF : DifferentiableOn ℂ F D)
    (hd : ∀ z ∈ D, deriv F z ≠ 0)
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  rintro p (⟨z, hz, rfl⟩ | hp)
  · exact isConformalAt_extendAtInfinity_coe
      ((hF z hz).differentiableAt (hD.mem_nhds hz)) (hd z hz)
  · rw [mem_singleton_iff] at hp
    subst p
    exact isConformalAt_extendAtInfinity_infty hnorm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedLimitEquivalence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized limit as a sphere conformal equivalence

The source includes infinity. The inverse on the image is constructed
by the local inverse theorem, so the limiting map satisfies the same
two-sided conformal predicate as the final circle-domain target.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isOpen_finite_domain_with_infty
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsOpen (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hc : IsCompact Dᶜ := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hD.isClosed_compl
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    exact hz (hext (le_of_lt (lt_of_not_ge hn)))
  apply (OnePoint.isOpen_iff_of_mem' (by simp)).mpr
  simpa only [preimage_union, OnePoint.coe_injective.preimage_image,
    OnePoint.coe_preimage_infty, union_empty] using And.intro hc hD

theorem injOn_extendAtInfinity
    {D : Set ℂ} {F : ℂ → ℂ} (hF : InjOn F D) :
    InjOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  rintro p (⟨z, hz, rfl⟩ | hp) q (⟨w, hw, rfl⟩ | hq) he
  · exact congrArg ((↑) : ℂ → Sphere) (hF hz hw (OnePoint.coe_injective he))
  · rw [mem_singleton_iff] at hq
    subst q
    exact (OnePoint.coe_ne_infty (F z) he).elim
  · rw [mem_singleton_iff] at hp
    subst p
    exact (OnePoint.coe_ne_infty (F w) he.symm).elim
  · rw [mem_singleton_iff] at hp hq
    exact hp.trans hq.symm

end CircleDomainRigidity

end

end OAI
end

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothImageArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorDerivativeMean
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact angular mean of the derivative of a principal exterior
map. Inversion turns the derivative into a holomorphic disk function
with value one at its center. No area inequality is used. -/
open Set Filter Function Metric Asymptotics Bornology Real
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma circleAverage_comp_inv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (r : ℝ) :
    circleAverage (fun z => f z⁻¹) 0 r = circleAverage f 0 r⁻¹ := by
  rw [circleAverage_eq_circleAverage_zero_one,
    circleAverage_eq_circleAverage_zero_one (f := f)]
  simp only [add_zero, mul_inv_rev, Complex.ofReal_inv]
  have he : (fun z : ℂ => f (z⁻¹ * (r : ℂ)⁻¹)) =
      (fun z : ℂ => f ((r : ℂ)⁻¹ * z)) ∘ (fun z => z⁻¹) := by
    funext z
    simp only [comp_apply, mul_comm]
  rw [he]
  simpa only [Function.comp_def] using
    (circleAverage_zero_one_congr_inv (f := fun z : ℂ => f ((r : ℂ)⁻¹ * z)))

lemma invertedPrincipalRemainder_analyticOnNhd {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) :
    AnalyticOnNhd ℂ (invertedPrincipalRemainder F) (ball 0 R⁻¹) := by
  have hfar : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
    exact (hF z hz).differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    exact invertedPrincipalRemainder_analytic hfar ht
  · have hwR : R < ‖w⁻¹‖ := by
      rw [norm_inv]
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hwlt : ‖w‖ < R⁻¹ := by simpa only [mem_ball, dist_zero_right] using hw
      exact (lt_inv_comm₀ hR hwpos).mpr hwlt
    have ha := hF.analyticAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hwR)
    have hi : AnalyticAt ℂ (fun z : ℂ => z⁻¹) w := analyticAt_inv hw0
    apply ((ha.comp hi).sub hi).congr
    filter_upwards [isOpen_ne.mem_nhds hw0] with z hz
    exact (Function.update_of_ne hz _ _).symm

lemma invertedPrincipalDerivative_zero (F : ℂ → ℂ) :
    invertedPrincipalDerivative F 0 = 1 := by simp [invertedPrincipalDerivative]

lemma invertedPrincipalDerivative_eq {F : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0)
    (hF : DifferentiableAt ℂ F w⁻¹) :
    invertedPrincipalDerivative F w = deriv F w⁻¹ := by
  have hi : HasDerivAt (fun z : ℂ => z⁻¹) (-w⁻¹^2) w := by
    simpa only [inv_pow] using (hasDerivAt_inv hw)
  have hu := (hF.hasDerivAt.comp w hi).sub hi
  have hue : HasDerivAt (invertedPrincipalRemainder F)
      (deriv F w⁻¹ * (-w⁻¹^2) - (-w⁻¹^2)) w := by
    apply hu.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hw] with z hz
    exact Function.update_of_ne hz _ _
  rw [invertedPrincipalDerivative, hue.deriv]
  field_simp
  ring

lemma exterior_derivative_circleAverage {F : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) (hr : R < r) :
    circleAverage (deriv F) 0 r = 1 := by
  have hrp : 0 < r := hR.trans hr
  have hu := invertedPrincipalRemainder_analyticOnNhd hR hF ht
  have hv : AnalyticOnNhd ℂ (invertedPrincipalDerivative F) (ball 0 R⁻¹) := by
    intro w hw
    exact analyticAt_const.sub ((analyticAt_id.pow 2).mul
      ((hu w hw).deriv))
  have hsub : closedBall (0 : ℂ) r⁻¹ ⊆ ball 0 R⁻¹ := by
    intro w hw
    have hh : r⁻¹ < R⁻¹ := inv_lt_inv₀ hrp hR |>.mpr hr
    exact (show dist w 0 ≤ r⁻¹ from hw).trans_lt hh
  have hav : circleAverage (invertedPrincipalDerivative F) 0 r⁻¹ = 1 := by
    rw [← invertedPrincipalDerivative_zero F]
    apply circleAverage_of_differentiable_on_off_countable (s := ∅)
      countable_empty
    · simpa only [abs_of_pos (inv_pos.mpr hrp)] using
        (hv.continuousOn.mono hsub)
    · intro w hw
      exact (hv w (hsub (ball_subset_closedBall (by
        simpa only [sdiff_empty, abs_of_pos (inv_pos.mpr hrp)] using hw)))).differentiableAt
  rw [← circleAverage_comp_inv] at hav
  refine (circleAverage_congr_sphere (fun z hz => ?_)).trans hav
  have hzn : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right, abs_of_pos hrp] using hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzn]; exact hrp.ne')
  have hdz : DifferentiableAt ℂ F z⁻¹⁻¹ := by
    simpa only [inv_inv] using ((hF z (by simpa only [mem_ofPred_eq, hzn] using hr)).differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (by simpa only [mem_ofPred_eq, hzn] using hr)))
  simpa only [inv_inv] using (invertedPrincipalDerivative_eq (inv_ne_zero hz0) hdz).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorCircleEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular energy of a principal exterior derivative is at least
one. The proof keeps the actual derivative and uses its exact mean. -/
open Set Filter Function Metric Asymptotics Bornology Real MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_derivative_continuousOn_circle {F : ℂ → ℂ} {R r : ℝ}
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hr : R < r) :
    ContinuousOn (deriv F) (sphere 0 r) := by
  apply (hF.deriv (isOpen_lt continuous_const continuous_norm)).continuousOn.mono
  intro z hz
  simpa only [mem_ofPred_eq, (mem_sphere_zero_iff_norm.mp hz)] using hr

lemma exterior_derivative_circle_energy {F : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) (hr : R < r) :
    1 ≤ circleAverage (fun z => ‖deriv F z‖^2) 0 r := by
  have hrp : 0 < r := hR.trans hr
  have hc := exterior_derivative_continuousOn_circle hF hr
  have hci := hc.circleIntegrable hrp.le
  have hcre := Complex.continuous_re.comp_continuousOn hc
  have hm : circleAverage (fun z => (deriv F z).re) 0 r = 1 := by
    have he := Complex.reCLM.circleAverage_comp_comm hci
    change circleAverage (fun z => (deriv F z).re) 0 r =
      (circleAverage (deriv F) 0 r).re at he
    simpa only [exterior_derivative_circleAverage hR hF ht hr, Complex.one_re] using he
  have hc2 : CircleIntegrable (fun z => 2*(deriv F z).re-1) 0 r := ((continuousOn_const.mul hcre).sub continuousOn_const).circleIntegrable hrp.le
  have hcn : CircleIntegrable (fun z => ‖deriv F z‖^2) 0 r := (hc.norm.pow 2).circleIntegrable hrp.le
  have hcm : CircleIntegrable (fun z => 2*(deriv F z).re) 0 r :=
    (continuousOn_const.mul hcre).circleIntegrable hrp.le
  have hav : circleAverage (fun z => 2*(deriv F z).re-1) 0 r = 1 := by
    rw [circleAverage_fun_sub hcm
      (circleIntegrable_const 1 0 r)]
    have he : circleAverage (fun z => 2*(deriv F z).re) 0 r =
        2*circleAverage (fun z => (deriv F z).re) 0 r :=
      circleAverage_fun_smul (a := (2 : ℝ))
    rw [he, hm, circleAverage_const]
    norm_num
  rw [← hav]
  apply circleAverage_mono hc2 hcn
  intro z _
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg ((deriv F z).re-1), sq_nonneg (deriv F z).im]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorAngularEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact angular-energy lower bound in the nonnegative integral
used by polar change of variables. -/
open Set Filter Function Metric Asymptotics Bornology Real MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exterior_derivative_angular_energy {F : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) (hr : R < r) :
    ENNReal.ofReal (2*Real.pi) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (‖deriv F (circleMap 0 r θ)‖^2) := by
  have hrp : 0 < r := hR.trans hr
  let g : ℝ → ℝ := fun θ => ‖deriv F (circleMap 0 r θ)‖^2
  have hc : Continuous g := by
    apply (exterior_derivative_continuousOn_circle hF hr).norm.pow 2 |>.comp_continuous
      (continuous_circleMap 0 r)
    intro θ
    simpa only [abs_of_pos hrp] using circleMap_mem_sphere' (0 : ℂ) r θ
  have hi : IntegrableOn g (Ioo (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])).mp
      (hc.intervalIntegrable _ _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun θ => sq_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  have he : (∫ θ in Ioo (-Real.pi) Real.pi, g θ) = ∫ θ in (0 : ℝ)..2*Real.pi, g θ := by
    have hp : Periodic g (2*Real.pi) := by
      intro θ
      dsimp only [g]
      rw [periodic_circleMap 0 r θ]
    have hs := hp.intervalIntegral_add_eq (-Real.pi) 0
    have ha : -Real.pi+2*Real.pi = Real.pi := by ring
    rw [ha, zero_add, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo] at hs
    exact hs
  rw [he]
  have hav := exterior_derivative_circle_energy hR hF ht hr
  change 1 ≤ (2*Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2*Real.pi, g θ) at hav
  simpa only [mul_one] using (le_inv_mul_iff₀ (by positivity : 0 < 2*Real.pi)).mp hav

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PolarAnnulusEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polar integration on a bounded annulus, with the actual radial weight. -/
open Set Filter Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem lintegral_polar_annulus (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    {a b : ℝ} (ha : 0 ≤ a) :
    (∫⁻ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, g z) =
      ∫⁻ r in Ioo a b, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * g (Complex.polarCoord.symm (r, θ)) := by
  let A := {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}
  let S := Ioo a b
  let T := Ioo (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p)
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hP : MeasurableSet polarCoord.target :=
    polarCoord.open_target.measurableSet
  have hf : Measurable f := by
    apply Measurable.mul (ENNReal.measurable_ofReal.comp measurable_fst)
    apply hg.comp
    change Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hpolar := Complex.lintegral_comp_polarCoord_symm (A.indicator g)
  rw [lintegral_indicator hA] at hpolar
  calc
    _ = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * (A.indicator g) (Complex.polarCoord.symm p) := hpolar.symm
    _ = ∫⁻ p, (S ×ˢ T).indicator f p := by
      rw [← lintegral_indicator hP]
      apply lintegral_congr
      intro p
      by_cases hp : p ∈ polarCoord.target
      · have hp0 : 0 < p.1 := hp.1
        have hmem : Complex.polarCoord.symm p ∈ A ↔ p.1 ∈ S := by
          simp only [A, S, mem_ofPred_eq, mem_Ioo, Complex.norm_polarCoord_symm,
            abs_of_pos hp0]
        by_cases hS : p.1 ∈ S
        · have hST : p ∈ S ×ˢ T := ⟨hS, hp.2⟩
          rw [indicator_of_mem hp, indicator_of_mem hST, indicator_of_mem (hmem.mpr hS)]
        · have hST : p ∉ S ×ˢ T := fun h => hS h.1
          rw [indicator_of_mem hp, indicator_of_notMem hST,
            indicator_of_notMem (fun h => hS (hmem.mp h)), mul_zero]
      · have hST : p ∉ S ×ˢ T := by
          rintro ⟨hS, hT⟩
          exact hp ⟨lt_of_le_of_lt ha hS.1, hT⟩
        rw [indicator_of_notMem hp, indicator_of_notMem hST]
    _ = ∫⁻ p in S ×ˢ T, f p := lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo) f
    _ = _ := setLIntegral_prod f hf.aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PolarAnnulusIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polar integration on a bounded annulus, with nonnegative measurable
integrands. The angular interval is fixed to the standard polar chart. -/
open Set MeasureTheory Metric Real
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma complex_polar_symm_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply]
  apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

lemma lintegral_circleMap_annulus (q : ℂ → ℝ≥0∞) (hq : Measurable q)
    {a b : ℝ} (ha : 0 ≤ a) :
    (∫⁻ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, q z) =
      ∫⁻ r in Ioo a b, ENNReal.ofReal r *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, q (circleMap 0 r θ) := by
  rw [lintegral_polar_annulus q hq ha]
  apply lintegral_congr
  intro r
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  apply lintegral_congr
  intro θ
  rw [complex_polar_symm_circleMap]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorAnnulusEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A principal holomorphic exterior map pays at least the Euclidean
area of each source annulus in squared derivative energy. -/
open Set Filter Function Metric Asymptotics Bornology Real MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma polar_constant_annulus_energy {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ r in Ioo a b, ENNReal.ofReal r * ENNReal.ofReal (2*Real.pi)) =
      ENNReal.ofReal (Real.pi*(b^2-a^2)) := by
  have hi : IntegrableOn (fun r : ℝ => r*(2*Real.pi)) (Ioo a b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
      ((continuous_id.mul continuous_const).intervalIntegrable _ _)
  have he : (∫ r in Ioo a b, r*(2*Real.pi)) = Real.pi*(b^2-a^2) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_mul_const, integral_id]
    ring
  calc
    _ = ∫⁻ r in Ioo a b, ENNReal.ofReal (r*(2*Real.pi)) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      change ENNReal.ofReal r * ENNReal.ofReal (2*Real.pi) = ENNReal.ofReal (r*(2*Real.pi))
      rw [ENNReal.ofReal_mul (ha.trans hr.1.le)]
    _ = ENNReal.ofReal (∫ r in Ioo a b, r*(2*Real.pi)) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hi
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact mul_nonneg (ha.trans hr.1.le) (by positivity)
    _ = _ := by rw [he]

lemma exterior_annulus_energy {F : ℂ → ℂ} {R a b : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0))
    (ha : R < a) (hab : a ≤ b) :
    ENNReal.ofReal (Real.pi*(b^2-a^2)) ≤
      ∫⁻ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, ENNReal.ofReal (‖deriv F z‖^2) := by
  have hap : 0 ≤ a := (hR.trans ha).le
  rw [lintegral_circleMap_annulus _ ((measurable_deriv F).norm.pow_const 2).ennreal_ofReal hap,
    ← polar_constant_annulus_energy hap hab]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  gcongr
  exact exterior_derivative_angular_energy hR hF ht (ha.trans hr.1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalComplexJacobianForm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local smooth Jacobian one-forms, on the actual open set where a map
is smooth. Their curl is the determinant of its real differential. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma smooth_complex_partial_commute_at {v : ℂ → ℝ} {z : ℂ}
    (hv : ContDiffAt ℝ (⊤ : ℕ∞) v z) (p q : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ v w q) z p =
      fderiv ℝ (fun w => fderiv ℝ v w p) z q := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) z :=
    ((hv.fderiv_right (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by norm_num))
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact hv.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _ _

lemma smooth_complex_partial_on {v : ℂ → ℝ} {O : Set ℂ}
    (hO : IsOpen O) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v O) (p : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ v z p) O := by
  intro z hz
  exact (((hv.contDiffAt (hO.mem_nhds hz)).fderiv_right (m := (⊤ : ℕ∞)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply
    contDiffAt_const).contDiffWithinAt

lemma smooth_complex_jacobian_curl {a b : ℂ → ℝ} {O : Set ℂ}
    (hO : IsOpen O) (ha : ContDiffOn ℝ (⊤ : ℕ∞) a O)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b O) {z : ℂ} (hz : z ∈ O) :
    fderiv ℝ (fun z => a z * fderiv ℝ b z Complex.I) z 1 -
        fderiv ℝ (fun z => a z * fderiv ℝ b z 1) z Complex.I =
      fderiv ℝ a z 1 * fderiv ℝ b z Complex.I -
        fderiv ℝ a z Complex.I * fderiv ℝ b z 1 := by
  have had := (ha.contDiffAt (hO.mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hbd (p : ℂ) := ((smooth_complex_partial_on hO hb p).contDiffAt
    (hO.mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [fderiv_fun_mul had (hbd Complex.I), fderiv_fun_mul had (hbd 1)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [smooth_complex_partial_commute_at (hb.contDiffAt (hO.mem_nhds hz)) 1 Complex.I]
  ring

lemma holomorphic_real_jacobian {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) :
    fderiv ℝ (fun w => (F w).re) z 1 * fderiv ℝ (fun w => (F w).im) z Complex.I -
        fderiv ℝ (fun w => (F w).re) z Complex.I * fderiv ℝ (fun w => (F w).im) z 1 =
      ‖deriv F z‖^2 := by
  have hd := hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hre := (Complex.reCLM.hasFDerivAt.comp z hd).fderiv
  have him := (Complex.imCLM.hasFDerivAt.comp z hd).fderiv
  change fderiv ℝ (Complex.reCLM ∘ F) z 1 * fderiv ℝ (Complex.imCLM ∘ F) z Complex.I -
    fderiv ℝ (Complex.reCLM ∘ F) z Complex.I * fderiv ℝ (Complex.imCLM ∘ F) z 1 = _
  rw [hre, him]
  change (1 * deriv F z).re * (Complex.I * deriv F z).im -
    (Complex.I * deriv F z).re * (1 * deriv F z).im = _
  simp only [one_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, zero_sub, Complex.sq_norm, Complex.normSq_apply]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalImageAreaForm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The boundary-area identity requires smoothness only along the
actual parametrized curve. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma signedCurveArea_local_image {F : ℂ → ℂ} {γ : ℝ → ℂ}
    (hF : ∀ t, DifferentiableAt ℝ F (γ t)) (hγ : Differentiable ℝ γ) :
    signedCurveArea (F ∘ γ) =
      planarFormIntegral (fun z => (F z).re * fderiv ℝ (fun w => (F w).im) z 1)
        (fun z => (F z).re * fderiv ℝ (fun w => (F w).im) z Complex.I) γ := by
  unfold signedCurveArea planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [Function.comp_def]
  have hd := (hF t).hasFDerivAt.comp_hasDerivAt t (hγ t).hasDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp (γ t) (hF t).hasFDerivAt
  have hie (v : ℂ) : fderiv ℝ (fun w => (F w).im) (γ t) v =
      (fderiv ℝ F (γ t) v).im := by
    change fderiv ℝ (Complex.imCLM ∘ F) (γ t) v = _
    rw [hi.fderiv]
    rfl
  have hde : deriv (fun x => F (γ x)) t = fderiv ℝ F (γ t) (deriv γ t) := by
    simpa only [Function.comp_def] using hd.deriv
  rw [hde, ← hie, complex_real_linear_decomposition]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RoundAnnulusGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing signed Green input on a round annulus. The outer sign
is fixed by its zero-hole radial-form specialization. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma round_annulus_green (hgreen : UnorientedFiniteCircleGreenFormula)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : closedBall (0 : ℂ) b \ ball 0 a ⊆ O)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ (⊤ : ℕ∞) P O)
    (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q O) :
    planarFormIntegral P Q (unitCircleParam 0 b) -
      planarFormIntegral P Q (unitCircleParam 0 a) =
      ∫ z in ball (0 : ℂ) b \ closedBall 0 a,
        (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨e, _, hg⟩ := hgreen (roundDiskChart b hb) (unitCircleParam 0 b)
    (unitCircleParam_regular b hb)
  have hzero := hg 0 Fin.elim0 Fin.elim0 (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    univ isOpen_univ (subset_univ _) (fun z => -z.im) (fun z => z.re)
    Complex.imCLM.contDiff.neg.contDiffOn Complex.reCLM.contDiff.contDiffOn
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
    iUnion_of_empty, sdiff_empty, roundDiskChart_interior] at hzero
  rw [← round_disk_green hgreen b hb univ isOpen_univ (subset_univ _)
    (fun z : ℂ => -z.im) (fun z : ℂ => z.re)
      Complex.imCLM.contDiff.neg.contDiffOn Complex.reCLM.contDiff.contDiffOn,
    radial_form_unitCircleParam] at hzero
  have he : e = 1 := by
    have hp : 0 < 2*Real.pi*b^2 := by positivity
    nlinarith
  have h := hg 1 (fun _ => 0) (fun _ => a) (fun _ => ha)
    (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
    (by intro i; rw [roundDiskChart_interior]; exact closedBall_subset_ball hab)
    O hO (by simpa only [roundDiskChart_interior, iUnion_const,
      closure_ball _ hb.ne'] using hsub) P Q hP hQ
  simpa only [he, one_mul, Fin.sum_univ_one, roundDiskChart_interior, iUnion_const] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleFormBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual boundary terms for the finite-circle Stokes formula. Smoothness
and integrability of real lifts follow from the circle coordinate, rather
than being extra analytic hypotheses on each boundary. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem contDiff_unitCircleParam (c : ℂ) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (unitCircleParam c r) :=
  (contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorAnnulusArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Green's identity on the actual source annulus computes the increase
of signed image-circle area as its squared holomorphic derivative. -/
open Set Filter Function MeasureTheory Metric Asymptotics Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exterior_annulus_area (hgreen : UnorientedFiniteCircleGreenFormula)
    {F : ℂ → ℂ} {R a b : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (ha : R < a) (hab : a < b) :
    signedCurveArea (fun t => F (unitCircleParam 0 b t)) -
      signedCurveArea (fun t => F (unitCircleParam 0 a t)) =
        ∫ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, ‖deriv F z‖^2 := by
  let O : Set ℂ := {z | R < ‖z‖}
  have hO : IsOpen O := isOpen_lt continuous_const continuous_norm
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) F O := (hF.contDiffOn hO).restrict_scalars ℝ
  have hRe : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (F z).re) O :=
    Complex.reCLM.contDiff.contDiffOn.comp hsm (mapsTo_univ _ _)
  have hIm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (F z).im) O :=
    Complex.imCLM.contDiff.contDiffOn.comp hsm (mapsTo_univ _ _)
  have hdiff (r : ℝ) (hr : R < r) (t : ℝ) : DifferentiableAt ℝ F (unitCircleParam 0 r t) := by
    have hz : unitCircleParam 0 r t ∈ O := by
      simpa only [O, mem_ofPred_eq, unitCircleParam, norm_circleMap_zero,
        abs_of_pos (hR.trans hr)] using hr
    exact ((hF _ hz).differentiableAt (hO.mem_nhds hz)).restrictScalars ℝ
  have hcurve (r : ℝ) : Differentiable ℝ (unitCircleParam 0 r) :=
    (contDiff_unitCircleParam 0 r).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [show (fun t => F (unitCircleParam 0 b t)) = F ∘ unitCircleParam 0 b from rfl,
    show (fun t => F (unitCircleParam 0 a t)) = F ∘ unitCircleParam 0 a from rfl,
    signedCurveArea_local_image (hdiff b (ha.trans hab)) (hcurve b),
    signedCurveArea_local_image (hdiff a ha) (hcurve a)]
  rw [round_annulus_green hgreen (hR.trans ha) hab O hO (by
    intro z hz
    have hza : a ≤ ‖z‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hz.2
    exact ha.trans_le hza) _ _ (hRe.mul (smooth_complex_partial_on hO hIm 1))
      (hRe.mul (smooth_complex_partial_on hO hIm Complex.I))]
  have he : ball (0 : ℂ) b \ closedBall 0 a = {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
    ext z
    simp only [Set.mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, not_le, mem_ofPred_eq, and_comm]
  rw [he]
  apply setIntegral_congr_fun ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet
  intro z hz
  have hzO : z ∈ O := ha.trans hz.1
  dsimp only
  rw [smooth_complex_jacobian_curl hO hRe hIm hzO]
  exact holomorphic_real_jacobian ((hF z hzO).differentiableAt (hO.mem_nhds hzO))

lemma exterior_annulus_energy_integrable {F : ℂ → ℂ} {R a b : ℝ}
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (ha : R < a) :
    IntegrableOn (fun z => ‖deriv F z‖^2) {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
  let C : Set ℂ := closedBall 0 b \ ball 0 a
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) b).diff isOpen_ball
  have hCO : C ⊆ {z : ℂ | R < ‖z‖} := by
    intro z hz
    exact ha.trans_le (by simpa only [mem_ball, dist_zero_right, not_lt] using hz.2)
  have hc : IntegrableOn (fun z => ‖deriv F z‖^2) C volume := (((hF.deriv (isOpen_lt continuous_const continuous_norm)).continuousOn.norm.pow 2).mono hCO).integrableOn_compact hC
  apply hc.mono_set
  intro z hz
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hz.2.le,
    by simpa only [mem_ball, dist_zero_right, not_lt] using hz.1.le⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed cores bounded by a finite disjoint Jordan family

The closed common exterior is regular closed, its interior is the already
constructed connected open completed region, and its boundary is exactly
the union of the specified Jordan curves.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem interior_finite_disjoint_closed
    {I : Type*} [Finite I] (C : I → Set Sphere)
    (hC : ∀ i, IsClosed (C i)) (hd : Pairwise (Disjoint on C)) :
    interior (⋃ i, C i) = ⋃ i, interior (C i) := by
  classical
  apply Subset.antisymm
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hp)
    let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, C j
    have hB : IsClosed B := isClosed_iUnion_of_finite fun j => hC j
    have hpB : p ∉ B := by
      intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact Set.disjoint_left.mp (hd j.property.symm) hi hj
    have hsub : interior (⋃ j, C j) ∩ Bᶜ ⊆ C i := by
      rintro q ⟨hq, hqB⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hq)
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact (hqB (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
    exact mem_iUnion.mpr ⟨i, interior_maximal hsub (isOpen_interior.inter hB.isOpen_compl) ⟨hp, hpB⟩⟩
  · exact iUnion_subset fun i => interior_mono (subset_iUnion C i)

theorem closure_interior_closedJordanCore
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    closure (interior (closedJordanCore H)) = closedJordanCore H := by
  rw [interior_closedJordanCore, openCompletedRegion, closure_compl,
    interior_finite_disjoint_closed (fun i => closedTerminalCap (H i))
      (fun i => (isCompact_closedTerminalCap (H i)).isClosed) (disjoint_closedTerminalCaps H hd)]
  simp only [interior_closedTerminalCap, closedJordanCore]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Images of compact retained cores

A conformal injection on an open neighborhood carries a compact core's
interior and boundary to the interior and boundary of its image. Regular
closed cores remain regular closed. These facts use local openness, not a
boundary extension of the conformal map.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem frontier_image_of_continuous_open
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hG : IsOpen G) (hi : InjOn f G) (hK : IsCompact K) (hKG : K ⊆ G) :
    frontier (f '' K) = f '' frontier K := by
  have hfc : IsClosed (f '' K) := (hK.image_of_continuousOn (hc.mono hKG)).isClosed
  rw [frontier, hfc.closure_eq, interior_image_of_continuous_open hc ho hG hi hKG,
    frontier, hK.isClosed.closure_eq]
  exact ((hi.mono hKG).image_sdiff_subset interior_subset).symm

theorem closure_image_interior_of_continuous
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hf : ContinuousOn f G) (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K) :
    closure (f '' interior K) = f '' K := by
  have hc : ContinuousOn f K := hf.mono hKG
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset) (hK.image_of_continuousOn hc).isClosed
  · have hci : ContinuousOn f (closure (interior K)) := hregular.symm ▸ hc
    simpa only [hregular] using hci.image_closure

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanCoreRecognition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recognizing the exterior bounded by a finite Jordan family

A regular closed sphere set with connected interior containing infinity
and with finitely many disjoint Jordan boundary curves is exactly their
common closed exterior. The filled disks are disjoint. This supplies the
image-side identification of retained cores without assuming orientation
or a boundary extension theorem.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem unbounded_preconnected_subset_jordan_exterior
    {T : Set ℂ} (hT : IsPreconnected T) (hunbounded : ¬ Bornology.IsBounded T)
    (H : ℂ ≃ₜ ℂ) (havoid : Disjoint T (frontier (jordanInterior H))) :
    T ⊆ (closure (jordanInterior H))ᶜ := by
  have hsplit : T ⊆ jordanInterior H ∨ T ⊆ (closure (jordanInterior H))ᶜ := by
    apply hT.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact Set.disjoint_left.mpr fun _ hx hy => hy (subset_closure hx)
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        exact Set.disjoint_left.mp havoid hz (by
          rw [(jordanInterior_isOpen H).frontier_eq]
          exact ⟨hc, hi⟩)
  rcases hsplit with h | h
  · exact (hunbounded ((isCompact_closure_jordanInterior H).isBounded.subset
      (h.trans subset_closure))).elim
  · exact h

theorem sphere_jordan_core_recognition
    {I : Type*} [Finite I] {A : Set Sphere}
    (hregular : closure (interior A) = A)
    (hconn : IsPreconnected (interior A)) (hinf : OnePoint.infty ∈ interior A)
    (H : I → ℂ ≃ₜ ℂ)
    (hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))))
    (hfront : frontier A = ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) :
    Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      Aᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hAclosed : IsClosed A := hregular ▸ isClosed_closure
  let T : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' interior A
  have hT := finite_part_connected_unbounded hconn (by
    simpa only [interior_interior] using hinf)
  have hfrontA (i : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) ⊆ frontier A := by
    rw [hfront]
    exact subset_iUnion (fun j : I => ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j))) i
  have hTout (i : I) : T ⊆ (closure (jordanInterior (H i)))ᶜ := by
    apply unbounded_preconnected_subset_jordan_exterior hT.1 hT.2 (H i)
    apply Set.disjoint_left.mpr
    intro z hz hzfront
    have hzf := hfrontA i (mem_image_of_mem _ hzfront)
    exact hzf.2 hz
  have hAout (i : I) : A ⊆ (((↑) : ℂ → Sphere) '' jordanInterior (H i))ᶜ := by
    rw [← hregular]
    apply closure_minimal ?_ (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H i))).isClosed_compl
    intro p hp hinside
    obtain ⟨z, hz, rfl⟩ := hinside
    exact hTout i hp (subset_closure hz)
  have hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) := by
    intro i j hij
    rcases disjoint_or_nested_jordanInteriors (H i) (H j) (hpair hij) with hd | hn | hn
    · exact hd
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA i (mem_image_of_mem _ hz))
      exact (hAout j hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H j)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA j (mem_image_of_mem _ hz))
      exact (hAout i hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
  let U : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Aᶜ
  have hUo : IsOpen U := hAclosed.isOpen_compl.preimage OnePoint.continuous_coe
  have hUb : Bornology.IsBounded U := by
    have hc := ((OnePoint.isOpen_iff_of_mem hinf).mp isOpen_interior).2
    apply hc.isBounded.subset
    intro z hz hzint
    exact hz (interior_subset hzint)
  have hprefront : frontier U = ((↑) : ℂ → Sphere) ⁻¹' frontier A := by
    change frontier (((↑) : ℂ → Sphere) ⁻¹' Aᶜ) = _
    rw [← OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
      OnePoint.continuous_coe, frontier_compl]
  have hcover : frontier U ⊆ ⋃ i, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hprefront] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront ▸ hz)
    have hzi : z ∈ frontier (jordanInterior (H i)) := OnePoint.coe_injective.mem_set_image.mp hi
    exact mem_iUnion.mpr ⟨i, frontier_subset_closure hzi⟩
  have hselected (i : I) : frontier (jordanInterior (H i)) ⊆ frontier U := by
    intro z hz
    rw [hprefront]
    exact hfrontA i (mem_image_of_mem _ hz)
  have hUfill := open_subset_finite_jordanInteriors_of_frontier_subset H hd hUo hUb hcover hselected
  refine ⟨hd, Subset.antisymm ?_ ?_⟩
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact (hp (interior_subset hinf)).elim
    | coe z =>
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hUfill hp)
      exact mem_iUnion.mpr ⟨i, z, hi, rfl⟩
  · intro p hp hpA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hAout i hpA hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual Jordan disks bounded by an image core

Schoenflies is applied only to the images of the given boundary circles.
The image-core theorem then proves that their filled sides are pairwise
disjoint and exhaust the complement of the image core.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_jordan_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hG : IsOpen G) (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K)
    (hconn : IsPreconnected (interior K)) (hinf : OnePoint.infty ∈ interior K)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {I : Type*} [Finite I] (γ : I → Circle → ℂ)
    (hγ : ∀ i, Continuous (γ i)) (hγinj : ∀ i, Injective (γ i))
    (hγpair : Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))))
    (hfront : frontier K = ⋃ i, ((↑) : ℂ → Sphere) '' range (γ i)) :
    ∃ H : I → ℂ ≃ₜ ℂ,
      (∀ i, frontier (jordanInterior (H i)) =
        range (fun t => finiteCoord (f ((γ i t : ℂ) : Sphere)))) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      (f '' K)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hγK (i : I) (t : Circle) : ((γ i t : ℂ) : Sphere) ∈ K := by
    apply hK.isClosed.closure_eq ▸ frontier_subset_closure
    rw [hfront]
    exact mem_iUnion.mpr ⟨i, γ i t, ⟨t, rfl⟩, rfl⟩
  have hinfG : OnePoint.infty ∈ G := hKG (interior_subset hinf)
  have hfinite (i : I) (t : Circle) : f ((γ i t : ℂ) : Sphere) ≠ OnePoint.infty :=
    finite_image_of_fixes_infty hi hinfG hfix (hKG (hγK i t))
  let δ : I → Circle → ℂ := fun i t => finiteCoord (f ((γ i t : ℂ) : Sphere))
  have hcoords (i : I) (t : Circle) : (δ i t : Sphere) = f ((γ i t : ℂ) : Sphere) :=
    CannonMobius.coe_coordinate (hfinite i t)
  have hδ (i : I) : Continuous (δ i) := by
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have he : ((↑) : ℂ → Sphere) ∘ δ i = f ∘ ((↑) : ℂ → Sphere) ∘ γ i :=
      funext (hcoords i)
    rw [he]
    exact hf.comp_continuous (OnePoint.continuous_coe.comp (hγ i))
      (fun t => hKG (hγK i t))
  have hδinj (i : I) : Injective (δ i) := by
    intro x y hxy
    apply hγinj i
    apply OnePoint.coe_injective
    apply hi (hKG (hγK i x)) (hKG (hγK i y))
    exact (hcoords i x).symm.trans ((congrArg ((↑) : ℂ → Sphere) hxy).trans (hcoords i y))
  choose H hH using fun i => hschoenflies (δ i) (hδ i) (hδinj i)
  have hHfront (i : I) : frontier (jordanInterior (H i)) = range (δ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (δ i) (hH i)
  have hHp : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    rw [hHfront i, hHfront j]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have he : ((γ i x : ℂ) : Sphere) = ((γ j y : ℂ) : Sphere) := by
      apply hi (hKG (hγK i x)) (hKG (hγK j y))
      exact (hcoords i x).symm.trans
        ((congrArg ((↑) : ℂ → Sphere) (hx.trans hy.symm)).trans (hcoords j y))
    exact Set.disjoint_left.mp (hγpair hij) ⟨x, rfl⟩ ⟨y, OnePoint.coe_injective he.symm⟩
  have himages (i : I) : f '' (((↑) : ℂ → Sphere) '' range (γ i)) =
      ((↑) : ℂ → Sphere) '' range (δ i) := by
    ext p
    constructor
    · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
      exact ⟨δ i t, ⟨t, rfl⟩, hcoords i t⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨((γ i t : ℂ) : Sphere), ⟨γ i t, ⟨t, rfl⟩, rfl⟩, (hcoords i t).symm⟩
  have htargetfront : frontier (f '' K) =
      ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := by
    rw [frontier_image_of_continuous_open hf ho hG hi hK hKG, hfront, image_iUnion]
    congr 1
    funext i
    rw [hHfront i]
    exact himages i
  have htargetint := interior_image_of_continuous_open hf ho hG hi hKG
  have htargetregular : closure (interior (f '' K)) = f '' K := by
    rw [htargetint]
    exact closure_image_interior_of_continuous hf hK hKG hregular
  have htargetconn : IsPreconnected (interior (f '' K)) := by
    rw [htargetint]
    exact hconn.image f (hf.mono (interior_subset.trans hKG))
  have htargetinf : OnePoint.infty ∈ interior (f '' K) := by
    rw [htargetint]
    exact ⟨OnePoint.infty, hinf, hfix⟩
  obtain ⟨hd, he⟩ := sphere_jordan_core_recognition htargetregular htargetconn htargetinf H hHp htargetfront
  exact ⟨H, hHfront, hd, he⟩

theorem exists_jordan_image_core
    (hschoenflies : PlanarSchoenflies)
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hG : IsOpen G) (hf : IsConformalOn f G) (hi : InjOn f G)
    (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K)
    (hconn : IsPreconnected (interior K)) (hinf : OnePoint.infty ∈ interior K)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {I : Type*} [Finite I] (γ : I → Circle → ℂ)
    (hγ : ∀ i, Continuous (γ i)) (hγinj : ∀ i, Injective (γ i))
    (hγpair : Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))))
    (hfront : frontier K = ⋃ i, ((↑) : ℂ → Sphere) '' range (γ i)) :
    ∃ H : I → ℂ ≃ₜ ℂ,
      (∀ i, frontier (jordanInterior (H i)) =
        range (fun t => finiteCoord (f ((γ i t : ℂ) : Sphere)))) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      (f '' K)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) :=
  exists_jordan_image_core_of_continuous_open hschoenflies hG
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi hK hKG hregular hconn hinf hfix
    γ hγ hγinj hγpair hfront

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ExteriorJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A holomorphic principal exterior injection maps each closed exterior
core to the closed exterior of its image Jordan curve. Schoenflies
identifies the filled Jordan disk. -/
open Set Filter Function Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exterior_closed_core_jordan (hsch : PlanarSchoenflies)
    {F : ℂ → ℂ} {R a : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hi : InjOn F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) (ha : R < a) :
    ∃ H : ℂ ≃ₜ ℂ,
      frontier (jordanInterior H) = range (fun z : Circle => F ((a : ℂ)*(z : ℂ))) ∧
      (F '' {z : ℂ | a ≤ ‖z‖})ᶜ = jordanInterior H := by
  have hap : 0 < a := hR.trans ha
  let D : Set ℂ := {z | R < ‖z‖}
  let G : Set Sphere := ((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}
  let T : Fin 1 → ℂ ≃ₜ ℂ := fun _ => roundDiskChart a hap
  let K := closedJordanCore T
  have hD : IsOpen D := isOpen_lt continuous_const continuous_norm
  have hG : IsOpen G := isOpen_finite_domain_with_infty hD
    (R := R+1) (by
      intro z hz
      change R+1 ≤ ‖z‖ at hz
      change R < ‖z‖
      linarith)
  have hconf : IsConformalOn (extendAtInfinity F) G :=
    isConformalOn_extendAtInfinity hD hF
      (fun z hz => holomorphicInjOn_deriv_ne_zero hD hF hi hz) hn
  have hpair : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hKe : K = (((↑) : ℂ → Sphere) '' ball (0 : ℂ) a)ᶜ := by
    simp only [K, closedJordanCore, T, roundDiskChart_interior, iUnion_const]
  have hK : IsCompact K := by
    rw [hKe]
    exact (OnePoint.isOpen_image_coe.mpr isOpen_ball).isClosed_compl.isCompact
  have hKG : K ⊆ G := by
    intro p hp
    rw [hKe] at hp
    cases p using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z =>
      apply Or.inl
      refine ⟨z, ?_, rfl⟩
      have hz : a ≤ ‖z‖ := by
        by_contra hh
        exact hp ⟨z, by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hh, rfl⟩
      exact ha.trans_le hz
  have hreg : closure (interior K) = K := closure_interior_closedJordanCore T hpair
  have hconn : IsPreconnected (interior K) := by
    rw [show K = closedJordanCore T from rfl, interior_closedJordanCore]
    exact (isConnected_openCompletedRegion T hpair).isPreconnected
  have hinf : OnePoint.infty ∈ interior K := by
    rw [show K = closedJordanCore T from rfl, interior_closedJordanCore]
    simp only [openCompletedRegion, T, closedTerminalCap, mem_compl_iff, mem_iUnion]
    rintro ⟨i, z, _, hz⟩
    exact OnePoint.coe_ne_infty z hz
  let γ : Fin 1 → Circle → ℂ := fun i z => T i (z : ℂ)
  have hγ (i : Fin 1) : Continuous (γ i) := (T i).continuous.comp continuous_subtype_val
  have hγi (i : Fin 1) : Injective (γ i) := (T i).injective.comp Subtype.val_injective
  have hγp : Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hfront : frontier K = ⋃ i, ((↑) : ℂ → Sphere) '' range (γ i) := by
    rw [show K = closedJordanCore T from rfl, frontier_closedJordanCore T hpair]
    congr 1
    funext i
    rw [frontier_jordanInterior_eq_circle_range (T i) (γ i) (by intro z; rfl)]
  obtain ⟨H, hH, _, hfill⟩ := exists_jordan_image_core hsch hG hconf
    (injOn_extendAtInfinity hi) hK hKG hreg hconn hinf rfl γ hγ hγi hγp hfront
  refine ⟨H 0, ?_, ?_⟩
  · have hh := hH 0
    simp only [extendAtInfinity_coe, finiteCoord_coe] at hh
    change frontier (jordanInterior (H 0)) = range (fun z : Circle => F ((a : ℂ)*(z : ℂ))) at hh
    exact hh
  · have he := congrArg (fun S : Set Sphere => ((↑) : ℂ → Sphere) ⁻¹' S) hfill
    have hpre : ((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity F '' K) =
        F '' {z : ℂ | a ≤ ‖z‖} := by
      ext z
      constructor
      · rintro ⟨p, hp, heq⟩
        cases p using OnePoint.rec with
        | infty => exact (OnePoint.coe_ne_infty z heq.symm).elim
        | coe w =>
          refine ⟨w, ?_, OnePoint.coe_injective heq⟩
          rw [hKe] at hp
          by_contra hh
          exact hp ⟨w, by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hh, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        refine ⟨(w : Sphere), ?_, rfl⟩
        rw [hKe]
        rintro ⟨v, hv, heq⟩
        have hvw := OnePoint.coe_injective heq
        subst v
        exact (not_lt_of_ge hw) (by simpa only [mem_ball, dist_zero_right] using hv)
    have hh : (F '' {z : ℂ | a ≤ ‖z‖})ᶜ = ⋃ i, jordanInterior (H i) := by
      simpa only [preimage_compl, hpre, preimage_iUnion,
        OnePoint.coe_injective.preimage_image] using he
    apply hh.trans
    ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      simpa only [Subsingleton.elim i (0 : Fin 1)] using hi
    · intro hz
      exact ⟨0, hz⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ExteriorImageCircuit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The image of an exterior source circle is the actual smooth regular
parametrization of its target Jordan boundary. -/
open Set Filter Function Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_image_circle_regular {F : ℂ → ℂ} {R a : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hi : InjOn F {z | R < ‖z‖})
    (ha : R < a) (H : ℂ ≃ₜ ℂ)
    (hH : frontier (jordanInterior H) = range (fun z : Circle => F ((a : ℂ)*(z : ℂ)))) :
    RegularJordanParametrization H (fun t => F (unitCircleParam 0 a t)) := by
  have hap : 0 < a := hR.trans ha
  have hO : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hs := unitCircleParam_regular a hap
  have hin (t : ℝ) : unitCircleParam 0 a t ∈ {z : ℂ | R < ‖z‖} := by
    simpa only [mem_ofPred_eq, unitCircleParam, norm_circleMap_zero, abs_of_pos hap] using ha
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => F (unitCircleParam 0 a t)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((hF.analyticAt (hO.mem_nhds (hin t))).contDiffAt.restrict_scalars ℝ).comp t
      hs.smooth.contDiffAt
  refine ⟨hγ, fun t => congrArg F (hs.periodic t), ?_, ?_, ?_⟩
  · intro s hs' t ht' he
    exact hs.injective hs' ht' (hi (hin s) (hin t) he)
  · intro t
    have hf := ((hF _ (hin t)).differentiableAt (hO.mem_nhds (hin t))).hasDerivAt
    have hd := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      ((hs.smooth.differentiable (by simp) t).hasDerivAt)
    have he : deriv (fun t => F (unitCircleParam 0 a t)) t =
        deriv F (unitCircleParam 0 a t) * deriv (unitCircleParam 0 a) t := by
      change deriv (F ∘ unitCircleParam 0 a) t = _
      rw [hd.deriv]
      change deriv (unitCircleParam 0 a) t * deriv F (unitCircleParam 0 a t) = _
      exact mul_comm _ _
    rw [he]
    exact mul_ne_zero (holomorphicInjOn_deriv_ne_zero hO hF hi (hin t)) (hs.regular t)
  · have hc : range (fun z : Circle => (a : ℂ)*(z : ℂ)) =
        frontier (jordanInterior (roundDiskChart a hap)) := by
      symm
      exact frontier_jordanInterior_eq_circle_range (roundDiskChart a hap)
        (fun z : Circle => (a : ℂ)*(z : ℂ)) (by intro z; rfl)
    calc
      (fun t => F (unitCircleParam 0 a t)) '' Icc 0 1 =
          F '' (unitCircleParam 0 a '' Icc 0 1) := (image_image _ _ _).symm
      _ = F '' frontier (jordanInterior (roundDiskChart a hap)) := by rw [hs.boundary]
      _ = F '' range (fun z : Circle => (a : ℂ)*(z : ℂ)) := by rw [hc]
      _ = range (fun z : Circle => F ((a : ℂ)*(z : ℂ))) := (range_comp' _ _).symm
      _ = frontier (jordanInterior H) := hH.symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_JordanSignedArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolute signed area of a regular Jordan curve is the actual
area of its bounded component. This is a direct specialization of the
remaining signed Green input, with no analytic area theorem assumed. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_signed_area (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ) :
    |signedCurveArea γ| = (volume (jordanInterior H)).toReal := by
  obtain ⟨e, he, hg⟩ := hgreen H γ hγ
  have hh := hg 0 Fin.elim0 Fin.elim0 (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    univ isOpen_univ (subset_univ _) (fun _ => 0) (fun z => z.re)
    contDiff_const.contDiffOn Complex.reCLM.contDiff.contDiffOn
  have hder (z : ℂ) : fderiv ℝ (fun w : ℂ => w.re) z 1 -
      fderiv ℝ (fun _ : ℂ => (0 : ℝ)) z Complex.I = 1 := by
    change (fderiv ℝ Complex.reCLM z) 1 - _ = 1
    rw [Complex.reCLM.fderiv]
    simp only [fderiv_const_apply, Complex.reCLM_apply, Complex.one_re, zero_apply, sub_zero]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, iUnion_of_empty,
    sdiff_empty, hder, integral_const, Measure.real, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one] at hh
  have hform : planarFormIntegral (fun _ => 0) (fun z => z.re) γ = signedCurveArea γ := by
    simp only [planarFormIntegral, signedCurveArea, zero_mul, zero_add]
  rw [hform] at hh
  have habs := congrArg abs hh
  simpa only [abs_mul, he, one_mul, abs_of_nonneg ENNReal.toReal_nonneg] using habs

lemma regular_jordan_signed_area_ne_zero (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ) :
    signedCurveArea γ ≠ 0 := by
  have hpos : 0 < volume (jordanInterior H) :=
    (jordanInterior_isOpen H).measure_pos volume (isConnected_jordanInterior H).nonempty
  have hfin : volume (jordanInterior H) ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt
      (isCompact_closure_jordanInterior H).measure_lt_top).ne
  have hr : 0 < (volume (jordanInterior H)).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have he := regular_jordan_signed_area hgreen H γ hγ
  intro hz
  rw [hz, abs_zero] at he
  exact hr.ne' he.symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorCircleAreaContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed image-circle area varies continuously with the source
radius. Only holomorphy on the exterior open set is required. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_image_circle_deriv {F : ℂ → ℂ} {R a : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (ha : R < a) (t : ℝ) :
    deriv (fun t => F (unitCircleParam 0 a t)) t =
      deriv F (unitCircleParam 0 a t) *
        (unitCircleParam 0 a t * Complex.I * (2*Real.pi)) := by
  have hap : 0 < a := hR.trans ha
  have hz : unitCircleParam 0 a t ∈ {z : ℂ | R < ‖z‖} := by
    simpa only [mem_ofPred_eq, unitCircleParam, norm_circleMap_zero, abs_of_pos hap] using ha
  have hf := ((hF _ hz).differentiableAt
    ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)).hasDerivAt
  have hd := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (unitCircleParam_hasDerivAt a t)
  change deriv (F ∘ unitCircleParam 0 a) t = _
  rw [hd.deriv]
  change (unitCircleParam 0 a t * Complex.I * (2*Real.pi)) *
      deriv F (unitCircleParam 0 a t) = _
  exact mul_comm _ _

lemma exterior_circle_area_continuousOn {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) :
    ContinuousOn (fun a => signedCurveArea (fun t => F (unitCircleParam 0 a t))) (Ioi R) := by
  let : LocallyCompactSpace (Ioi R) := isOpen_Ioi.locallyCompactSpace
  let p : (Ioi R) × ℝ → ℂ := fun x => unitCircleParam 0 x.1.val x.2
  have hp : Continuous p := by
    dsimp only [p, unitCircleParam]
    exact (Real.circleMap.continuous (c := 0)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hloc (x : (Ioi R) × ℝ) : p x ∈ {z : ℂ | R < ‖z‖} := by
    simpa only [p, unitCircleParam, mem_ofPred_eq, norm_circleMap_zero,
      abs_of_pos (hR.trans x.1.property), mem_Ioi] using x.1.property
  have hf : Continuous (fun x => F (p x)) := hF.continuousOn.comp_continuous hp hloc
  have hd : Continuous (fun x => deriv F (p x)) :=
    (hF.deriv (isOpen_lt continuous_const continuous_norm)).continuousOn.comp_continuous hp hloc
  let v : (Ioi R) → ℝ → ℝ := fun a t => (F (p (a,t))).re *
    (deriv F (p (a,t)) * (p (a,t) * Complex.I * (2*Real.pi))).im
  have hv : Continuous v.uncurry := by
    exact (Complex.continuous_re.comp hf).mul
      (Complex.continuous_im.comp (hd.mul ((hp.mul_const Complex.I).mul_const (2*Real.pi))))
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hv (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  change signedCurveArea (fun t => F (unitCircleParam 0 a.val t)) = _
  rw [signedCurveArea, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  change (F (unitCircleParam 0 a.val t)).re *
    (deriv (fun s => F (unitCircleParam 0 a.val s)) t).im = _
  rw [exterior_image_circle_deriv hR hF a.property]

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorCircleAreaPositive
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Principal normalization fixes the positive orientation of every
exterior image circle: signed area is continuous, never zero, and
positive on sufficiently large circles. -/
open Set Filter Function MeasureTheory Metric Bornology Asymptotics
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_circle_area_eventually_pos {F : ℂ → ℂ} {R : ℝ}
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ᶠ a : ℝ in atTop, 0 < signedCurveArea (fun t => F (unitCircleParam 0 a t)) := by
  have hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
    exact (hF z hz).differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
  obtain ⟨c, T, hT, he⟩ := principal_exterior_expansion hd (principal_remainder_tendsto_zero hn)
  have hl := principal_circle_area_limit hT he
  have hsmall := hl.eventually (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with a ha ha1
  have hs : (1 : ℝ) ≤ a^2 := one_le_pow₀ ha1
  have hp := Real.pi_gt_three
  nlinarith

lemma exterior_circle_area_pos (hsch : PlanarSchoenflies)
    (hgreen : UnorientedFiniteCircleGreenFormula) {F : ℂ → ℂ} {R a : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hi : InjOn F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) (ha : R < a) :
    0 < signedCurveArea (fun t => F (unitCircleParam 0 a t)) := by
  let A : ℝ → ℝ := fun r => signedCurveArea (fun t => F (unitCircleParam 0 r t))
  have hnz {r : ℝ} (hr : R < r) : A r ≠ 0 := by
    obtain ⟨H, hH, _⟩ := exterior_closed_core_jordan hsch hR hF hi hn hr
    exact regular_jordan_signed_area_ne_zero hgreen H _
      (exterior_image_circle_regular hR hF hi hr H hH)
  have hcont : ContinuousOn A (Ioi R) := exterior_circle_area_continuousOn hR hF
  obtain ⟨b, hb, hab⟩ := Filter.Eventually.exists
    ((exterior_circle_area_eventually_pos hF hn).and (eventually_ge_atTop a))
  change 0 < A b at hb
  change 0 < A a
  by_contra h
  have ha0 : A a ≤ 0 := le_of_not_gt h
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hab
    (hcont.mono (fun r hr => ha.trans_le hr.1)) (show (0 : ℝ) ∈ Icc (A a) (A b) from ⟨ha0, hb.le⟩)
  exact hnz (ha.trans_le hr.1) he

lemma exterior_jordan_area (hsch : PlanarSchoenflies)
    (hgreen : UnorientedFiniteCircleGreenFormula) {F : ℂ → ℂ} {R a : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hi : InjOn F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) (ha : R < a)
    (H : ℂ ≃ₜ ℂ)
    (hH : frontier (jordanInterior H) = range (fun z : Circle => F ((a : ℂ)*(z : ℂ)))) :
    (volume (jordanInterior H)).toReal = signedCurveArea (fun t => F (unitCircleParam 0 a t)) := by
  rw [← regular_jordan_signed_area hgreen H _ (exterior_image_circle_regular hR hF hi ha H hH),
    abs_of_pos (exterior_circle_area_pos hsch hgreen hR hF hi hn ha)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExteriorAreaBoundProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of the omitted-area form of the exterior area theorem.
The proof uses Green and Schoenflies, exact
annular energy, and the principal signed-area limit. -/
open Set Filter Function MeasureTheory Metric Bornology Asymptotics
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exterior_circle_area_le (hgreen : UnorientedFiniteCircleGreenFormula)
    {F : ℂ → ℂ} {R a : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) (ha : R < a) :
    signedCurveArea (fun t => F (unitCircleParam 0 a t)) ≤ Real.pi*a^2 := by
  have hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
    exact (hF z hz).differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
  obtain ⟨c, T, hT, he⟩ := principal_exterior_expansion hd (principal_remainder_tendsto_zero hn)
  have hlim := principal_circle_area_limit hT he
  have hle : ∀ᶠ b : ℝ in atTop,
      signedCurveArea (fun t => F (unitCircleParam 0 a t)) - Real.pi*a^2 ≤
        signedCurveArea (fun t => F (unitCircleParam 0 b t)) - Real.pi*b^2 := by
    filter_upwards [eventually_gt_atTop a] with b hab
    have henergy := exterior_annulus_energy hR hF (principal_remainder_tendsto_zero hn) ha hab.le
    have hint := exterior_annulus_energy_integrable hF ha (b := b)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall (fun z => sq_nonneg ‖deriv F z‖))] at henergy
    have hr := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun z => sq_nonneg ‖deriv F z‖))).mp henergy
    rw [← exterior_annulus_area hgreen hR hF ha hab] at hr
    nlinarith
  have hzero := ge_of_tendsto hlim hle
  linarith

lemma exteriorOmittedAreaTheorem_oai (hsch : PlanarSchoenflies)
    (hgreen : UnorientedFiniteCircleGreenFormula) : ExteriorOmittedAreaTheorem := by
  intro F R hR hF hi hn
  have hext : (closedBall (0 : ℂ) R)ᶜ = {z : ℂ | R < ‖z‖} := by
    ext z
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, mem_ofPred_eq]
  rw [hext] at hF hi
  unfold ExteriorOmittedAreaBound
  have hbound (a : ℝ) (ha : R < a) :
      volume ((F '' (closedBall (0 : ℂ) R)ᶜ)ᶜ) ≤ ENNReal.ofReal (Real.pi*a^2) := by
    obtain ⟨H, hH, hfill⟩ := exterior_closed_core_jordan hsch hR hF hi hn ha
    have hsub : ((F '' (closedBall (0 : ℂ) R)ᶜ)ᶜ) ⊆ jordanInterior H := by
      rw [← hfill]
      apply compl_subset_compl.mpr
      apply image_mono
      intro z hz
      rw [hext]
      exact ha.trans_le hz
    have hfin : volume (jordanInterior H) ≠ ∞ :=
      ((measure_mono subset_closure).trans_lt (isCompact_closure_jordanInterior H).measure_lt_top).ne
    calc
      _ ≤ volume (jordanInterior H) := measure_mono hsub
      _ = ENNReal.ofReal (signedCurveArea (fun t => F (unitCircleParam 0 a t))) := by
        rw [← exterior_jordan_area hsch hgreen hR hF hi hn ha H hH,
          ENNReal.ofReal_toReal hfin]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (exterior_circle_area_le hgreen hR hF hn ha)
  have ht : Tendsto (fun a : ℝ => ENNReal.ofReal (Real.pi*a^2)) (𝓝[>] R)
      (𝓝 (ENNReal.ofReal (Real.pi*R^2))) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow 2))).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact hbound a ha

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.exteriorOmittedAreaTheorem_oai := @OAI.CircleDomainRigidity.exteriorOmittedAreaTheorem_oai
