-- Prove2me | solution 1 for OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:01:58.444223+00:00
-- url     : https://prove2.me/submissions/401b29be-32e6-4fc5-a882-bc14a3bc5ce7

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010
import Theorems.Thm_OAI_CircleDomainRigidity_MatchedConformalEnds_MatchedRealMask_global_sobolev_of_published_inputs
import Theorems.Thm_OAI_CircleDomainRigidity_MatchedConformalEnds_normalized_identity_of_trace

section
-- module Solutions.Q146_CD.CircleDomains_LengthArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle domains, conformal removability, and conditional analytic rigidity from length and area estimates. -/

noncomputable section
open Set Classical
open scoped OnePoint

namespace CircleDomainRigidity

theorem IsConformallyRemovable.of_isCompact_subset {E K : Set Sphere}
    (hE : IsConformallyRemovable E) (hK : IsCompact K) (hKE : K ⊆ E) :
    IsConformallyRemovable K := by
  refine ⟨hK, fun h hor hconf ↦ ?_⟩
  exact hE.2 h hor (hconf.mono (compl_subset_compl.mpr hKE))

end CircleDomainRigidity

open MeasureTheory Filter Bornology
open scoped Topology
namespace CircleDomainRigidity.LengthArea

theorem summable_mul_of_squares {ι : Type*} {r s : ι → ℝ}
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2)) :
    Summable (fun j ↦ r j * s j) := by
  apply (hr.add hs).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|r j| - |s j|), sq_abs (r j), sq_abs (s j),
    sq_nonneg (r j), sq_nonneg (s j)]

end CircleDomainRigidity.LengthArea

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SourceArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The source-area inequality for circle domains

The source region and the interiors of its complementary disks are
disjoint subsets of one outer disk. Countable additivity gives the
source-area inequality used in Section 6 of the rigidity manuscript.
No regularity of the remaining point components is needed.
-/

open MeasureTheory Metric Set Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- Countable additivity for a disjoint measurable family, together with
one further disjoint source set, gives an area bound in a containing set. -/
theorem measure_source_add_disks_le {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) {U O : Set X} (D : ι → Set X)
    (hD : ∀ j, MeasurableSet (D j))
    (hpair : Pairwise (Disjoint on D))
    (hdisj : ∀ j, Disjoint U (D j))
    (hUO : U ⊆ O) (hDO : ∀ j, D j ⊆ O) :
    μ U + ∑' j, μ (D j) ≤ μ O := by
  have hd : Disjoint U (⋃ j, D j) := disjoint_iUnion_right.mpr hdisj
  calc
    μ U + ∑' j, μ (D j) = μ (U ∪ ⋃ j, D j) := by
      rw [measure_union hd (MeasurableSet.iUnion hD), measure_iUnion hpair hD]
    _ ≤ μ O := measure_mono (union_subset hUO (iUnion_subset hDO))

/-- The actual geometric source-area bound for pairwise disjoint disks. -/
theorem sourceArea_le {ι : Type*} [Countable ι] {U : Set ℂ}
    (centers : ι → ℂ) (radii : ι → ℝ) (R : ℝ)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (radii j)))
    (hdisj : ∀ j, Disjoint U (ball (centers j) (radii j)))
    (hUO : U ⊆ ball 0 R)
    (hDO : ∀ j, ball (centers j) (radii j) ⊆ ball 0 R) :
    volume U + ∑' j, volume (ball (centers j) (radii j)) ≤ volume (ball (0 : ℂ) R) :=
  measure_source_add_disks_le volume (fun j => ball (centers j) (radii j))
    (fun _ => measurableSet_ball) hpair hdisj hUO hDO

/-- Finitely bounded, pairwise disjoint disks have square-summable radii. -/
theorem summable_radii_sq {ι : Type*} [Countable ι]
    (centers : ι → ℂ) (radii : ι → ℝ) (R : ℝ)
    (hr : ∀ j, 0 ≤ radii j)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (radii j)))
    (hDO : ∀ j, ball (centers j) (radii j) ⊆ ball 0 R) :
    Summable (fun j => radii j ^ 2) := by
  have hbound := sourceArea_le (U := ∅) centers radii R hpair
    (fun _ => by simp) (empty_subset _) hDO
  simp only [measure_empty, zero_add] at hbound
  have hfinite : (∑' j, volume (ball (centers j) (radii j))) ≠ ∞ :=
    ne_of_lt (hbound.trans_lt (measure_ball_lt_top))
  have hs := ENNReal.summable_toReal hfinite
  have hs' : Summable (fun j => Real.pi * radii j ^ 2) :=
    hs.congr (fun j => real_volume_ball (centers j) (hr j))
  exact (summable_mul_left_iff Real.pi_ne_zero).mp hs'

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BallMaximalPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A maximal-function majorant pays the mass on a balloon by its mass
on any measurable subset occupying a fixed fraction of the balloon. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem ball_subset_double_ball {c x : ℂ} {d : ℝ} (hx : x ∈ ball c d) :
    ball c d ⊆ ball x (2*d) := by
  intro y hy
  rw [mem_ball] at hx hy ⊢
  calc
    dist y x ≤ dist y c+dist c x := dist_triangle _ _ _
    _ < d+d := add_lt_add hy (by simpa only [dist_comm] using hx)
    _ = 2*d := by ring

 theorem maximal_ball_payment {g m : ℂ → ℝ}
    (hg : MemLp g 2 volume) (hm : MemLp m 2 volume) (_hm0 : ∀ z, 0 ≤ m z)
    (hmax : ∀ r : ℝ, 0 < r → ∀ᵐ x ∂volume,
      (∫ y in ball x r, ‖g y‖) ≤ volume.real (ball x r)*m x)
    {c : ℂ} {d k : ℝ} (hd : 0 < d) (_hk : 0 < k) {E : Set ℂ}
    (hE : MeasurableSet E) (hEB : E ⊆ ball c d)
    (hsize : k*d^2 ≤ volume.real E) :
    k*(∫ y in ball c d, ‖g y‖) ≤ 4*Real.pi*(∫ x in E, m x) := by
  have hEf : volume E ≠ ∞ := measure_ne_top_of_subset hEB measure_ball_lt_top.ne
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hEf
  have hmE : IntegrableOn m E := (hm.restrict E).integrable (by norm_num)
  have hpoint : ∀ᵐ x ∂volume.restrict E,
      (∫ y in ball c d, ‖g y‖) ≤ (4*Real.pi*d^2)*m x := by
    filter_upwards [ae_restrict_mem hE,ae_restrict_of_ae (hmax (2*d) (by positivity))] with x hx hxmax
    have hbig : IntegrableOn (fun y => ‖g y‖) (ball x (2*d)) :=
      ((hg.norm.locallyIntegrable (by norm_num)).integrableOn_isCompact
        (isCompact_closedBall x (2*d))).mono_set ball_subset_closedBall
    calc
      _ ≤ ∫ y in ball x (2*d), ‖g y‖ :=
        setIntegral_mono_set hbig (Eventually.of_forall (fun _ => norm_nonneg _))
          (Filter.Eventually.of_forall (ball_subset_double_ball (hEB hx)))
      _ ≤ volume.real (ball x (2*d))*m x := hxmax
      _ = _ := by rw [show volume.real (ball x (2*d)) = Real.pi*(2*d)^2 from
          real_volume_ball x (by positivity)]; ring
  have hi := integral_mono_ae (integrable_const (∫ y in ball c d, ‖g y‖))
    (hmE.const_mul (4*Real.pi*d^2)) hpoint
  rw [integral_const,integral_const_mul,smul_eq_mul,Measure.real,Measure.restrict_apply_univ] at hi
  have hI : 0 ≤ ∫ y in ball c d, ‖g y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hl := (mul_le_mul_of_nonneg_right hsize hI).trans hi
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hd)).mp
  nlinarith only [hl]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DisjointBallPayments
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cauchy--Schwarz for finitely many disjoint payment regions inside
balloons. Only their containing ball areas enter the estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integral_sq_le_measure_mul_energy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {m : X → ℝ}
    (hm : MemLp m 2 μ) (hm0 : ∀ x, 0 ≤ m x) :
    (∫ x, m x ∂μ)^2 ≤ μ.real univ*(∫ x, m x^2 ∂μ) := by
  have hb := integral_le_sqrt_measure_mul_L2 hm (Eventually.of_forall hm0)
  have hh := mul_self_le_mul_self (integral_nonneg hm0) hb
  simpa only [← pow_two,mul_pow,Real.sq_sqrt measureReal_nonneg,
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (m x)))] using hh

 theorem sum_disjoint_ball_payments_sq_le {ι : Type*} [DecidableEq ι]
    (F : Finset ι) {E : ι → Set ℂ} {c : ι → ℂ} {d a : ι → ℝ}
    (hd : ∀ j ∈ F, 0 < d j) (hE : ∀ j ∈ F, MeasurableSet (E j))
    (hdisj : Set.Pairwise (↑F) (Disjoint on E))
    (hsub : ∀ j ∈ F, E j ⊆ ball (c j) (d j))
    {m : ℂ → ℝ} (hm : MemLp m 2 volume) (hm0 : ∀ z, 0 ≤ m z) :
    (∑ j ∈ F, a j/d j*(∫ x in E j, m x))^2 ≤
      Real.pi*(∑ j ∈ F, a j^2)*(∫ x, m x^2) := by
  have hpiece (j : ι) (hj : j ∈ F) :
      (a j/d j*(∫ x in E j, m x))^2 ≤ (Real.pi*a j^2)*(∫ x in E j, m x^2) := by
    have hEf : volume (E j) ≠ ∞ := measure_ne_top_of_subset (hsub j hj) measure_ball_lt_top.ne
    let : IsFiniteMeasure (volume.restrict (E j)) := isFiniteMeasure_restrict.mpr hEf
    have hh := integral_sq_le_measure_mul_energy (hm.restrict (E j)) hm0
    rw [Measure.real,Measure.restrict_apply_univ] at hh
    have harea : volume.real (E j) ≤ Real.pi*d j^2 := by
      exact (measureReal_mono (hsub j hj) measure_ball_lt_top.ne).trans_eq (real_volume_ball _ (hd j hj).le)
    have hh' : (∫ x in E j, m x)^2 ≤ Real.pi*d j^2*(∫ x in E j, m x^2) :=
      hh.trans (mul_le_mul_of_nonneg_right harea (integral_nonneg (fun _ => sq_nonneg _)))
    calc
      _ = (a j)^2/(d j)^2*(∫ x in E j, m x)^2 := by ring
      _ ≤ (a j)^2/(d j)^2*(Real.pi*d j^2*(∫ x in E j, m x^2)) :=
        mul_le_mul_of_nonneg_left hh' (by positivity)
      _ = _ := by field_simp [ne_of_gt (hd j hj)]
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul F
    (fun j _ => mul_nonneg Real.pi_pos.le (sq_nonneg (a j)))
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) hpiece
  have hunion : (∑ j ∈ F, ∫ x in E j, m x^2) ≤ ∫ x, m x^2 := by
    rw [← integral_biUnion_finset F hE hdisj (fun _ _ => hm.integrable_sq.restrict)]
    exact setIntegral_le_integral hm.integrable_sq (Eventually.of_forall (fun x => sq_nonneg (m x)))
  have hsum : (∑ j ∈ F, Real.pi*a j^2) = Real.pi*(∑ j ∈ F, a j^2) :=
    (Finset.mul_sum F (fun j => a j^2) Real.pi).symm
  rw [hsum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hunion (mul_nonneg Real.pi_pos.le
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MobiusNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete Möbius normalizations

Affine changes and inversion are homeomorphisms of the concrete sphere.
Their matrix actions agree with the projective-line action used in the
definition of round disks.
-/

open Set Filter Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem inversion_eq_smul (p : Sphere) : CannonMobius.inversion p = inversionMobius • p := by
  change CannonMobius.inv p = inversionMobius • p
  cases p using OnePoint.rec with
  | infty => simp [OnePoint.smul_infty_eq_ite, inversionMobius]
  | coe z =>
    by_cases hz : z = 0
    · simp [hz, OnePoint.smul_some_eq_ite, inversionMobius]
    · simp [hz, OnePoint.smul_some_eq_ite, inversionMobius,
        CannonMobius.inv, div_eq_mul_inv]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentControl
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recognition of the limiting circle domain

Complementary-component coverage, collapse of unmarked components, and filling
of marked components together identify the limiting image as a circle domain.
-/

namespace CircleDomainRigidity

/-- Complementary components are nonempty. -/
theorem IsComplementaryComponent.nonempty {G K : Set Sphere}
    (h : IsComplementaryComponent G K) : K.Nonempty := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, mem_connectedComponentIn hp⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleMobiusImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Circle domains under the normalizing Möbius maps

Round complementary disks transform by multiplication of their defining
matrices. A homeomorphic Möbius map therefore preserves circle domains.
The explicit normalizer sends any prescribed sphere point to infinity.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem isCircleDomain_image_mobius
    {U : Set Sphere} (hU : IsCircleDomain U) (M : Mobius) (e : Sphere ≃ₜ Sphere)
    (he : ∀ p, e p = M • p) : IsCircleDomain (e '' U) := by
  refine ⟨e.isOpenMap _ hU.1, hU.2.1.image e e.continuous.continuousOn, ?_⟩
  intro p hp
  have hpre : e.symm p ∈ Uᶜ := by
    intro hx
    exact hp ⟨e.symm p, hx, e.apply_symm_apply p⟩
  have hcomponent : e '' connectedComponentIn Uᶜ (e.symm p) =
      connectedComponentIn (e '' U)ᶜ p := by
    rw [e.image_connectedComponentIn hpre, e.image_compl, e.apply_symm_apply]
  rcases hU.2.2 (e.symm p) hpre with ⟨q, hq⟩ | hround
  · left
    refine ⟨e q, ?_⟩
    rw [← hcomponent, hq, image_singleton]
  · right
    rw [← hcomponent]
    have hefun : (e : Sphere → Sphere) = fun x => M • x := funext he
    simpa only [hefun] using isRoundClosedDisk_image_mobius hround M

theorem pointToInfinity_eq_smul (p q : Sphere) :
    pointToInfinity p q = pointToInfinityMobius p • q := by
  cases p using OnePoint.rec with
  | infty => simp [pointToInfinity, pointToInfinityMobius]
  | coe z =>
    change CannonMobius.inversion (affineSphere 1 (-z) one_ne_zero q) = _
    rw [inversion_eq_smul, affineSphere_eq_smul, ← mul_smul]
    rfl

theorem pointToInfinity_preserves_circleDomain (p : Sphere)
    {U : Set Sphere} (hU : IsCircleDomain U) :
    IsCircleDomain (pointToInfinity p '' U) :=
  isCircleDomain_image_mobius hU (pointToInfinityMobius p) (pointToInfinity p)
    (pointToInfinity_eq_smul p)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite smooth Jordan neighborhoods

The contour construction in Section 1 of the Koebe manuscript is derived
from the smooth cutoff and regular level, scalar Sard, compact
one-manifold classification, and planar Schoenflies. Outer selection and containment
give the finite family of Jordan neighborhoods.
-/

open Set Filter Function
open scoped Topology ContDiff Manifold

namespace CircleDomainRigidity

/-- Actual finite smooth Jordan disks covering a chosen compact part of an
obstacle, with disjoint closures contained in the prescribed physical open
set. Its complement is required connected and unbounded precisely for the
hole-filling containment argument. -/
theorem exists_finite_smooth_jordan_cover
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ A ⊆ ⋃ i ∈ s, jordanInterior (H i) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F := by
  classical
  obtain ⟨f, t, hf, ht, hU, hAU, hUc, hUV, _, hlevel, hregular, havoid, _⟩ :=
    exists_regular_superlevel_isolating_obstacle hsard hA hAF hFA hV hAV
  obtain ⟨hfinite, γ, hγ, hγdisj, hγcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  let : Finite (ConnectedComponents {z // f z = t}) := hfinite
  choose H hH using fun i => hschoenflies (γ i) (hγ i).2.continuous (hγ i).2.injective
  have hfront (i) : frontier (jordanInterior (H i)) = range (γ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hUd : frontier {z | t < f z} = {z | f z = t} :=
    frontier_superlevel_eq_regular_level hf.continuous hregular
  have hfrontlevel (i) : frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
    rw [hfront, ← hγcover]
    exact subset_iUnion (fun i => range (γ i)) i
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hγdisj hij
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hpair
  let : Finite s := hs.to_subtype
  have hsd' : Pairwise (Disjoint on fun i : s => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hsd i.property j.property (fun h => hij (Subtype.ext h))
  have hcover : frontier {z | t < f z} ⊆ ⋃ i : s, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hUd, ← hγcover] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : z ∈ closure (jordanInterior (H i)) := by
      apply frontier_subset_closure
      simpa only [hfront] using hi
    obtain ⟨j, hj, hij⟩ := hdom i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi'⟩
  have hUcover : {z | t < f z} ⊆ ⋃ i : s, jordanInterior (H i) :=
    open_subset_finite_jordanInteriors_of_frontier_subset (fun i : s => H i) hsd'
      hU (hUc.isBounded.subset subset_closure) hcover
      (fun i => hUd.symm ▸ hfrontlevel i)
  refine ⟨f, t, γ, H, s, hs, ?_, hsd, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcover (hAU hz))
    exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
  · intro i _
    apply closed_jordanInterior_subset_of_unbounded_connected_compl (H i) hVconn hVunbounded
    intro z hz
    apply hUV
    apply frontier_subset_closure
    rw [hUd]
    exact hfrontlevel i hz
  · intro i _
    exact ⟨(hγ i).1, (hγ i).2, hfront i, havoid.mono_left (hfrontlevel i)⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Topological parts of the component argument

The quotient theorem below proves the totally disconnected dust conclusion
from the component-collapse properties of the quotient.  Moore's 1925
sphere-decomposition theorem supplies the sphere realization; that published
input is not assumed to provide the dust conclusion for free.
-/

open Set Topology

namespace CircleDomainRigidity

theorem IsComplementaryComponent.disjoint_of_ne {G K L : Set Sphere}
    (hK : IsComplementaryComponent G K) (hL : IsComplementaryComponent G L)
    (hne : K ≠ L) : Disjoint K L := by
  obtain ⟨p, _, rfl⟩ := hK
  obtain ⟨q, _, rfl⟩ := hL
  apply Set.disjoint_left.mpr
  intro x hpx hqx
  exact hne ((connectedComponentIn_eq hpx).trans (connectedComponentIn_eq hqx).symm)

/-- No countability is imposed on point components.  The components with
nonempty interior are countable by separability. -/
theorem countable_complementaryComponents_with_interior (G : Set Sphere) :
    {K : Set Sphere | IsComplementaryComponent G K ∧ (interior K).Nonempty}.Countable := by
  let : TopologicalSpace.SeparableSpace Sphere :=
    (OnePoint.isDenseEmbedding_coe (X := ℂ)).separableSpace
  let A := {K : Set Sphere | IsComplementaryComponent G K ∧ (interior K).Nonempty}
  have hdisj : A.PairwiseDisjoint id := by
    intro K hK L hL hne
    exact hK.1.disjoint_of_ne hL.1 hne
  exact hdisj.countable_of_nonempty_interior (fun _ hK => hK.2)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryBumping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Boundary bumping for compact continua

This is the compact-space argument used in the small-disk and generic-level
lemmas of the uniformization manuscript. It does not assume local
connectedness of the continuum.
-/

open Set Topology

namespace CircleDomainRigidity

/-- Every component of a proper closed subset of a compact connected space
meets its boundary. -/
theorem component_meets_frontier
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [PreconnectedSpace X] {F : Set X} (hF : IsClosed F) (hproper : F ≠ univ)
    {x : X} (hx : x ∈ F) :
    (connectedComponentIn F x ∩ frontier F).Nonempty := by
  classical
  by_contra hnonempty
  have hdisj : Disjoint (frontier F) (connectedComponentIn F x) :=
    (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hnonempty)).symm
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  let K : Set F := (Subtype.val : F → X) ⁻¹' frontier F
  have hK : IsClosed K := isClosed_frontier.preimage continuous_subtype_val
  have hd : Disjoint K (connectedComponent xf) := by
    apply Set.disjoint_left.mpr
    intro z hzK hzC
    apply Set.disjoint_left.mp hdisj hzK
    rw [connectedComponentIn_eq_image hx]
    exact ⟨z, hzC, rfl⟩
  rw [connectedComponent_eq_iInter_isClopen xf] at hd
  obtain ⟨s, hs⟩ := hK.isCompact.elim_finite_subfamily_closed
    (fun U : {U : Set F // IsClopen U ∧ xf ∈ U} => U.val)
    (fun U => U.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)
  let U : Set F := ⋂ V ∈ s, (V : Set F)
  have hU : IsClopen U := isClopen_biInter_finset fun V _ => V.property.1
  have hxU : xf ∈ U := mem_iInter₂.mpr fun V _ => V.property.2
  let W : Set X := (Subtype.val : F → X) '' U
  have hWclosed : IsClosed W := hF.isClosedMap_subtype_val U hU.isClosed
  have hWF : W ⊆ F := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hWint : W ⊆ interior F := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hzi
    have hzK : z ∈ K := ⟨subset_closure z.property, hzi⟩
    exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hzK hz
  obtain ⟨O, hO, hWO⟩ :=
    Topology.IsInducing.subtypeVal.image_eq_isOpen_inter_range hU.isOpen
  change W = O ∩ range (Subtype.val : F → X) at hWO
  have hWeq : W = O ∩ interior F := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨(hWO ▸ hz).1, hWint hz⟩
    · intro z hz
      rw [hWO]
      exact ⟨hz.1, ⟨⟨z, interior_subset hz.2⟩, rfl⟩⟩
  have hWopen : IsOpen W := hWeq ▸ hO.inter isOpen_interior
  have hWuniv : W = univ := (show IsClopen W from ⟨hWclosed, hWopen⟩).eq_univ
    ⟨x, xf, hxU, rfl⟩
  apply hproper
  apply Set.eq_univ_of_univ_subset
  rw [← hWuniv]
  exact hWF

end CircleDomainRigidity

end OAI
end

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

theorem isPrincipalNormalized_extendAtInfinity {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsPrincipalNormalized (extendAtInfinity F) :=
  ⟨rfl, by simpa only [extendAtInfinity_coe, finiteCoord_coe] using hF⟩

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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_FiniteTraceMask
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite lower-envelope masks for the common-point trace argument.
The variation is paid only on intervals in which the corresponding cutoff
is active. These estimates precede the Sobolev and infinite-mask limits. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem finiteTraceMask_bounds {X : Type*} {cutoff : ℕ → X → ℝ}
    (hcutoff : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (t : ℝ) (n : ℕ) :
    finiteTraceMask cutoff I x t n ∈ Icc (0:ℝ) 1 := by
  induction n with
  | zero => exact ⟨zero_le_one,le_rfl⟩
  | succ n ih =>
    simp only [finiteTraceMask,mem_Icc]
    constructor
    · apply le_min ih.1
      split_ifs
      · exact (hcutoff n x).1
      · exact zero_le_one
    · exact (min_le_left _ _).trans ih.2

 theorem finiteTraceMask_antitone {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x : X) (t : ℝ) : Antitone (finiteTraceMask cutoff I x t) := by
  apply antitone_nat_of_succ_le
  intro n
  exact min_le_left _ _

 theorem finiteTraceMask_eq_one {X : Type*} {cutoff : ℕ → X → ℝ} {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {n : ℕ} (h : ∀ j < n, t ∈ I j → cutoff j x = 1) :
    finiteTraceMask cutoff I x t n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finiteTraceMask,ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    by_cases ht : t ∈ I n
    · rw [ite_eq_left ht,h n (Nat.lt_succ_self n) ht,min_self]
    · rw [ite_eq_right ht,min_self]

 theorem finiteTraceMask_le_active {X : Type*} {cutoff : ℕ → X → ℝ} {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {j n : ℕ} (hj : j < n) (ht : t ∈ I j) :
    finiteTraceMask cutoff I x t n ≤ cutoff j x := by
  have he : finiteTraceMask cutoff I x t (j+1) ≤ cutoff j x := by
    simpa only [finiteTraceMask,ite_eq_left ht] using
      min_le_right (finiteTraceMask cutoff I x t j) (cutoff j x)
  exact ((finiteTraceMask_antitone cutoff I x t) hj).trans he

 theorem finiteTraceMask_zero_of_active {X : Type*} {cutoff : ℕ → X → ℝ}
    (hcutoff : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {j n : ℕ} (hj : j < n) (ht : t ∈ I j) (hz : cutoff j x = 0) :
    finiteTraceMask cutoff I x t n = 0 := by
  apply le_antisymm
  · simpa only [hz] using finiteTraceMask_le_active (cutoff := cutoff) (x := x) hj ht
  · exact (finiteTraceMask_bounds hcutoff I x t n).1

 theorem finiteTraceMask_variation {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x y : X) (t : ℝ) (n : ℕ) :
    |finiteTraceMask cutoff I x t n-finiteTraceMask cutoff I y t n| ≤
      ∑ j ∈ Finset.range n, (I j).indicator (fun _ => |cutoff j x-cutoff j y|) t := by
  induction n with
  | zero => simp [finiteTraceMask]
  | succ n ih =>
    have hs : 0 ≤ ∑ j ∈ Finset.range n, (I j).indicator (fun _ => |cutoff j x-cutoff j y|) t :=
      Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => abs_nonneg _) t)
    rw [finiteTraceMask,finiteTraceMask,Finset.sum_range_succ]
    have hh := abs_min_sub_min_le_max (finiteTraceMask cutoff I x t n)
      (if t ∈ I n then cutoff n x else 1) (finiteTraceMask cutoff I y t n)
      (if t ∈ I n then cutoff n y else 1)
    apply hh.trans
    apply max_le
    · apply ih.trans
      exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ => abs_nonneg _) _)
    · by_cases ht : t ∈ I n
      · simp only [ite_eq_left ht,indicator_of_mem ht]
        exact le_add_of_nonneg_left hs
      · simp only [ite_eq_right ht,sub_self,abs_zero,indicator_of_notMem ht,add_zero]
        exact hs

 theorem finiteTraceMask_measurable {X : Type*} (cutoff : ℕ → X → ℝ) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) :
    Measurable (fun t => finiteTraceMask cutoff I x t n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.min (Measurable.ite (hI n) measurable_const measurable_const)

 theorem finiteTraceMask_tendsto {X : Type*} {cutoff : ℕ → X → ℝ}
    (hcutoff : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (t : ℝ) :
    Tendsto (finiteTraceMask cutoff I x t) atTop (𝓝 (infiniteTraceMask cutoff I x t)) := by
  apply tendsto_atTop_ciInf (finiteTraceMask_antitone cutoff I x t)
  exact ⟨0,fun _ ⟨n,hn⟩ => hn ▸ (finiteTraceMask_bounds hcutoff I x t n).1⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_NullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null images from connected-neighborhood oscillation bounds

The measure part of the trace-null argument: split an open neighborhood
into its countably many connected components and pay for the diameter
of each real image by the measure of its component. No measurability of
the trace function or of its image is assumed.
-/

open Set MeasureTheory Metric Function
open scoped ENNReal

namespace CircleDomainRigidity

theorem null_image_of_connected_open_oscillation
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyConnectedSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [μ.OuterRegular] {F : Set X} (hF : μ F = 0) (v : X → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hosc : ∀ U : Set X, IsOpen U → IsConnected U →
      ∀ x ∈ F ∩ U, ∀ y ∈ F ∩ U, |v x - v y| ≤ A * μ.real U) :
    volume (v '' F) = 0 := by
  classical
  have hbound (O : Set X) (hFO : F ⊆ O) (hO : IsOpen O) :
      volume (v '' F) ≤ ENNReal.ofReal A * μ O := by
    let C : Set (Set X) := {U | ∃ x ∈ O, U = connectedComponentIn O x}
    have hC (U : Set X) (hU : U ∈ C) : IsOpen U ∧ IsConnected U ∧ U ⊆ O := by
      obtain ⟨x, hx, rfl⟩ := hU
      exact ⟨hO.connectedComponentIn, isConnected_connectedComponentIn_iff.mpr hx,
        connectedComponentIn_subset O x⟩
    have hd : C.PairwiseDisjoint id := by
      rintro U ⟨x, hx, rfl⟩ V ⟨y, hy, rfl⟩ hne
      apply Set.disjoint_left.mpr
      intro z hzx hzy
      exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)
    have hcount : C.Countable := hd.countable_of_nonempty_interior (fun U hU => by
      change (interior U).Nonempty
      rw [(hC U hU).1.interior_eq]
      exact (hC U hU).2.1.nonempty)
    let : Countable C := hcount.to_subtype
    have hcover : v '' F ⊆ ⋃ U : C, v '' (F ∩ U.val) := by
      rintro _ ⟨x, hx, rfl⟩
      let U : C := ⟨connectedComponentIn O x, x, hFO hx, rfl⟩
      exact mem_iUnion.mpr ⟨U, x, ⟨hx, mem_connectedComponentIn (hFO hx)⟩, rfl⟩
    have hpiece (U : C) : volume (v '' (F ∩ U.val)) ≤ ENNReal.ofReal A * μ U.val := by
      calc
        _ ≤ ediam (v '' (F ∩ U.val)) := Real.volume_le_diam _
        _ ≤ ENNReal.ofReal (A * μ.real U.val) := by
          apply Metric.ediam_le
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          rw [edist_dist, Real.dist_eq]
          exact ENNReal.ofReal_le_ofReal (hosc U.val (hC _ U.property).1
            (hC _ U.property).2.1 x hx y hy)
        _ = ENNReal.ofReal A * μ U.val := by
          rw [ENNReal.ofReal_mul hA, ofReal_measureReal]
    have hdc : Pairwise (Disjoint on fun U : C => U.val) := by
      intro U V hne
      exact hd U.property V.property (fun heq => hne (Subtype.ext heq))
    have hunion : (⋃ U : C, U.val) = O := by
      apply Subset.antisymm
      · exact iUnion_subset (fun U => (hC _ U.property).2.2)
      · intro x hx
        exact mem_iUnion.mpr ⟨⟨connectedComponentIn O x, x, hx, rfl⟩,
          mem_connectedComponentIn hx⟩
    calc
      volume (v '' F) ≤ volume (⋃ U : C, v '' (F ∩ U.val)) := measure_mono hcover
      _ ≤ ∑' U : C, volume (v '' (F ∩ U.val)) := measure_iUnion_le _
      _ ≤ ∑' U : C, ENNReal.ofReal A * μ U.val := ENNReal.tsum_le_tsum hpiece
      _ = ENNReal.ofReal A * ∑' U : C, μ U.val := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal A * μ O := by
        rw [← measure_iUnion hdc (fun U => (hC _ U.property).1.measurableSet), hunion]
  have hzero : volume (v '' F) ≤ ENNReal.ofReal A * μ F := by
    by_cases hAz : ENNReal.ofReal A = 0
    · simpa only [hAz, zero_mul] using hbound univ (subset_univ _) isOpen_univ
    · rw [F.measure_eq_iInf_isOpen μ]
      simp_rw [ENNReal.mul_iInf_of_ne hAz ENNReal.ofReal_ne_top]
      exact le_iInf (fun U => le_iInf (fun hFU => le_iInf (fun hU => hbound U hFU hU)))
  rw [hF, mul_zero] at hzero
  exact le_antisymm hzero bot_le

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LocalNullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local null-image criterion

Restrict the connected-neighborhood oscillation argument to an open
region. Oscillation need only be controlled on connected open sets
inside that region; no behavior across its boundary is required.
-/

open Set MeasureTheory Metric

namespace CircleDomainRigidity

theorem null_image_inter_open_of_connected_open_oscillation
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyConnectedSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [μ.OuterRegular] {F V : Set X} (hV : IsOpen V) (hF : μ (F ∩ V) = 0)
    (v : X → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hosc : ∀ U : Set X, U ⊆ V → IsOpen U → IsConnected U →
      ∀ x ∈ F ∩ U, ∀ y ∈ F ∩ U, |v x - v y| ≤ A * μ.real U) :
    volume (v '' (F ∩ V)) = 0 := by
  let ν : Measure V := μ.comap Subtype.val
  let : LocallyConnectedSpace V := hV.locallyConnectedSpace
  have hemb : MeasurableEmbedding (Subtype.val : V → X) :=
    MeasurableEmbedding.subtype_coe hV.measurableSet
  let : ν.OuterRegular := Measure.OuterRegular.comap' μ continuous_subtype_val hemb
  let Fv : Set V := Subtype.val ⁻¹' F
  have hnull : ν Fv = 0 := by
    rw [show ν Fv = μ (Subtype.val '' Fv) from hemb.comap_apply μ Fv]
    simpa only [Fv, Subtype.image_preimage_coe, inter_comm] using hF
  have hoscV : ∀ U : Set V, IsOpen U → IsConnected U →
      ∀ x ∈ Fv ∩ U, ∀ y ∈ Fv ∩ U,
        |v x.val - v y.val| ≤ A * ν.real U := by
    intro U hU hconn x hx y hy
    have hsub : Subtype.val '' U ⊆ V := by
      rintro _ ⟨z, _, rfl⟩
      exact z.property
    have hopen : IsOpen (Subtype.val '' U) := hV.isOpenMap_subtype_val U hU
    have hconnected : IsConnected (Subtype.val '' U) :=
      hconn.image Subtype.val continuous_subtype_val.continuousOn
    have hb := hosc _ hsub hopen hconnected x.val
      ⟨hx.1, x, hx.2, rfl⟩ y.val ⟨hy.1, y, hy.2, rfl⟩
    have hmeasure : ν.real U = μ.real (Subtype.val '' U) := by
      simp only [measureReal_def, ν, hemb.comap_apply]
    rwa [hmeasure]
  have hz := null_image_of_connected_open_oscillation hnull
    (fun x : V => v x.val) hA hoscV
  have himage : (fun x : V => v x.val) '' Fv = v '' (F ∩ V) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, ⟨hx, x.property⟩, rfl⟩
    · rintro ⟨x, ⟨hxF, hxV⟩, rfl⟩
      exact ⟨⟨x, hxV⟩, hxF, rfl⟩
  rwa [himage] at hz

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceCompression
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar tail compression used for common-point traces. The null-image
recovery works for arbitrary subsets of the line, by applying the monotone
area formula to a measurable envelope. No analyticity premise is needed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem null_outside_of_compressed_image_null
    {H : ℝ → ℝ} (hH : Continuous H) (hmono : Monotone H)
    {E S : Set ℝ} (hE : MeasurableSet E)
    (hd : ∀ᵐ x ∂volume, x ∉ E → HasDerivAt H 1 x)
    (hnull : volume (H '' S) = 0) : volume (S \ E) = 0 := by
  let N := toMeasurable volume (H '' S)
  let D := toMeasurable volume {x | x ∉ E ∧ ¬HasDerivAt H 1 x}
  have hN : volume N = 0 := by simpa only [N,measure_toMeasurable] using hnull
  have hD : volume D = 0 := by
    rw [show D = toMeasurable volume {x | x ∉ E ∧ ¬HasDerivAt H 1 x} from rfl,
      measure_toMeasurable]
    simpa only [not_forall,_root_.not_imp,exists_prop] using (ae_iff.mp hd)
  let T := (Eᶜ ∩ H ⁻¹' N) \ D
  have hT : MeasurableSet T :=
    (hE.compl.inter (hH.measurable (measurableSet_toMeasurable _ _))).diff
      (measurableSet_toMeasurable _ _)
  have hder (x : ℝ) (hx : x ∈ T) : HasDerivWithinAt H 1 T x := by
    apply HasDerivAt.hasDerivWithinAt
    by_contra hn
    exact hx.2 (subset_toMeasurable volume _ ⟨hx.1.1,hn⟩)
  have ht0 : volume T = 0 := by
    have he := lintegral_deriv_eq_volume_image_of_monotoneOn hT hder (hmono.monotoneOn T)
    have hi : H '' T ⊆ N := by rintro _ ⟨x,hx,rfl⟩; exact hx.1.2
    have hz := measure_mono_null hi hN
    simpa only [ENNReal.ofReal_one,lintegral_const,one_mul,hz,Measure.restrict_apply_univ] using he
  apply measure_mono_null (t := T ∪ D) _ (measure_union_null ht0 hD)
  intro x hx
  by_cases hxD : x ∈ D
  · exact Or.inr hxD
  · exact Or.inl ⟨⟨hx.2,subset_toMeasurable volume _ (mem_image_of_mem H hx.1)⟩,hxD⟩

 theorem traceCompression_intervalIntegrable {E : Set ℝ} (hE : MeasurableSet E)
    (a b : ℝ) : IntervalIntegrable (Eᶜ.indicator (fun _ => (1 : ℝ))) volume a b :=
  intervalIntegrable_iff.mpr
    ((((locallyIntegrable_const (μ := (volume : Measure ℝ)) (1 : ℝ)).indicator hE.compl).integrableOn_isCompact
      isCompact_uIcc).mono_set uIoc_subset_uIcc)

 theorem traceCompression_sub {E : Set ℝ} (hE : MeasurableSet E) (a x y : ℝ) :
    traceCompression E a y-traceCompression E a x =
      ∫ s in x..y, Eᶜ.indicator (fun _ => (1 : ℝ)) s := by
  exact intervalIntegral.integral_interval_sub_left
    (traceCompression_intervalIntegrable hE a y) (traceCompression_intervalIntegrable hE a x)

 theorem traceCompression_monotone {E : Set ℝ} (hE : MeasurableSet E) (a : ℝ) :
    Monotone (traceCompression E a) := by
  intro x y hxy
  apply sub_nonneg.mp
  rw [traceCompression_sub hE]
  exact intervalIntegral.integral_nonneg_of_forall hxy
    (fun s => indicator_nonneg (fun _ _ => zero_le_one) s)

 theorem traceCompression_lipschitz {E : Set ℝ} (hE : MeasurableSet E) (a : ℝ) :
    LipschitzWith 1 (traceCompression E a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.dist_eq,← Real.norm_eq_abs,traceCompression_sub hE]
  simpa only [NNReal.coe_one,one_mul] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x) (C := 1)
      (f := Eᶜ.indicator (fun _ => (1 : ℝ)))
      (fun s _ => by simpa using (norm_indicator_le_norm_self (s := Eᶜ) (fun _ => (1 : ℝ)) s))

 theorem traceCompression_ae_deriv {E : Set ℝ} (hE : MeasurableSet E) (a : ℝ) :
    ∀ᵐ x ∂volume, x ∉ E → HasDerivAt (traceCompression E a) 1 x := by
  have hli : LocallyIntegrable (Eᶜ.indicator (fun _ => (1 : ℝ))) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hE.compl
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hli] with x hx hxe
  have hx' := hx a
  rw [indicator_of_mem (show x ∈ Eᶜ from hxe)] at hx'
  convert hx' using 1
  all_goals try with_reducible_and_instances rfl
  rfl

 theorem traceCompression_null_recovery {E S : Set ℝ} (hE : MeasurableSet E) (a : ℝ)
    (hn : volume (traceCompression E a '' S) = 0) : volume (S \ E) = 0 :=
  null_outside_of_compressed_image_null (traceCompression_lipschitz hE a).continuous
    (traceCompression_monotone hE a) hE (traceCompression_ae_deriv hE a) hn

 theorem null_of_tail_compressions {E : ℕ → Set ℝ} {S : Set ℝ}
    (hE : ∀ n, MeasurableSet (E n)) (a : ℝ)
    (hnull : ∀ n, volume (traceCompression (E n) a '' S) = 0)
    (htail : Tendsto (fun n => volume (E n)) atTop (𝓝 0)) : volume S = 0 := by
  have hle (n : ℕ) : volume S ≤ volume (E n) := by
    calc
      volume S ≤ volume ((S \ E n) ∪ E n) := measure_mono (by intro x hx; by_cases he : x ∈ E n; exact Or.inr he; exact Or.inl ⟨hx,he⟩)
      _ ≤ volume (S \ E n) + volume (E n) := measure_union_le _ _
      _ = volume (E n) := by rw [traceCompression_null_recovery (hE n) a (hnull n),zero_add]
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds htail hle) bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskPrimitive
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral primitives of the actual finite and infinite trace masks.
The finite spatial variation is bounded by interval lengths times cutoff
variation, while endpoint changes are always one-Lipschitz. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finiteTraceMask_norm_le {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (s : ℝ) (n : ℕ) :
    ‖finiteTraceMask cutoff I x s n‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (finiteTraceMask_bounds hc I x s n).1]
  exact (finiteTraceMask_bounds hc I x s n).2

 theorem finiteTraceMask_intervalIntegrable {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s => finiteTraceMask cutoff I x s n) volume a b := by
  apply intervalIntegrable_iff.mpr
  exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).def'.mono'
    ((finiteTraceMask_measurable cutoff hI x n).aestronglyMeasurable.restrict)
    (Eventually.of_forall (fun s => finiteTraceMask_norm_le hc I x s n))

 theorem finiteTracePrimitive_sub {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) (a s t : ℝ) :
    finiteTracePrimitive cutoff I a x t n-finiteTracePrimitive cutoff I a x s n =
      ∫ u in s..t, finiteTraceMask cutoff I x u n :=
  intervalIntegral.integral_interval_sub_left
    (finiteTraceMask_intervalIntegrable hc hI x n a t)
    (finiteTraceMask_intervalIntegrable hc hI x n a s)

 theorem finiteTracePrimitive_lipschitz {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) (a : ℝ) :
    LipschitzWith 1 (fun t => finiteTracePrimitive cutoff I a x t n) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [Real.dist_eq,Real.dist_eq,← Real.norm_eq_abs,finiteTracePrimitive_sub hc hI]
  simpa only [NNReal.coe_one,one_mul] using
    intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (a := s) (b := t)
      (fun u _ => finiteTraceMask_norm_le hc I x u n)

 theorem finiteTracePrimitive_variation {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    (x y : X) (a t : ℝ) (n : ℕ) :
    |finiteTracePrimitive cutoff I a x t n-finiteTracePrimitive cutoff I a y t n| ≤
      ∑ j ∈ Finset.range n, volume.real (I j)*|cutoff j x-cutoff j y| := by
  let p := fun s => ∑ j ∈ Finset.range n, (I j).indicator (fun _ => |cutoff j x-cutoff j y|) s
  have hi (j : ℕ) : Integrable ((I j).indicator (fun _ => |cutoff j x-cutoff j y|)) volume :=
    (integrableOn_const (hIf j)).integrable_indicator (hI j)
  have hp : Integrable p volume := integrable_finsetSum _ (fun j _ => hi j)
  have hp0 (s : ℝ) : 0 ≤ p s :=
    Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => abs_nonneg _) s)
  rw [finiteTracePrimitive,finiteTracePrimitive,← intervalIntegral.integral_sub
    (finiteTraceMask_intervalIntegrable hc hI x n a t)
    (finiteTraceMask_intervalIntegrable hc hI y n a t),← Real.norm_eq_abs]
  calc
    _ ≤ ∫ s in uIoc a t, ‖finiteTraceMask cutoff I x s n-finiteTraceMask cutoff I y s n‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ s in uIoc a t, p s := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => norm_nonneg _)) hp.restrict
      (Eventually.of_forall (fun s => by
        simpa only [Real.norm_eq_abs] using finiteTraceMask_variation cutoff I x y s n))
    _ ≤ ∫ s, p s := integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hp0) hp
    _ = _ := by
      rw [integral_finsetSum _ (fun j _ => hi j)]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_indicator_const _ (hI j)

 theorem infiniteTraceMask_bounds {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (s : ℝ) :
    infiniteTraceMask cutoff I x s ∈ Icc (0:ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (finiteTraceMask_tendsto hc I x s)
    (Eventually.of_forall (fun n => finiteTraceMask_bounds hc I x s n))

 theorem finiteTracePrimitive_tendsto {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (a t : ℝ) :
    Tendsto (fun n => finiteTracePrimitive cutoff I a x t n) atTop
      (𝓝 (infiniteTracePrimitive cutoff I a x t)) := by
  have ht : Tendsto (fun n => ∫ s in uIoc a t, finiteTraceMask cutoff I x s n) atTop
      (𝓝 (∫ s in uIoc a t, infiniteTraceMask cutoff I x s)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (finiteTraceMask_measurable cutoff hI x n).aestronglyMeasurable.restrict)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a t).def'
      (fun n => Eventually.of_forall (fun s => finiteTraceMask_norm_le hc I x s n))
      (Eventually.of_forall (fun s => finiteTraceMask_tendsto hc I x s))
  simpa only [finiteTracePrimitive,infiniteTracePrimitive,
    intervalIntegral.intervalIntegral_eq_integral_uIoc] using
    ht.const_smul (if a ≤ t then (1 : ℝ) else -1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskTail
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A tail which is inactive outside one scalar interval changes the
entire primitive by at most that interval's length. This is the local
finite approximation used at accumulating common-point components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem finiteTraceMask_tail_eq {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {N n : ℕ} (hn : N ≤ n)
    (htail : ∀ j, N ≤ j → t ∈ I j → cutoff j x = 1) :
    finiteTraceMask cutoff I x t n = finiteTraceMask cutoff I x t N := by
  induction n,hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [finiteTraceMask,ih]
    have he : (if t ∈ I n then cutoff n x else 1) = 1 := by
      split_ifs with ht
      · exact htail n hn ht
      · rfl
    rw [he,min_eq_left (finiteTraceMask_bounds hc I x t N).2]

 theorem infiniteTraceMask_tail_eq {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {N : ℕ}
    (htail : ∀ j, N ≤ j → t ∈ I j → cutoff j x = 1) :
    infiniteTraceMask cutoff I x t = finiteTraceMask cutoff I x t N := by
  apply tendsto_nhds_unique (finiteTraceMask_tendsto hc I x t)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (finiteTraceMask_tail_eq hc hn htail).symm

 theorem infiniteTraceMask_measurable {X : Type*} (cutoff : ℕ → X → ℝ)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (x : X) :
    Measurable (infiniteTraceMask cutoff I x) :=
  Measurable.iInf (fun n => finiteTraceMask_measurable cutoff hI x n)

 theorem infiniteTraceMask_intervalIntegrable {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (a b : ℝ) :
    IntervalIntegrable (infiniteTraceMask cutoff I x) volume a b := by
  apply intervalIntegrable_iff.mpr
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).def'.mono'
    ((infiniteTraceMask_measurable cutoff hI x).aestronglyMeasurable.restrict)
  apply Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs,abs_of_nonneg (infiniteTraceMask_bounds hc I x s).1]
  exact (infiniteTraceMask_bounds hc I x s).2

 theorem tracePrimitive_tail_bound {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) {J : Set ℝ}
    (hJ : MeasurableSet J) (hJf : volume J ≠ ∞) {x : X} {N : ℕ}
    (htail : ∀ j, N ≤ j → ∀ t ∈ I j, t ∉ J → cutoff j x = 1)
    (a t : ℝ) :
    |infiniteTracePrimitive cutoff I a x t-finiteTracePrimitive cutoff I a x t N| ≤
      volume.real J := by
  let p := J.indicator (fun _ => (1 : ℝ))
  have hp : Integrable p volume := (integrableOn_const hJf).integrable_indicator hJ
  have hp0 (s : ℝ) : 0 ≤ p s := indicator_nonneg (fun _ _ => zero_le_one) s
  have hbound (s : ℝ) :
      ‖infiniteTraceMask cutoff I x s-finiteTraceMask cutoff I x s N‖ ≤ p s := by
    by_cases hs : s ∈ J
    · rw [show p s = 1 from indicator_of_mem hs _]
      rw [Real.norm_eq_abs,abs_le]
      have h1 := infiniteTraceMask_bounds hc I x s
      have h2 := finiteTraceMask_bounds hc I x s N
      constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
    · rw [infiniteTraceMask_tail_eq hc (fun j hj hij => htail j hj s hij hs),sub_self,norm_zero]
      exact hp0 s
  rw [infiniteTracePrimitive,finiteTracePrimitive,← intervalIntegral.integral_sub
    (infiniteTraceMask_intervalIntegrable hc hI x a t)
    (finiteTraceMask_intervalIntegrable hc hI x N a t),← Real.norm_eq_abs]
  calc
    _ ≤ ∫ s in uIoc a t, ‖infiniteTraceMask cutoff I x s-finiteTraceMask cutoff I x s N‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ s in uIoc a t, p s := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => norm_nonneg _)) hp.restrict
      (Eventually.of_forall hbound)
    _ ≤ ∫ s, p s := integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hp0) hp
    _ = volume.real J := integral_indicator_one hJ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TracePrimitiveContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of finite primitives follows from the explicit
finite variation bound. Uniformly small scalar tails then prove the
continuity of the actual infinite masked scalar at a common point. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finiteTracePrimitive_continuous {X : Type*} [TopologicalSpace X]
    {cutoff : ℕ → X → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    (a : ℝ) (n : ℕ) :
    Continuous (fun p : X × ℝ => finiteTracePrimitive cutoff I a p.1 p.2 n) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := fun q : X × ℝ => |q.2-p.2|+
    ∑ j ∈ Finset.range n, volume.real (I j)*|cutoff j q.1-cutoff j p.1|
  have hB : Continuous B := by dsimp only [B]; fun_prop
  have hB0 : B p = 0 := by simp [B]
  have hb : Tendsto B (𝓝 p) (𝓝 0) := hB0 ▸ hB.continuousAt.tendsto
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ hb
  intro q
  calc
    _ ≤ dist (finiteTracePrimitive cutoff I a q.1 q.2 n)
          (finiteTracePrimitive cutoff I a q.1 p.2 n)+
        dist (finiteTracePrimitive cutoff I a q.1 p.2 n)
          (finiteTracePrimitive cutoff I a p.1 p.2 n) := dist_triangle _ _ _
    _ ≤ B q := by
      apply add_le_add
      · simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using
          (finiteTracePrimitive_lipschitz hc hI q.1 n a).dist_le_mul q.2 p.2
      · simpa only [Real.dist_eq] using finiteTracePrimitive_variation hc hI hIf q.1 p.1 a p.2 n

 theorem infinite_masked_scalar_continuousAt {X : Type*} [TopologicalSpace X]
    {cutoff : ℕ → X → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {b : X → ℝ} {x : X} (hb : ContinuousAt b x) (a : ℝ)
    (htail : ∀ δ > 0, ∃ N : ℕ, ∀ᶠ y in 𝓝 x,
      ∀ j, N ≤ j → ∀ t ∈ I j, t ∉ Ioo (b x-δ) (b x+δ) → cutoff j y = 1) :
    ContinuousAt (fun y => infiniteTracePrimitive cutoff I a y (b y)) x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/8
  have hδ : 0 < δ := by dsimp only [δ] <;> positivity
  obtain ⟨N,hN⟩ := htail δ hδ
  have hNx := hN.self_of_nhds
  have hcont := (finiteTracePrimitive_continuous hc hcc hI hIf a N).continuousAt.comp
    (continuousAt_id.prodMk hb)
  have hnear := hcont.eventually (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hN,hnear] with y hy hnear
  have hJ : MeasurableSet (Ioo (b x-δ) (b x+δ)) := measurableSet_Ioo
  have hJf : volume (Ioo (b x-δ) (b x+δ)) ≠ ∞ := by simp
  have hlen : volume.real (Ioo (b x-δ) (b x+δ)) = 2*δ := by
    rw [Real.volume_real_Ioo_of_le (by linarith : b x-δ ≤ b x+δ)]
    ring
  have h1 := tracePrimitive_tail_bound hc hI hJ hJf hy a (b y)
  have h2 := tracePrimitive_tail_bound hc hI hJ hJf hNx a (b x)
  rw [hlen] at h1 h2
  have h3 : dist (finiteTracePrimitive cutoff I a y (b y) N)
      (finiteTracePrimitive cutoff I a x (b x) N) < δ := hnear
  have hd := dist_triangle (infiniteTracePrimitive cutoff I a y (b y))
    (finiteTracePrimitive cutoff I a y (b y) N) (infiniteTracePrimitive cutoff I a x (b x))
  have hd' := dist_triangle (finiteTracePrimitive cutoff I a y (b y) N)
    (finiteTracePrimitive cutoff I a x (b x) N) (infiniteTracePrimitive cutoff I a x (b x))
  simp only [Real.dist_eq] at hd hd' h3 ⊢
  have h2' : |finiteTracePrimitive cutoff I a x (b x) N-
      infiniteTracePrimitive cutoff I a x (b x)| ≤ 2*δ := by simpa only [abs_sub_comm] using h2
  dsimp only [δ] at *
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TracePrimitivePlateau
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On an indexed component neighborhood an active zero cutoff fixes the
upper endpoint of the primitive. Late intervals absorbed by that same
zero interval have no effect, so the infinite masked scalar is locally
an actual finite continuous primitive, even when the raw scalar jumps. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem infiniteTraceMask_zero_of_active {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {j : ℕ} (ht : t ∈ I j) (hz : cutoff j x = 0) :
    infiniteTraceMask cutoff I x t = 0 := by
  apply tendsto_nhds_unique (finiteTraceMask_tendsto hc I x t)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with n hn
  exact (finiteTraceMask_zero_of_active hc hn ht hz).symm

 theorem infiniteTracePrimitive_plateau {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) {x : X} {j : ℕ}
    (hconv : OrdConnected (I j)) (hz : cutoff j x = 0) {s t : ℝ}
    (hs : s ∈ I j) (ht : t ∈ I j) (a : ℝ) :
    infiniteTracePrimitive cutoff I a x s = infiniteTracePrimitive cutoff I a x t := by
  apply sub_eq_zero.mp
  rw [infiniteTracePrimitive,infiniteTracePrimitive,
    intervalIntegral.integral_interval_sub_left
      (infiniteTraceMask_intervalIntegrable hc hI x a s)
      (infiniteTraceMask_intervalIntegrable hc hI x a t)]
  calc
    _ = ∫ u in t..s, (0 : ℝ) := intervalIntegral.integral_congr (fun u hu =>
      infiniteTraceMask_zero_of_active hc (hconv.uIcc_subset ht hs hu) hz)
    _ = 0 := by simp

 theorem infiniteTraceMask_absorbed_tail {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {j N : ℕ} (hj : j < N) (hz : cutoff j x = 0)
    (htail : ∀ k, N ≤ k → ∀ t ∈ I k, cutoff k x ≠ 1 → t ∈ I j) (t : ℝ) :
    infiniteTraceMask cutoff I x t = finiteTraceMask cutoff I x t N := by
  by_cases ht : t ∈ I j
  · rw [infiniteTraceMask_zero_of_active hc ht hz,finiteTraceMask_zero_of_active hc hj ht hz]
  · apply infiniteTraceMask_tail_eq hc
    intro k hk hkI
    by_contra he
    exact ht (htail k hk t hkI he)

 theorem infiniteTracePrimitive_absorbed_tail {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {j N : ℕ} (hj : j < N) (hz : cutoff j x = 0)
    (htail : ∀ k, N ≤ k → ∀ t ∈ I k, cutoff k x ≠ 1 → t ∈ I j) (a t : ℝ) :
    infiniteTracePrimitive cutoff I a x t = finiteTracePrimitive cutoff I a x t N := by
  apply intervalIntegral.integral_congr
  intro u _
  exact infiniteTraceMask_absorbed_tail hc hj hz htail u

 theorem indexed_masked_scalar_continuousAt {X : Type*} [TopologicalSpace X]
    {cutoff : ℕ → X → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {b : X → ℝ} {x : X} {j N : ℕ} (hj : j < N)
    (hconv : OrdConnected (I j)) {β : ℝ} (hβ : β ∈ I j) (a : ℝ)
    (hnear : ∀ᶠ y in 𝓝 x, cutoff j y = 0 ∧ b y ∈ I j ∧
      ∀ k, N ≤ k → ∀ t ∈ I k, cutoff k y ≠ 1 → t ∈ I j) :
    ContinuousAt (fun y => infiniteTracePrimitive cutoff I a y (b y)) x := by
  have hh : (fun y => infiniteTracePrimitive cutoff I a y (b y)) =ᶠ[𝓝 x]
      (fun y => finiteTracePrimitive cutoff I a y β N) := by
    filter_upwards [hnear] with y hy
    rw [infiniteTracePrimitive_plateau hc hI hconv hy.1 hy.2.1 hβ a,
      infiniteTracePrimitive_absorbed_tail hc hj hy.1 hy.2.2 a β]
  have hcont : ContinuousAt (fun y => finiteTracePrimitive cutoff I a y β N) x :=
    (finiteTracePrimitive_continuous hc hcc hI hIf a N).continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)
  exact hcont.congr_of_eventuallyEq hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedRelationNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed relation with compact target sends a neighborhood of a
compact source set into every open neighborhood of its fibers. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_relation_neighborhood {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] {R : X → Y → Prop}
    (hR : IsClosed {p : X × Y | R p.1 p.2}) {K : Set X} {U : Set Y}
    (hU : IsOpen U) (hKU : ∀ x ∈ K, ∀ y, R x y → y ∈ U) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, ∀ y, R x y → y ∈ U := by
  let B := {p : X × Y | R p.1 p.2} ∩ (univ ×ˢ Uᶜ)
  have hB : IsClosed B := hR.inter (isClosed_univ.prod hU.isClosed_compl)
  have hproj : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  refine ⟨(Prod.fst '' B)ᶜ,hproj.isOpen_compl,?_,?_⟩
  · intro x hx
    rintro ⟨p,hp,hpx⟩
    have hr : R p.1 p.2 := hp.1
    have hr' : R x p.2 := by simpa only [hpx] using hr
    exact hp.2.2 (hKU x hx p.2 hr')
  · intro x hx y hxy
    by_contra hy
    exact hx ⟨(x,y),⟨hxy,⟨mem_univ _,hy⟩⟩,rfl⟩

 theorem closed_relation_selection_continuousAt {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    (b : X → Y) (hb : ∀ x, R x (b x)) {x : X}
    (hfiber : ∀ y, R x y → y = b x) : ContinuousAt b x := by
  apply continuousAt_def.mpr
  intro U hU
  obtain ⟨W,hWU,hW,hxW⟩ := mem_nhds_iff.mp hU
  obtain ⟨V,hV,hxV,hmap⟩ := closed_relation_neighborhood (K := {x}) hR hW (by
    intro z hz y hzy
    rw [mem_singleton_iff] at hz
    subst z
    rwa [hfiber y hzy])
  filter_upwards [hV.mem_nhds (hxV (mem_singleton x))] with z hz
  exact hWU (hmap z hz (b z) (hb z))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ShrinkingBallNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact source sets uniformly control the centers of late shrinking
balls that meet a fixed neighborhood. Applied to a closed correspondence,
this controls every scalar interval of such a ball, not just its center. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem nonnegative_square_summable_tendsto_zero {d : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (hs : Summable (fun j => d j^2)) :
    Tendsto d atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hs.tendsto_atTop_zero.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with j hj
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (hd j)]
  nlinarith

 theorem shrinking_balls_near_compact {X : Type*} [PseudoMetricSpace X]
    {K W : Set X} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (c : ℕ → X) {d : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0)) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ z ∈ V, z ∈ ball (c j) (d j) → c j ∈ W := by
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open hW hKW
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hd.eventually (gt_mem_nhds (half_pos hδ)))
  refine ⟨thickening (δ/2) K,isOpen_thickening,self_subset_thickening (half_pos hδ) K,N,?_⟩
  intro j hj z hz hball
  obtain ⟨k,hk,hzk⟩ := mem_thickening_iff.mp hz
  apply hsub
  apply mem_cthickening_of_dist_le (c j) k δ K hk
  have hcz : dist (c j) z < d j := by simpa only [mem_ball,dist_comm] using hball
  exact (dist_triangle _ _ _).trans ((add_lt_add hcz hzk).le.trans (by linarith [hN j hj]))

 theorem closed_relation_shrinking_intervals {X Y : Type*} [PseudoMetricSpace X]
    [TopologicalSpace Y] [CompactSpace Y] {R : X → Y → Prop}
    (hR : IsClosed {p : X × Y | R p.1 p.2}) {φ : Y → ℝ} (hφ : Continuous φ)
    {K : Set X} (hK : IsCompact K) {a b η : ℝ} (hη : 0 < η)
    (hmargin : ∀ q ∈ K, ∀ p, R q p → φ p ∈ Ioo (a+η) (b-η))
    (c : ℕ → X) {d ε : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0)) (I : ℕ → Set ℝ)
    (hI : ∀ j t, t ∈ I j → ∃ p, R (c j) p ∧ |t-φ p| ≤ ε j) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ z ∈ V, z ∈ ball (c j) (d j) → I j ⊆ Ioo a b := by
  obtain ⟨W,hW,hKW,hw⟩ := closed_relation_neighborhood hR
    (isOpen_Ioo.preimage hφ) hmargin
  obtain ⟨V,hV,hKV,N,hN⟩ := shrinking_balls_near_compact hK hW hKW c hd
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hε.eventually (gt_mem_nhds hη))
  refine ⟨V,hV,hKV,max N M,?_⟩
  intro j hj z hz hbz t ht
  obtain ⟨p,hp,hpt⟩ := hI j t ht
  have hpm := hw (c j) (hN j ((le_max_left _ _).trans hj) z hz hbz) p hp
  have hεj := hM j ((le_max_right _ _).trans hj)
  have habs := abs_le.mp hpt
  constructor <;> linarith [hpm.1,hpm.2,habs.1,habs.2]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CorrespondenceMaskContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed component correspondence and shrinking balloon radii supply
the tail conditions in the continuity proof of the actual infinite mask. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem correspondence_mask_continuousAt_singleton
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    {s : X → Y} (hs : ∀ q, R q (s q)) {φ : Y → ℝ} (hφ : Continuous φ)
    {cutoff : ℕ → X → ℝ} (hc : ∀ j q, cutoff j q ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) (c : ℕ → X) {d ε : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hout : ∀ j q, d j ≤ dist q (c j) → cutoff j q = 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ⊤)
    (hrep : ∀ j t, t ∈ I j → ∃ p, R (c j) p ∧ |t-φ p| ≤ ε j)
    {x : X} (hsingle : ∀ p, R x p → p = s x) (a : ℝ) :
    ContinuousAt (fun q => infiniteTracePrimitive cutoff I a q (φ (s q))) x := by
  have hb := hφ.continuousAt.comp (closed_relation_selection_continuousAt hR s hs hsingle)
  apply infinite_masked_scalar_continuousAt hc hcc hI hIf hb a
  intro δ hδ
  obtain ⟨V,hV,hxV,N,hN⟩ := closed_relation_shrinking_intervals hR hφ
    (K := {x}) isCompact_singleton (half_pos hδ)
    (a := φ (s x)-δ) (b := φ (s x)+δ) (by
      intro q hq p hp
      rw [mem_singleton_iff] at hq
      subst q
      rw [hsingle p hp]
      constructor <;> linarith) c hd hε I hrep
  refine ⟨N,?_⟩
  filter_upwards [hV.mem_nhds (hxV (mem_singleton x))] with q hq
  intro j hj t ht hnot
  by_contra hne
  have hball : q ∈ ball (c j) (d j) := by
    rw [mem_ball]
    exact lt_of_not_ge (fun hh => hne (hout j q hh))
  exact hnot (hN j hj q hq hball ht)

 theorem correspondence_mask_indexed_neighborhood
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    {s : X → Y} (hs : ∀ q, R q (s q)) {φ : Y → ℝ} (hφ : Continuous φ)
    {cutoff : ℕ → X → ℝ} (hc : ∀ j q, cutoff j q ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) (c : ℕ → X) {d ε : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hout : ∀ j q, d j ≤ dist q (c j) → cutoff j q = 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ⊤)
    (hrep : ∀ j t, t ∈ I j → ∃ p, R (c j) p ∧ |t-φ p| ≤ ε j)
    {K Z : Set X} (hK : IsCompact K) (hZ : IsOpen Z) (hKZ : K ⊆ Z)
    {j : ℕ} (hzero : ∀ q ∈ Z, cutoff j q = 0)
    {A B η β : ℝ} (hη : 0 < η) (hIj : I j = Ioo A B) (hβ : β ∈ I j)
    (hmargin : ∀ q ∈ K, ∀ p, R q p → φ p ∈ Ioo (A+η) (B-η)) (a : ℝ) :
    ∃ (N : ℕ) (V : Set X), IsOpen V ∧ K ⊆ V ∧
      ContinuousOn (fun q => infiniteTracePrimitive cutoff I a q (φ (s q))) V ∧
      ∀ q ∈ V, infiniteTracePrimitive cutoff I a q (φ (s q)) =
        finiteTracePrimitive cutoff I a q β N := by
  obtain ⟨T,hT,hKT,N,hN⟩ := closed_relation_shrinking_intervals hR hφ hK hη
    hmargin c hd hε I hrep
  obtain ⟨W,hW,hKW,hraw⟩ := closed_relation_neighborhood hR ((isOpen_Ioo : IsOpen (Ioo A B)).preimage hφ) (by
    intro q hq p hp
    have h := hmargin q hq p hp
    exact ⟨by linarith [h.1],by linarith [h.2]⟩)
  let V := Z ∩ T ∩ W
  let M := max N (j+1)
  have hV : IsOpen V := (hZ.inter hT).inter hW
  have hKV : K ⊆ V := fun q hq => ⟨⟨hKZ hq,hKT hq⟩,hKW hq⟩
  have hj : j < M := lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)
  have hdata (q : X) (hq : q ∈ V) : cutoff j q = 0 ∧ φ (s q) ∈ I j ∧
      ∀ k, M ≤ k → ∀ t ∈ I k, cutoff k q ≠ 1 → t ∈ I j := by
    refine ⟨hzero q hq.1.1,?_,?_⟩
    · rw [hIj]
      exact hraw q hq.2 _ (hs q)
    · intro k hk t ht hne
      rw [hIj]
      apply hN k ((le_max_left _ _).trans hk) q hq.1.2 _ ht
      rw [mem_ball]
      exact lt_of_not_ge (fun hh => hne (hout k q hh))
  refine ⟨M,V,hV,hKV,?_,?_⟩
  · intro q hq
    apply ContinuousAt.continuousWithinAt
    apply indexed_masked_scalar_continuousAt hc hcc hI hIf hj
      (hIj ▸ ordConnected_Ioo) hβ a
    filter_upwards [hV.mem_nhds hq] with z hz
    exact hdata z hz
  · intro q hq
    have h := hdata q hq
    rw [infiniteTracePrimitive_plateau hc hI (hIj ▸ ordConnected_Ioo) h.1 h.2.1 hβ a,
      infiniteTracePrimitive_absorbed_tail hc hj h.1 h.2.2 a β]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedCoreExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connected retained-core exhaustions

Compact exhaustion and paths in an open plane domain give nested connected
open cores with compact closure in that domain. Adjoining one fixed exterior
then gives the cofinite cores required by normalized model compactness.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_connected_plane_exhaustion
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsConnected G)
    {z₀ : ℂ} (hz₀ : z₀ ∈ G) :
    ∃ U : ℕ → Set ℂ,
      (∀ n, IsOpen (U n)) ∧ (∀ n, IsConnected (U n)) ∧ Monotone U ∧
      (∀ n, IsCompact (closure (U n)) ∧ closure (U n) ⊆ G) ∧
      (⋃ n, U n) = G ∧ z₀ ∈ U 0 := by
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let : LocallyPathConnectedSpace G := hG.locallyPathConnectedSpace
  let C := CompactExhaustion.choice G
  let x₀ : G := ⟨z₀, hz₀⟩
  obtain ⟨k₀, hk₀⟩ := C.exists_mem x₀
  let A : ℕ → Set G := fun n => connectedComponentIn (interior (C (n + k₀ + 1))) x₀
  have hxA (n : ℕ) : x₀ ∈ A n := by
    apply mem_connectedComponentIn
    apply C.subset_interior (by omega : k₀ < n + k₀ + 1)
    exact hk₀
  have hAo (n : ℕ) : IsOpen (A n) := isOpen_interior.connectedComponentIn
  have hAc (n : ℕ) : IsConnected (A n) :=
    ⟨⟨x₀, hxA n⟩, isPreconnected_connectedComponentIn⟩
  have hAm : Monotone A := by
    intro m n hmn
    exact connectedComponentIn_mono _ (interior_mono (C.subset (by omega)))
  let U : ℕ → Set ℂ := fun n => Subtype.val '' A n
  have hUclosed (n : ℕ) : closure (U n) ⊆ Subtype.val '' C (n + k₀ + 1) := by
    apply closure_minimal _ ((C.isCompact _).image continuous_subtype_val).isClosed
    exact image_mono ((connectedComponentIn_subset _ _).trans interior_subset)
  refine ⟨U, fun n => hG.isOpenMap_subtype_val _ (hAo n),
    fun n => (hAc n).image _ continuous_subtype_val.continuousOn,
    fun m n hmn => image_mono (hAm hmn), ?_, ?_, ⟨x₀, hxA 0, rfl⟩⟩
  · intro n
    exact ⟨((C.isCompact _).image continuous_subtype_val).of_isClosed_subset
      isClosed_closure (hUclosed n), (hUclosed n).trans (by rintro _ ⟨x, _, rfl⟩; exact x.property)⟩
  · apply Subset.antisymm
    · exact iUnion_subset fun n => by rintro _ ⟨x, _, rfl⟩; exact x.property
    · intro z hz
      let x : G := ⟨z, hz⟩
      have hj : Joined x₀ x := (hG.isConnected_iff_isPathConnected.mp hconn).joinedIn
        z₀ hz₀ z hz |>.joined_subtype
      let γ := hj.somePath
      obtain ⟨k, hk⟩ := C.exists_superset_of_isCompact (isCompact_range γ.continuous)
      have hrange : range γ ⊆ interior (C (k + k₀ + 1)) :=
        hk.trans (C.subset_interior (by omega : k < k + k₀ + 1))
      have hx : x ∈ A k :=
        (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
          (by exact ⟨0, γ.source⟩) hrange (by exact ⟨1, γ.target⟩)
      exact mem_iUnion.mpr ⟨k, x, hx, rfl⟩

/-- The cofinite cores retain a full fixed exterior, while the closure
of every core stays in the original domain. -/
theorem exists_cofinite_connected_plane_exhaustion
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsConnected G)
    {R : ℝ} (hR : 0 < R) (hext : {z : ℂ | R ≤ ‖z‖} ⊆ G) :
    ∃ D : ℕ → Set ℂ,
      (∀ n, IsOpen (D n)) ∧ (∀ n, IsConnected (D n)) ∧ Monotone D ∧
      (∀ n, closure (D n) ⊆ G) ∧ (⋃ n, D n) = G ∧
      {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0 := by
  let z₀ : ℂ := (2 * R : ℝ)
  have hnorm : ‖z₀‖ = 2 * R := by
    simp only [z₀, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * R)]
  have hz₀ : z₀ ∈ G := hext (by change R ≤ ‖z₀‖; rw [hnorm]; linarith)
  obtain ⟨U, hUo, hUc, hUm, hUcl, hUunion, hbase⟩ :=
    exists_connected_plane_exhaustion hG hconn hz₀
  let E : Set ℂ := (closedBall (0 : ℂ) R)ᶜ
  have hEo : IsOpen E := isClosed_closedBall.isOpen_compl
  have hEc : IsConnected E := isConnected_complex_exterior_closedBall hR.le
  have hzE : z₀ ∈ E := by
    simpa only [E, mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hnorm] using
      (by linarith : R < 2 * R)
  have hEcl : closure E ⊆ G := by
    rw [closure_compl, interior_closedBall (0 : ℂ) hR.ne']
    intro z hz
    apply hext
    change R ≤ ‖z‖
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz
  refine ⟨fun n => U n ∪ E, fun n => (hUo n).union hEo,
    fun n => (hUc n).union ⟨z₀, hUm (Nat.zero_le n) hbase, hzE⟩ hEc,
    fun m n hmn => union_subset_union_left E (hUm hmn), ?_, ?_, ?_⟩
  · intro n
    rw [closure_union]
    exact union_subset (hUcl n).2 hEcl
  · ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨n, hz | hz⟩
      · exact (hUcl n).2 (subset_closure hz)
      · exact hEcl (subset_closure hz)
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hUunion.symm ▸ hz)
      exact ⟨n, Or.inl hn⟩
  · intro z hz
    right
    have hz' : 2 * R ≤ ‖z‖ := hz
    change z ∉ closedBall (0 : ℂ) R
    rw [mem_closedBall, dist_zero_right, not_le]
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereCoreExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual source cores for domains containing infinity

The open connected cores exhaust the given domain. Their finite closures,
with infinity added, are compact subsets of the domain and can therefore
be prescribed in the finite-transfer construction.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isClosed_finite_set_with_infty {C : Set ℂ} (hC : IsClosed C) :
    IsClosed (((↑) : ℂ → Sphere) '' C ∪ {OnePoint.infty}) := by
  have he : (((↑) : ℂ → Sphere) '' C ∪ {OnePoint.infty})ᶜ =
      ((↑) : ℂ → Sphere) '' Cᶜ := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp
    | coe z => simp only [mem_compl_iff, mem_union, OnePoint.coe_injective.mem_set_image,
        mem_singleton_iff, OnePoint.coe_ne_infty, or_false]
  rw [← isOpen_compl_iff, he]
  exact OnePoint.isOpen_image_coe.mpr hC.isOpen_compl

theorem exists_sphere_connected_core_exhaustion
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) :
    ∃ (R : ℝ) (D : ℕ → Set ℂ) (K : ℕ → Set Sphere),
      0 < R ∧ (∀ n, IsOpen (D n)) ∧ (∀ n, IsConnected (D n)) ∧ Monotone D ∧
      (∀ n, K n = ((↑) : ℂ → Sphere) '' closure (D n) ∪ {OnePoint.infty}) ∧
      (∀ n, IsCompact (K n) ∧ K n ⊆ G) ∧
      (∀ n, ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ interior (K n)) ∧
      (⋃ n, ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty}) = G ∧
      {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0 ∧
      ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ G := by
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G
  have hA : IsOpen A := hG.preimage OnePoint.continuous_coe
  have hAc : IsCompact Aᶜ := ((OnePoint.isOpen_iff_of_mem hinf).mp hG).2
  obtain ⟨R, hR, hbound⟩ := hAc.isBounded.exists_pos_norm_lt
  have hext : {z : ℂ | R ≤ ‖z‖} ⊆ A := by
    intro z hz
    by_contra hzA
    exact (not_lt_of_ge hz) (hbound z hzA)
  have hAn : A.Nonempty := by
    refine ⟨(R : ℂ), hext ?_⟩
    change R ≤ ‖(R : ℂ)‖
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, le_refl]
  have hconnA : IsConnected A := ⟨hAn,
    (finite_part_connected_unbounded hconn.isPreconnected (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1⟩
  obtain ⟨D, hDo, hDc, hDm, hDcl, hDunion, hDexterior⟩ :=
    exists_cofinite_connected_plane_exhaustion hA hconnA hR hext
  let K : ℕ → Set Sphere := fun n => ((↑) : ℂ → Sphere) '' closure (D n) ∪ {OnePoint.infty}
  have hDG (n : ℕ) : ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ G := by
    rintro p (⟨z, hz, rfl⟩ | hp)
    · exact hDcl n (subset_closure hz)
    · exact mem_singleton_iff.mp hp ▸ hinf
  have hDE (n : ℕ) : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D n :=
    hDexterior.trans (hDm (Nat.zero_le n))
  refine ⟨R, D, K, hR, hDo, hDc, hDm, fun _ => rfl, ?_, ?_, ?_, hDexterior, ?_⟩
  · intro n
    refine ⟨(isClosed_finite_set_with_infty isClosed_closure).isCompact, ?_⟩
    rintro p (⟨z, hz, rfl⟩ | hp)
    · exact hDcl n hz
    · exact mem_singleton_iff.mp hp ▸ hinf
  · intro n
    apply interior_maximal ?_ (isOpen_finite_domain_with_infty (hDo n) (hDE n))
    exact union_subset_union_left _ (image_mono subset_closure)
  · apply Subset.antisymm (iUnion_subset hDG)
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact mem_iUnion.mpr ⟨0, Or.inr rfl⟩
    | coe z =>
      have hz : z ∈ A := hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hDunion.symm ▸ hz)
      exact mem_iUnion.mpr ⟨n, Or.inl ⟨z, hn, rfl⟩⟩
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply hext
      change R ≤ ‖z‖
      simpa only [OnePoint.coe_injective.mem_set_image, mem_compl_iff, mem_ball,
        dist_zero_right, not_lt] using hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedCoreNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact connected neighborhoods inside the source

A compact subset of a domain containing infinity lies strictly inside a
compact connected subset of that domain which also contains a neighborhood
of infinity. This lets successive finite Jordan cores retain earlier ones.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem closure_finite_domain_with_infty (D : Set ℂ) :
    closure (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) =
      ((↑) : ℂ → Sphere) '' closure D ∪ {OnePoint.infty} := by
  apply Subset.antisymm
  · exact closure_minimal (union_subset_union_left _ (image_mono subset_closure))
      (isClosed_finite_set_with_infty isClosed_closure)
  · apply union_subset
    · exact (image_closure_subset_closure_image OnePoint.continuous_coe).trans
        (closure_mono subset_union_left)
    · exact subset_union_right.trans subset_closure

theorem isConnected_finite_domain_with_infty
    {D : Set ℂ} (hD : IsConnected D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsConnected (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hunbounded : ¬ Bornology.IsBounded D := by
    intro h
    have hc := (isBounded_closedBall (x := (0 : ℂ)) (r := R)).union h
    apply NormedSpace.unbounded_univ ℝ ℂ
    apply hc.subset
    intro z _
    by_cases hz : ‖z‖ ≤ R
    · exact Or.inl (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
    · exact Or.inr (hext (le_of_lt (lt_of_not_ge hz)))
  have hinf := infty_mem_closure_image_of_unbounded hunbounded
  apply (hD.image _ OnePoint.continuous_coe.continuousOn).subset_closure subset_union_left
  exact union_subset subset_closure (singleton_subset_iff.mpr hinf)

theorem exists_compact_connected_core_neighborhood
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ P : Set Sphere, IsCompact P ∧ IsConnected P ∧ P ⊆ G ∧
      S ⊆ interior P ∧ OnePoint.infty ∈ interior P := by
  obtain ⟨R, D, K, hR, hDo, hDc, hDm, hKdef, hK, hDK, hcover, hext, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  let U : ℕ → Set Sphere := fun n => ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty}
  have hUo (n : ℕ) : IsOpen (U n) :=
    isOpen_finite_domain_with_infty (hDo n) (hext.trans (hDm (Nat.zero_le n)))
  have hUm : Monotone U := fun _ _ h => union_subset_union_left _ (image_mono (hDm h))
  obtain ⟨n, hn⟩ := hS.elim_directed_cover U hUo
    (fun p hp => hcover.symm ▸ hSG hp) hUm.directed_le
  refine ⟨K n, (hK n).1, ?_, (hK n).2, hn.trans (hDK n), hDK n (Or.inr rfl)⟩
  rw [hKdef n, ← closure_finite_domain_with_infty]
  exact (isConnected_finite_domain_with_infty (hDc n)
    (hext.trans (hDm (Nat.zero_le n)))).closure

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
-- module Solutions.Q146_CD.CircleDomains_Topology_PrescribedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite smooth Jordan core retaining a prescribed connected set

Sard, compact one-manifold classification and Schoenflies produce disjoint
smooth filled contours around the complement. Their common exterior stays
in the original domain and retains the prescribed compact set in its interior.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_prescribed_jordan_core
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G P : Set Sphere} (hG : IsOpen G) (hP : IsCompact P) (hPG : P ⊆ G)
    (hconn : IsPreconnected P) (hinf : OnePoint.infty ∈ interior P) :
    ∃ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      closedJordanCore H ⊆ G ∧ P ⊆ interior (closedJordanCore H) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i)) := by
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Gᶜ
  let V : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Pᶜ
  have hinfG : OnePoint.infty ∈ G := hPG (interior_subset hinf)
  have hAc : IsCompact A := isCompact_finite_preimage hG.isClosed_compl
    (by simpa only [mem_compl_iff, not_not] using hinfG)
  have hVo : IsOpen V := hP.isClosed.isOpen_compl.preimage OnePoint.continuous_coe
  have hAV : A ⊆ V := preimage_mono (compl_subset_compl.mpr hPG)
  have hVc : IsPreconnected Vᶜ ∧ ¬ Bornology.IsBounded Vᶜ := by
    simpa only [V, ← preimage_compl, compl_compl] using
      finite_part_connected_unbounded hconn hinf
  obtain ⟨f, t, γ₀, H₀, s, hs, hcover, hdisj, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hAc (Subset.refl A)
      (by simp only [sdiff_self, isClosed_empty]) hVo hAV hVc.1 hVc.2
  let : Fintype s := hs.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let H : Fin (Fintype.card s) → ℂ ≃ₜ ℂ := fun i => H₀ (e.symm i)
  let γ : Fin (Fintype.card s) → Circle → ℂ := fun i => γ₀ (e.symm i)
  have hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hdisj (e.symm i).property (e.symm j).property
      (fun h => hij (e.symm.injective (Subtype.ext h)))
  have hcover' : A ⊆ ⋃ i, jordanInterior (H i) := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hcover hz)
    refine mem_iUnion.mpr ⟨e ⟨j, hj⟩, ?_⟩
    simpa only [H, e.symm_apply_apply] using hzj
  have hinside' (i : Fin (Fintype.card s)) : closure (jordanInterior (H i)) ⊆ V :=
    hinside _ (e.symm i).property
  refine ⟨Fintype.card s, H, γ, hd, ?_, ?_, ?_⟩
  · intro p hp
    by_contra hpG
    cases p using OnePoint.rec with
    | infty => exact hpG hinfG
    | coe z =>
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover' hpG)
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  · rw [interior_closedJordanCore]
    intro p hp hbad
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hbad
    exact hinside' i hz hp
  · intro i
    obtain ⟨hsm, hemb, hfront, _⟩ := hcurves _ (e.symm i).property
    exact ⟨hsm, hemb, hfront⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A strict exhaustion by finite smooth Jordan cores

Every prescribed compact subset is retained in the interior of a finite
Jordan core. Recursive application retains the preceding core and the next
compact exhaustion set. The construction uses Sard, one-manifold
classification, and Schoenflies.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

namespace SmoothJordanCore

variable {G : Set Sphere} (C : SmoothJordanCore G)

theorem regular : closure (interior C.carrier) = C.carrier :=
  closure_interior_closedJordanCore C.disk C.disjoint

theorem connected_interior : IsConnected (interior C.carrier) := by
  rw [carrier, interior_closedJordanCore]
  exact isConnected_openCompletedRegion C.disk C.disjoint

theorem infty_interior : OnePoint.infty ∈ interior C.carrier := by
  rw [carrier, interior_closedJordanCore]
  intro h
  obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
  exact OnePoint.coe_ne_infty z hz

end SmoothJordanCore

theorem exists_smooth_jordan_core_containing
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ C : SmoothJordanCore G, S ⊆ interior C.carrier := by
  obtain ⟨P, hPc, hPconn, hPG, hSP, hinfP⟩ :=
    exists_compact_connected_core_neighborhood hG hconn hinf hS hSG
  obtain ⟨n, H, γ, hd, hKG, hPK, hcurves⟩ :=
    exists_prescribed_jordan_core hsard hschoenflies hG hPc hPG hPconn.isPreconnected hinfP
  let C : SmoothJordanCore G := ⟨n, H, γ, hd, hKG,
    fun i => (hcurves i).1, fun i => (hcurves i).2.1, fun i => (hcurves i).2.2⟩
  exact ⟨C, (hSP.trans interior_subset).trans hPK⟩

theorem exists_smooth_jordan_exhaustion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) :
    ∃ C : ℕ → SmoothJordanCore G,
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G := by
  classical
  obtain ⟨R, D, K, _, _, _, _, _, hK, hDK, hcover, _, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  have hex (S : Set Sphere) (hS : IsCompact S) (hSG : S ⊆ G) :=
    exists_smooth_jordan_core_containing hsard hschoenflies hG hconn hinf hS hSG
  let initial : SmoothJordanCore G := Classical.choose (hex (K 0) (hK 0).1 (hK 0).2)
  have hinitial : K 0 ⊆ interior initial.carrier :=
    Classical.choose_spec (hex (K 0) (hK 0).1 (hK 0).2)
  let next (n : ℕ) (C : SmoothJordanCore G) : SmoothJordanCore G :=
    Classical.choose (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  have hnext (n : ℕ) (C : SmoothJordanCore G) :
      C.carrier ∪ K (n + 1) ⊆ interior (next n C).carrier :=
    Classical.choose_spec (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  let C : ℕ → SmoothJordanCore G := fun n => Nat.rec initial next n
  have hstep (n : ℕ) : C (n + 1) = next n (C n) := rfl
  have hretain (n : ℕ) : K n ⊆ interior (C n).carrier := by
    cases n with
    | zero => exact hinitial
    | succ n => exact subset_union_right.trans (hnext n (C n))
  refine ⟨C, fun n => subset_union_left.trans (hnext n (C n)), ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset fun n => interior_subset.trans (C n).subset
  · intro p hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hp)
    exact mem_iUnion.mpr ⟨n, hretain n (interior_subset (hDK n hn))⟩

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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanIntersectionConnectivity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connectivity on the inside of a retained Jordan boundary

A radial clamp onto a slightly smaller disk fixes any prescribed pair of
interior points and maps the whole domain into its intersection with the
disk. The inner circle stays in the domain by compactness of the retained
boundary. This proves the connectedness needed to track source and image
sides under refinement.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_radialClamp {r : ℝ} (hr : 0 < r) : Continuous (radialClamp r) := by
  apply (continuous_const.div (continuous_const.max continuous_norm) ?_).smul continuous_id
  intro z
  exact ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))

theorem radialClamp_eq_self {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    radialClamp r z = z := by
  simp only [radialClamp, max_eq_left hz, div_self hr.ne', one_smul]

theorem norm_radialClamp_of_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : r ≤ ‖z‖) :
    ‖radialClamp r z‖ = r := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (hr.trans_le hz)
  rw [radialClamp, max_eq_right hz, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr.le (norm_nonneg z)), div_mul_cancel₀ _ hn]

theorem inner_circle_subset_of_retained_boundary
    {W : Set ℂ} (hW : IsOpen W) (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < 1 → 1 - r < δ → sphere (0 : ℂ) r ⊆ W := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_sphere (0 : ℂ) 1).exists_cthickening_subset_open hW hboundary
  refine ⟨δ, hδ, ?_⟩
  intro r hr hr1 hnear z hz
  have hzn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  let w : ℂ := r⁻¹ • z
  have hwn : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hzn,
      inv_mul_cancel₀ hr.ne']
  have hzw : z = r • w := by simp only [w, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  apply hsub
  apply mem_cthickening_of_dist_le z w δ (sphere (0 : ℂ) 1)
    (mem_sphere_zero_iff_norm.mpr hwn)
  calc
    dist z w = ‖(r - 1) • w‖ := by rw [hzw, dist_eq_norm, sub_smul, one_smul]
    _ = 1 - r := by rw [norm_smul, Real.norm_eq_abs, hwn, mul_one, abs_of_neg (sub_neg.mpr hr1)]; ring
    _ ≤ δ := hnear.le

theorem isPreconnected_inter_unitDisk
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    IsPreconnected (W ∩ ball 0 1) := by
  obtain ⟨δ, hδ, hcircle⟩ := inner_circle_subset_of_retained_boundary hW hboundary
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  have hxn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx.2
  have hyn : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy.2
  have hmax : max (max ‖x‖ ‖y‖) (1 - δ) < 1 :=
    max_lt (max_lt hxn hyn) (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_between hmax
  have hxr : ‖x‖ < r := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hyr : ‖y‖ < r := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hr : 0 < r := (norm_nonneg x).trans_lt hxr
  have hnear : 1 - r < δ := by linarith [le_max_right (max ‖x‖ ‖y‖) (1 - δ)]
  have hmap : radialClamp r '' W ⊆ W ∩ ball 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzr : ‖z‖ ≤ r
    · rw [radialClamp_eq_self hr hzr]
      exact ⟨hz, by simpa only [mem_ball, dist_zero_right] using hzr.trans_lt hrhi⟩
    · have he := norm_radialClamp_of_le hr (le_of_lt (lt_of_not_ge hzr))
      exact ⟨hcircle r hr hrhi hnear (mem_sphere_zero_iff_norm.mpr he), by
        simpa only [mem_ball, dist_zero_right, he] using hrhi⟩
  refine ⟨radialClamp r '' W, hmap, ?_, ?_, hconn.image _ (continuous_radialClamp hr).continuousOn⟩
  · exact ⟨x, hx.1, radialClamp_eq_self hr hxr.le⟩
  · exact ⟨y, hy.1, radialClamp_eq_self hr hyr.le⟩

theorem isPreconnected_inter_jordanInterior
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (H : ℂ ≃ₜ ℂ) (hboundary : frontier (jordanInterior H) ⊆ W) :
    IsPreconnected (W ∩ jordanInterior H) := by
  have hpre : IsPreconnected (H ⁻¹' W) := H.isPreconnected_preimage.mpr hconn
  have hbd : sphere (0 : ℂ) 1 ⊆ H ⁻¹' W := by
    intro z hz
    apply hboundary
    rw [frontier_jordanInterior]
    exact mem_image_of_mem _ hz
  have hi := isPreconnected_inter_unitDisk (hW.preimage H.continuous) hpre hbd
  have he : H '' ((H ⁻¹' W) ∩ ball 0 1) = W ∩ jordanInterior H := by
    rw [image_preimage_inter]
    rfl
  exact he ▸ hi.image H H.continuous.continuousOn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanSideCorrespondence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correspondence of the source and image sides of a core boundary

Connectivity of the source on a disk's inside, together with local openness
at its retained boundary, determines which target Jordan disk it maps into.
This tracks the labels of boundary curves without extending the conformal
map across any omitted component.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem isPreconnected_sphere_jordan_intersection
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  let W : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G
  have hW : IsPreconnected W := (finite_part_connected_unbounded hconn
    (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1
  have hi := isPreconnected_inter_jordanInterior (hG.preimage OnePoint.continuous_coe) hW H
    (fun z hz => hboundary (mem_image_of_mem _ hz))
  have he : ((↑) : ℂ → Sphere) '' (W ∩ jordanInterior H) =
      G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) := image_preimage_inter _ _ _
  exact he ▸ hi.image _ OnePoint.continuous_coe.continuousOn

theorem open_image_jordan_side_subset
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (J i) := by
  classical
  let S : Set Sphere := G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))
  let O : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior (J i)
  have hOo : IsOpen O := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (J i))
  have hKclosed : IsClosed (closedJordanCore H) :=
    (isOpen_iUnion fun j => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H j))).isClosed_compl
  have hsrcboundary (j : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j)) ⊆ G := by
    intro q hq
    apply hKG
    have hfq : q ∈ frontier (closedJordanCore H) := by
      rw [frontier_closedJordanCore H hd]
      exact mem_iUnion.mpr ⟨j, hq⟩
    simpa only [hKclosed.closure_eq] using frontier_subset_closure hfq
  have hS : IsPreconnected S :=
    isPreconnected_sphere_jordan_intersection hG hconn.isPreconnected hinf (H i) (hsrcboundary i)
  have hfrontO : frontier O = ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) :=
    frontier_sphere_image_jordanInterior (J i)
  have havoid : Disjoint (f '' S) (frontier O) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ hq
    rw [hfrontO, ← hboundary i] at hq
    obtain ⟨y, hy, he⟩ := hq
    have hyx : y = x := hi (hsrcboundary i hy) hx.1 he
    rw [hyx] at hy
    obtain ⟨z, hz, hez⟩ := hy
    obtain ⟨w, hw, hew⟩ := hx.2
    have hwz : w = z := OnePoint.coe_injective (hew.trans hez.symm)
    exact hz.2 ((jordanInterior_isOpen (H i)).interior_eq.symm ▸ (hwz ▸ hw))
  obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
  let x : Sphere := (z : Sphere)
  have hxfront : x ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := ⟨z, hz, rfl⟩
  let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, closedTerminalCap (H j)
  have hBclosed : IsClosed B := isClosed_iUnion_of_finite fun j =>
    (isCompact_closedTerminalCap (H j)).isClosed
  have hxB : x ∉ B := by
    intro h
    obtain ⟨j, w, hw, he⟩ := mem_iUnion.mp h
    have hwz : w = z := OnePoint.coe_injective he
    exact Set.disjoint_left.mp (hd j.property.symm) (frontier_subset_closure hz) (hwz ▸ hw)
  let N : Set Sphere := G ∩ Bᶜ
  have hN : IsOpen N := hG.inter hBclosed.isOpen_compl
  have hxN : x ∈ N := ⟨hsrcboundary i hxfront, hxB⟩
  have hfN : IsOpen (f '' N) := ho _ hN inter_subset_left
  have hfxfront : f x ∈ frontier O := by
    rw [hfrontO, ← hboundary i]
    exact mem_image_of_mem _ hxfront
  obtain ⟨y, hyN, hyO⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hfxfront)
    (f '' N) (hfN.mem_nhds (mem_image_of_mem _ hxN))
  obtain ⟨w, hwN, rfl⟩ := hyN
  have hwK : w ∉ closedJordanCore H := by
    intro hw
    have htarget : f w ∈ (f '' closedJordanCore H)ᶜ := by
      rw [himage]
      exact mem_iUnion.mpr ⟨i, hyO⟩
    exact htarget (mem_image_of_mem _ hw)
  have hwS : w ∈ S := by
    refine ⟨hwN.1, ?_⟩
    have hwU : w ∈ ⋃ j, ((↑) : ℂ → Sphere) '' jordanInterior (H j) := not_not.mp hwK
    obtain ⟨j, v, hv, he⟩ := mem_iUnion.mp hwU
    by_cases hji : j = i
    · exact hji ▸ ⟨v, hv, he⟩
    · exact (hwN.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, v, subset_closure hv, he⟩)).elim
  have hmeet : (f '' S ∩ O).Nonempty := ⟨f w, mem_image_of_mem _ hwS, hyO⟩
  have hcover : f '' S ⊆ O ∪ (closure O)ᶜ := by
    intro q hq
    by_cases hqo : q ∈ O
    · exact Or.inl hqo
    · right
      intro hqc
      exact Set.disjoint_left.mp havoid hq ⟨hqc, by
        simpa only [hOo.interior_eq] using hqo⟩
  exact (hS.image f (hf.mono inter_subset_left)).subset_left_of_subset_union
    hOo isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ (subset_closure h₁)) hcover hmeet


theorem open_image_jordan_side_eq
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    (hJd : Pairwise (Disjoint on fun i => closure (jordanInterior (J i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsides := open_image_jordan_side_subset H J hd hG hconn hinf hKG hf ho hi hboundary himage
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_image_of_mem _ hx.1, hsides i (mem_image_of_mem _ hx)⟩
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    have hnotK : x ∉ closedJordanCore H := by
      intro hxK
      have hnot : f x ∈ (f '' closedJordanCore H)ᶜ := by
        rw [himage]
        exact mem_iUnion.mpr ⟨i, hy⟩
      exact hnot (mem_image_of_mem _ hxK)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (not_not.mp hnotK)
    have hj' := hsides j (mem_image_of_mem f ⟨hx, hj⟩)
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint_closedTerminalCaps J hJd hne)
        (by obtain ⟨z, hz, he⟩ := hj'; exact ⟨z, subset_closure hz, he⟩)
        (by obtain ⟨z, hz, he⟩ := hy; exact ⟨z, subset_closure hz, he⟩)
    exact ⟨x, ⟨hx, hji ▸ hj⟩, rfl⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedImageCores
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matched source and target Jordan cores

The actual mapped boundary parametrizations identify each target disk's
label. Both inclusions of the corresponding source/target side equality
are proved, so refinement can carry those labels to end components.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_matched_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) (C : SmoothJordanCore G) :
    ∃ J : Fin C.count → ℂ ≃ₜ ℂ,
      Pairwise (Disjoint on fun i => closure (jordanInterior (J i))) ∧
      (f '' C.carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i) ∧
      (∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (C.disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsrcfront : frontier C.carrier = ⋃ i, ((↑) : ℂ → Sphere) '' range (C.curve i) := by
    rw [SmoothJordanCore.carrier, frontier_closedJordanCore C.disk C.disjoint]
    simp only [C.boundary]
  have hcurvesG (i : Fin C.count) (t : Circle) : ((C.curve i t : ℂ) : Sphere) ∈ G := by
    apply C.subset
    have hfront : ((C.curve i t : ℂ) : Sphere) ∈ frontier C.carrier := by
      rw [hsrcfront]
      exact mem_iUnion.mpr ⟨i, C.curve i t, ⟨t, rfl⟩, rfl⟩
    simpa only [C.isCompact.isClosed.closure_eq] using frontier_subset_closure hfront
  obtain ⟨J, hJfront, hJd, hJe⟩ := exists_jordan_image_core_of_continuous_open hschoenflies hG hf ho hi
    C.isCompact C.subset C.regular C.connected_interior.isPreconnected C.infty_interior hfix
    C.curve (fun i => (C.embedding i).continuous) (fun i => (C.embedding i).injective)
    (by
      intro i j hij
      apply (C.disjoint hij).mono
      · rw [← C.boundary i]
        exact frontier_subset_closure
      · rw [← C.boundary j]
        exact frontier_subset_closure) hsrcfront
  have hboundary (i : Fin C.count) :
      f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) := by
    rw [C.boundary i, hJfront i, image_image, ← range_comp, ← range_comp]
    congr 1
    funext t
    exact (CannonMobius.coe_coordinate
      (finite_image_of_fixes_infty hi hinf hfix (hcurvesG i t))).symm
  refine ⟨J, hJd, hJe, hboundary, ?_⟩
  exact open_image_jordan_side_eq C.disk J C.disjoint hJd hG hconn hinf C.subset
    hf ho hi hboundary hJe


theorem exists_matched_jordan_exhaustion_of_continuous_open
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i)))) ∧
      (∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i)) ∧
      (∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i))) ∧
      ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)) := by
  classical
  obtain ⟨C, hs, hc⟩ := exists_smooth_jordan_exhaustion hsard hschoenflies hG hconn hinf
  choose J hd he hb hi' using fun n => exists_matched_image_core_of_continuous_open hschoenflies hG hconn hinf hf ho hi hfix (C n)
  exact ⟨C, J, hs, hc, hd, he, hb, hi'⟩

theorem exists_matched_jordan_exhaustion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i)))) ∧
      (∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i)) ∧
      (∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i))) ∧
      ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)) :=
  exists_matched_jordan_exhaustion_of_continuous_open hsard hschoenflies hG hconn hinf
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi hfix


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
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalPlaneCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite physical chart in the Euclidean coordinates used for smoothing. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

theorem exists_planeSphere_eq {p : Sphere} (hp : p ≠ OnePoint.infty) :
    ∃x : EuclideanPlane, planeSphere x = p := by
  cases p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z =>
    refine ⟨complexPlaneCoordinates.symm z, ?_⟩
    exact congrArg ((↑) : ℂ → Sphere) (complexPlaneCoordinates.apply_symm_apply z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlaneCovectorEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two actual coordinate derivatives control the full covector
energy on the physical plane. No measurability of the covector field
beyond that of the two given derivatives is needed for this bound. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem planeCovector_norm_le (L : EuclideanPlane →L[ℝ] ℝ) :
    ‖L‖ ≤ ‖L (EuclideanSpace.single 0 1)‖ + ‖L (EuclideanSpace.single 1 1)‖ := by
  apply L.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  have hx : x = (x 0) • EuclideanSpace.single 0 1 + (x 1) • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  calc
    ‖L x‖ = ‖(x 0) • L (EuclideanSpace.single 0 1) +
        (x 1) • L (EuclideanSpace.single 1 1)‖ := by
      conv_lhs => rw [hx, map_add, map_smul, map_smul]
    _ ≤ ‖x 0‖ * ‖L (EuclideanSpace.single 0 1)‖ +
        ‖x 1‖ * ‖L (EuclideanSpace.single 1 1)‖ := by
      simpa only [norm_smul] using norm_add_le
        ((x 0) • L (EuclideanSpace.single 0 1)) ((x 1) • L (EuclideanSpace.single 1 1))
    _ ≤ ‖x‖ * ‖L (EuclideanSpace.single 0 1)‖ +
        ‖x‖ * ‖L (EuclideanSpace.single 1 1)‖ := by
      gcongr
      · exact PiLp.norm_apply_le x 0
      · exact PiLp.norm_apply_le x 1
    _ = _ := by ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedConformalEnds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matched Jordan ends for a fixed conformal equivalence, independently
of the finite-model representation used to construct that equivalence. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_matched_conformal_ends
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G) (hc : IsConnected G)
    (hinf : OnePoint.infty ∈ G) {f : Sphere → Sphere}
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) :
    Nonempty (MatchedConformalEnds G f) := by
  obtain ⟨C,J,hs,hc,hd,he,hb,hi⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hc hinf hf.1 hf.bijOn.injOn hfix
  exact ⟨⟨C,J,hs,hc,hd,he,hb,hi⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedComponentCorrespondence
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed correspondence on the full spheres. On the domain it is
the conformal map; over a complementary component its fiber is the
whole matching component. This includes disk-to-point and point-to-disk
matches, where a continuous single-valued extension need not exist. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem componentRelation_closed (hf : IsConformalEquivalence f G (f '' G)) :
    IsClosed {z : Sphere × Sphere | D.componentRelation z.1 z.2} := by
  change IsClosed (⋂ n, D.relationStage n)
  apply isClosed_iInter
  intro n
  apply IsClosed.union
  · apply IsCompact.isClosed
    apply (D.cores n).isCompact.image_of_continuousOn
    exact continuousOn_id.prodMk (fun q hq => (hf.1 q ((D.cores n).subset hq)).1.continuousWithinAt.mono
      (D.cores n).subset)
  · apply isClosed_iUnion_of_finite
    intro i
    exact (isCompact_closedTerminalCap _).isClosed.prod (isCompact_closedTerminalCap _).isClosed

 theorem componentRelation_on_domain {q p : Sphere} (hq : q ∈ G)
    (h : D.componentRelation q p) : p = f q := by
  obtain ⟨n,hn⟩ := mem_iUnion.mp (D.cover.symm ▸ hq)
  rcases (D.relationStage_iff n q p).mp (mem_iInter.mp h n) with hqp | ⟨i,hqi,_⟩
  · exact hqp.2
  · rw [SmoothJordanCore.carrier,interior_closedJordanCore] at hn
    exact (hn (mem_iUnion.mpr ⟨i,hqi⟩)).elim

 theorem componentRelation_target_fiber (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    ∃ q ∈ Gᶜ, {q' | D.componentRelation q' p} = connectedComponentIn Gᶜ q := by
  let E := D.endAt hG hf p hp
  refine ⟨E.source,E.outside,?_⟩
  ext q'
  constructor
  · intro h
    rw [E.source_eq]
    apply mem_iInter.mpr
    intro n
    rcases (D.relationStage_iff n q' p).mp (mem_iInter.mp h n) with hg | ⟨i,hqi,hpi⟩
    · exact (hp ⟨q',(D.cores n).subset hg.1,hg.2.symm⟩).elim
    · have hpb : p ∈ closedTerminalCap (D.disks n (E.address n)) :=
        mem_iInter.mp (E.target_eq ▸ mem_connectedComponentIn hp) n
      have hi : i = E.address n := by
        by_contra hne
        exact Set.disjoint_left.mp (disjoint_closedTerminalCaps _ (D.disjoint n) hne) hpi hpb
      simpa only [hi] using hqi
  · intro h
    apply mem_iInter.mpr
    intro n
    apply (D.relationStage_iff n q' p).mpr
    exact Or.inr ⟨E.address n,mem_iInter.mp (E.source_eq ▸ h) n,
      mem_iInter.mp (E.target_eq ▸ mem_connectedComponentIn hp) n⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentRelationSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual selections from the matched component correspondence. They
agree with the conformal map on the domain, are constant on each omitted
component, and are continuous at every singleton target fiber. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem selectedTarget_mem (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (q : Sphere) : D.componentRelation q (D.selectedTarget hG hf q) :=
  (D.targetFiber_nonempty hG hf q).some_mem

 theorem selectedTarget_on_domain (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    {q : Sphere} (hq : q ∈ G) : D.selectedTarget hG hf q = f q :=
  D.componentRelation_on_domain hq (D.selectedTarget_mem hG hf q)

 theorem componentRelation_source_saturated (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' p : Sphere}
    (hq : q ∈ Gᶜ) (hqq : q' ∈ connectedComponentIn Gᶜ q)
    (hr : D.componentRelation q p) : D.componentRelation q' p := by
  obtain ⟨t,ht,he⟩ := D.componentRelation_source_fiber hG hf hq
  have hp : p ∈ (f '' G)ᶜ := by
    apply connectedComponentIn_subset (f '' G)ᶜ t
    rw [← he]
    exact hr
  obtain ⟨s,hs,hse⟩ := D.componentRelation_target_fiber hG hf hp
  have hqs : q ∈ connectedComponentIn Gᶜ s := by
    rw [← hse]
    exact hr
  have hcc : connectedComponentIn Gᶜ q = connectedComponentIn Gᶜ s :=
    (connectedComponentIn_eq hqs).symm
  change q' ∈ {q' | D.componentRelation q' p}
  rw [hse,← hcc]
  exact hqq

 theorem targetFiber_eq_on_component (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' : Sphere}
    (hq : q ∈ Gᶜ) (hqq : q' ∈ connectedComponentIn Gᶜ q) :
    D.targetFiber q = D.targetFiber q' := by
  have hq' : q' ∈ Gᶜ := connectedComponentIn_subset _ _ hqq
  have hback : q ∈ connectedComponentIn Gᶜ q' := by
    rw [← connectedComponentIn_eq hqq]
    exact mem_connectedComponentIn hq
  ext p
  exact ⟨D.componentRelation_source_saturated hG hf hq hqq,
    D.componentRelation_source_saturated hG hf hq' hback⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CountableMatchedComponents
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional component pairs in the trace argument are countable:
one side has nonempty interior. Common point pairs remain unrestricted. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem IsComplementaryComponent.eq_component_of_mem {G K : Set Sphere}
    (hK : IsComplementaryComponent G K) {q : Sphere} (hq : q ∈ K) :
    K = connectedComponentIn Gᶜ q := by
  obtain ⟨p,_,rfl⟩ := hK
  exact connectedComponentIn_eq hq

 theorem circle_component_euclidean {G K : Set Sphere}
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hK : IsComplementaryComponent G K) :
    ∃ (c : ℂ) (r : ℝ), 0 ≤ r ∧ K = ((↑) : ℂ → Sphere) '' Metric.closedBall c r := by
  obtain ⟨p,hp,rfl⟩ := hK
  rcases hG.2.2 p hp with ⟨q,he⟩ | hround
  · cases q using OnePoint.rec with
    | infty =>
      have hi : OnePoint.infty ∈ connectedComponentIn Gᶜ p := he.symm ▸ mem_singleton _
      exact ((connectedComponentIn_subset _ _ hi) hinf).elim
    | coe z =>
      refine ⟨z,0,le_rfl,?_⟩
      simpa only [Metric.closedBall_zero,image_singleton] using he
  · obtain ⟨c,r,hr,he⟩ := isRoundClosedDisk_eq_euclidean hround
      (fun h => (connectedComponentIn_subset _ _ h) hinf)
    exact ⟨c,r,hr.le,he⟩

 theorem circle_component_singleton_or_interior {G K : Set Sphere}
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hK : IsComplementaryComponent G K) :
    (∃ q, K = {q}) ∨ (interior K).Nonempty := by
  obtain ⟨p,hp,rfl⟩ := hK
  rcases hG.2.2 p hp with hpoint | hround
  · exact Or.inl hpoint
  · have hn : OnePoint.infty ∉ connectedComponentIn Gᶜ p :=
      fun h => (connectedComponentIn_subset _ _ h) hinf
    obtain ⟨c,r,hr,he⟩ := isRoundClosedDisk_eq_euclidean hround hn
    right
    rw [he]
    refine ⟨(c : Sphere),mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset ((OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball).mem_nhds
      (mem_image_of_mem _ (Metric.mem_ball_self hr))) (image_mono Metric.ball_subset_closedBall)

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem IsMatchedComponentPair.fst_injective {P Q : Set Sphere × Set Sphere}
    (hP : D.IsMatchedComponentPair P) (hQ : D.IsMatchedComponentPair Q) (hPQ : P.1 = Q.1) : P = Q := by
  obtain ⟨q,hq⟩ := hP.1.nonempty
  have hq' : q ∈ Q.1 := hPQ ▸ hq
  exact Prod.ext hPQ ((hP.2.2 q hq).symm.trans (hQ.2.2 q hq'))

 theorem equal_target_fibers_equal_source_components (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' : Sphere}
    (hq : q ∈ Gᶜ) (_hq' : q' ∈ Gᶜ) (he : D.targetFiber q = D.targetFiber q') :
    connectedComponentIn Gᶜ q = connectedComponentIn Gᶜ q' := by
  obtain ⟨p,hr⟩ := D.targetFiber_nonempty hG hf q
  obtain ⟨t,ht,hfiber⟩ := D.componentRelation_source_fiber hG hf hq
  have hp : p ∈ (f '' G)ᶜ := by
    apply connectedComponentIn_subset (f '' G)ᶜ t
    rw [← hfiber]
    exact hr
  obtain ⟨s,_,hs⟩ := D.componentRelation_target_fiber hG hf hp
  have hqs : q ∈ connectedComponentIn Gᶜ s := by rw [← hs]; exact hr
  have hq's : q' ∈ connectedComponentIn Gᶜ s := by
    rw [← hs]
    change p ∈ D.targetFiber q'
    rw [← he]
    exact hr
  exact (connectedComponentIn_eq hqs).symm.trans (connectedComponentIn_eq hq's)

 theorem IsMatchedComponentPair.snd_injective (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {P Q : Set Sphere × Set Sphere}
    (hP : D.IsMatchedComponentPair P) (hQ : D.IsMatchedComponentPair Q) (hPQ : P.2 = Q.2) : P = Q := by
  obtain ⟨q,hq⟩ := hP.1.nonempty
  obtain ⟨q',hq'⟩ := hQ.1.nonempty
  have hqG : q ∈ Gᶜ := by
    rw [hP.1.eq_component_of_mem hq] at hq
    exact connectedComponentIn_subset _ _ hq
  have hq'G : q' ∈ Gᶜ := by
    rw [hQ.1.eq_component_of_mem hq'] at hq'
    exact connectedComponentIn_subset _ _ hq'
  have he : D.targetFiber q = D.targetFiber q' :=
    (hP.2.2 q hq).trans (hPQ.trans (hQ.2.2 q' hq').symm)
  apply Prod.ext _ hPQ
  rw [hP.1.eq_component_of_mem hq,hQ.1.eq_component_of_mem hq']
  exact D.equal_target_fibers_equal_source_components hG hf hqG hq'G he

 theorem exists_matched_pair_of_source (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q : Sphere} (hq : q ∈ Gᶜ) :
    ∃ P : Set Sphere × Set Sphere, D.IsMatchedComponentPair P ∧
      P.1 = connectedComponentIn Gᶜ q := by
  obtain ⟨p,hp,he⟩ := D.componentRelation_source_fiber hG hf hq
  refine ⟨(connectedComponentIn Gᶜ q,connectedComponentIn (f '' G)ᶜ p),
    ⟨⟨q,hq,rfl⟩,⟨p,hp,rfl⟩,?_⟩,rfl⟩
  intro q' hq'
  exact (D.targetFiber_eq_on_component hG hf hq hq').symm.trans he

 theorem matched_pair_indexed_or_common_point
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {P : Set Sphere × Set Sphere} (hP : D.IsMatchedComponentPair P) :
    ((interior P.1).Nonempty ∨ (interior P.2).Nonempty) ∨
      ((∃ q, P.1 = {q}) ∧ (∃ p, P.2 = {p})) := by
  rcases circle_component_singleton_or_interior hG hinf hP.1 with hq | hi
  · rcases circle_component_singleton_or_interior hG' hinf' hP.2.1 with hp | hi
    · exact Or.inr ⟨hq,hp⟩
    · exact Or.inl (Or.inr hi)
  · exact Or.inl (Or.inl hi)

 theorem countable_matched_nonpoint_components (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) :
    {P : Set Sphere × Set Sphere | D.IsMatchedComponentPair P ∧
      ((interior P.1).Nonempty ∨ (interior P.2).Nonempty)}.Countable := by
  let A := {P : Set Sphere × Set Sphere | D.IsMatchedComponentPair P ∧ (interior P.1).Nonempty}
  let B := {P : Set Sphere × Set Sphere | D.IsMatchedComponentPair P ∧ (interior P.2).Nonempty}
  have hA : A.Countable :=
    (show MapsTo Prod.fst A {K | IsComplementaryComponent G K ∧ (interior K).Nonempty} from
      fun _ h => ⟨h.1.1,h.2⟩).countable_of_injOn
      (fun _ hP _ hQ he => IsMatchedComponentPair.fst_injective D hP.1 hQ.1 he)
      (countable_complementaryComponents_with_interior G)
  have hB : B.Countable :=
    (show MapsTo Prod.snd B {K | IsComplementaryComponent (f '' G) K ∧ (interior K).Nonempty} from
      fun _ h => ⟨h.1.2.1,h.2⟩).countable_of_injOn
      (fun _ hP _ hQ he => IsMatchedComponentPair.snd_injective D hG hf hP.1 hQ.1 he)
      (countable_complementaryComponents_with_interior (f '' G))
  apply (hA.union hB).mono
  intro P hP
  exact hP.2.elim (fun h => Or.inl ⟨hP.1,h⟩) (fun h => Or.inr ⟨hP.1,h⟩)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedRoundDisks
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual round disk parameters for the countable exceptional matched
component pairs. Both radius-square sums follow from their geometry. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem indexedMatchedPair_countable (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) : Countable D.IndexedMatchedPair :=
  (D.countable_matched_nonpoint_components hG hf).to_subtype

 theorem exists_matched_round_disks (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hG' : IsCircleDomain (f '' G))
    (hinf' : OnePoint.infty ∈ f '' G) : Nonempty D.MatchedRoundDisks := by
  let : Countable D.IndexedMatchedPair := D.indexedMatchedPair_countable hG.1 hf
  choose c r hr he using (fun j : D.IndexedMatchedPair =>
    circle_component_euclidean hG hinf j.property.1.1)
  choose c' s hs he' using (fun j : D.IndexedMatchedPair =>
    circle_component_euclidean hG' hinf' j.property.1.2.1)
  have hd : Pairwise (Disjoint on fun j => closedBall (c j) (r j)) := by
    intro i j hij
    have hne : i.val.1 ≠ j.val.1 := fun h => hij (Subtype.ext
      (IsMatchedComponentPair.fst_injective D i.property.1 j.property.1 h))
    have hdis := i.property.1.1.disjoint_of_ne j.property.1.1 hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    apply Set.disjoint_left.mp hdis
    · rw [he i]
      exact mem_image_of_mem _ hz
    · rw [he j]
      exact mem_image_of_mem _ hz'
  have hd' : Pairwise (Disjoint on fun j => closedBall (c' j) (s j)) := by
    intro i j hij
    have hne : i.val.2 ≠ j.val.2 := fun h => hij (Subtype.ext
      (IsMatchedComponentPair.snd_injective D hG.1 hf i.property.1 j.property.1 h))
    have hdis := i.property.1.2.1.disjoint_of_ne j.property.1.2.1 hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    apply Set.disjoint_left.mp hdis
    · rw [he' i]
      exact mem_image_of_mem _ hz
    · rw [he' j]
      exact mem_image_of_mem _ hz'
  obtain ⟨R,hR,hRb⟩ := ((OnePoint.isOpen_iff_of_mem hinf).mp hG.1).2.isBounded.exists_pos_norm_lt
  obtain ⟨R',hR',hRb'⟩ := ((OnePoint.isOpen_iff_of_mem hinf').mp hG'.1).2.isBounded.exists_pos_norm_lt
  have hcontain (j : D.IndexedMatchedPair) : ball (c j) (r j) ⊆ ball 0 R := by
    intro z hz
    rw [mem_ball,dist_zero_right]
    apply hRb
    have hmem : (z : Sphere) ∈ j.val.1 := by rw [he j]; exact mem_image_of_mem _ (ball_subset_closedBall hz)
    rw [j.property.1.1.eq_component_of_mem hmem] at hmem
    change (z : Sphere) ∈ Gᶜ
    exact connectedComponentIn_subset _ _ hmem
  have hcontain' (j : D.IndexedMatchedPair) : ball (c' j) (s j) ⊆ ball 0 R' := by
    intro z hz
    rw [mem_ball,dist_zero_right]
    apply hRb'
    have hmem : (z : Sphere) ∈ j.val.2 := by rw [he' j]; exact mem_image_of_mem _ (ball_subset_closedBall hz)
    rw [j.property.1.2.1.eq_component_of_mem hmem] at hmem
    change (z : Sphere) ∈ (f '' G)ᶜ
    exact connectedComponentIn_subset _ _ hmem
  exact ⟨⟨c,c',r,s,hr,hs,he,he',hd,hd',
    summable_radii_sq c r R hr (fun i j h => (hd h).mono ball_subset_closedBall ball_subset_closedBall) hcontain,
    summable_radii_sq c' s R' hs (fun i j h => (hd' h).mono ball_subset_closedBall ball_subset_closedBall) hcontain'⟩⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CountableTraceEnumeration
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate a countable family without repetitions. Missing natural
codes carry zero radii, so empty and finite families use the same bounds. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem traceEnumeration_encode {ι E : Type*} [Encodable ι] (v : ι → E) (e : E) (i : ι) :
    traceEnumeration v e (Encodable.encode i) = v i :=
  Encodable.encode_injective.extend_apply v (fun _ => e) i

 theorem traceEnumeration_missing {ι E : Type*} [Encodable ι] (v : ι → E) (e : E)
    {n : ℕ} (hn : n ∉ Set.range (Encodable.encode : ι → ℕ)) : traceEnumeration v e n = e :=
  Function.extend_apply' v (fun _ => e) n hn

 theorem traceEnumeration_map {ι E F : Type*} [Encodable ι] (v : ι → E) (e : E) (g : E → F) :
    (fun n => g (traceEnumeration v e n)) = traceEnumeration (g ∘ v) (g e) := by
  funext n
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨i,rfl⟩ := hn
    simp only [traceEnumeration_encode,comp_apply]
  · rw [traceEnumeration_missing v e hn,traceEnumeration_missing _ _ hn]

 theorem traceEnumeration_nonneg {ι : Type*} [Encodable ι] {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) : ∀ n, 0 ≤ traceEnumeration v 0 n := by
  intro n
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨i,rfl⟩ := hn
    rw [traceEnumeration_encode]
    exact hv i
  · rw [traceEnumeration_missing v 0 hn]

 theorem traceEnumeration_summable_sq {ι : Type*} [Encodable ι] {v : ι → ℝ}
    (hv : Summable (fun i => v i^2)) : Summable (fun n => traceEnumeration v 0 n^2) := by
  rw [traceEnumeration_map v 0 (fun t : ℝ => t^2)]
  simp only [Function.comp_def,zero_pow (by norm_num : (2:ℕ) ≠ 0),traceEnumeration]
  exact (summable_extend_zero Encodable.encode_injective).mpr hv

 theorem traceEnumeration_ball_disjoint {ι : Type*} [Encodable ι]
    {c : ι → ℂ} {r : ι → ℝ}
    (hd : Pairwise (Disjoint on fun i => ball (c i) (r i))) (fallback : ℂ) :
    Pairwise (Disjoint on fun n => ball (traceEnumeration c fallback n) (traceEnumeration r 0 n)) := by
  intro m n hmn
  change Disjoint (ball (traceEnumeration c fallback m) (traceEnumeration r 0 m))
    (ball (traceEnumeration c fallback n) (traceEnumeration r 0 n))
  by_cases hm : m ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨i,rfl⟩ := hm
    rw [traceEnumeration_encode,traceEnumeration_encode]
    by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
    · obtain ⟨j,rfl⟩ := hn
      rw [traceEnumeration_encode,traceEnumeration_encode]
      exact hd (fun hij => hmn (congrArg Encodable.encode hij))
    · rw [traceEnumeration_missing r 0 hn,ball_zero]
      exact disjoint_empty _
  · rw [traceEnumeration_missing r 0 hm,ball_zero]
    exact empty_disjoint _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonPacking
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reserve each zero-radius balloon after removing all later balloons.
The reserved pieces are disjoint even when the balloons overlap. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem reservedBalloon_measurable {B : ℕ → Set ℂ}
    (hB : ∀ j, MeasurableSet (B j)) (j : ℕ) : MeasurableSet (reservedBalloon B j) :=
  (hB j).diff (MeasurableSet.iUnion (fun _ => hB _))

 theorem reservedBalloon_pairwise (B : ℕ → Set ℂ) :
    Pairwise (Disjoint on reservedBalloon B) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact hxi.2 (mem_iUnion.mpr ⟨j-i-1,by convert hxj.1 using 1; congr 1; omega⟩)
  · exact hxj.2 (mem_iUnion.mpr ⟨i-j-1,by convert hxi.1 using 1; congr 1; omega⟩)

 theorem reservedBalloon_area_lower {c : ℕ → ℂ} {d : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (hs : Summable (fun j => d j^2)) (j : ℕ)
    (htail : (∑' k : ℕ, d (k+j+1)^2) ≤ d j^2/2) :
    Real.pi*d j^2/2 ≤ volume.real (reservedBalloon (fun i => ball (c i) (d i)) j) := by
  let U := ⋃ k : ℕ, ball (c (k+j+1)) (d (k+j+1))
  have hsj : Summable (fun k : ℕ => d (k+j+1)^2) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (j+1)).mpr hs
  have hreal : Summable (fun k : ℕ => volume.real (ball (c (k+j+1)) (d (k+j+1)))) :=
    (hsj.mul_left Real.pi).congr (fun k => (real_volume_ball _ (hd _)).symm)
  have hsum : (∑' k : ℕ, volume (ball (c (k+j+1)) (d (k+j+1)))) ≠ ∞ := by
    have hh := hreal.tsum_ofReal_ne_top
    simpa only [measureReal_def,ENNReal.ofReal_toReal measure_ball_lt_top.ne] using hh
  have hUf : volume U ≠ ∞ := ne_of_lt ((measure_iUnion_le _).trans_lt (lt_top_iff_ne_top.mpr hsum))
  have hU : volume.real U ≤ Real.pi*(∑' k : ℕ, d (k+j+1)^2) := by
    have hh := ENNReal.toReal_mono hsum (measure_iUnion_le
      (fun k : ℕ => ball (c (k+j+1)) (d (k+j+1))))
    rw [ENNReal.tsum_toReal_eq (fun _ => measure_ball_lt_top.ne)] at hh
    simpa only [← measureReal_def,real_volume_ball _ (hd _),hsj.tsum_mul_left] using hh
  have hdiff := le_measureReal_sdiff (μ := (volume : Measure ℂ))
    (s₁ := ball (c j) (d j)) (s₂ := U) hUf
  rw [show volume.real (ball (c j) (d j)) = Real.pi*d j^2 from real_volume_ball _ (hd j)] at hdiff
  change Real.pi*d j^2/2 ≤ volume.real (ball (c j) (d j) \ U)
  nlinarith [mul_le_mul_of_nonneg_left htail Real.pi_pos.le]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MonotoneL2Limit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative increasing finite sums with a uniform square-integral
bound have a finite L² limit almost everywhere. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_monotone_L2_limit {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} (hf : ∀ n, Measurable (f n))
    (hf2 : ∀ n, MemLp (f n) 2 μ) (hf0 : ∀ n x, 0 ≤ f n x)
    (hmono : ∀ x, Monotone (fun n => f n x)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, (∫ x, f n x^2 ∂μ) ≤ B) :
    ∃ P : X → ℝ, Measurable P ∧ (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧
      (∫ x, P x^2 ∂μ) ≤ B ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (P x)) ∧ ∀ n, f n x ≤ P x) := by
  let Q := fun x => ⨆ n, ENNReal.ofReal (f n x)
  have hQ : Measurable Q := Measurable.iSup (fun n => (hf n).ennreal_ofReal)
  have ht (x : X) : Tendsto (fun n => ENNReal.ofReal (f n x)) atTop (𝓝 (Q x)) :=
    tendsto_atTop_iSup (fun i j hij => ENNReal.ofReal_le_ofReal (hmono x hij))
  have hi : (∫⁻ x, Q x^2 ∂μ) ≤ ENNReal.ofReal B := by
    have hconv := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
      (fun n => ((hf n).ennreal_ofReal.pow_const 2).aemeasurable)
      (Eventually.of_forall (fun x i j hij => pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hmono x hij)) 2))
      (Eventually.of_forall (fun x => ENNReal.Tendsto.pow (ht x)))
    apply le_of_tendsto hconv
    apply Eventually.of_forall
    intro n
    have he : (∫⁻ x, ENNReal.ofReal (f n x)^2 ∂μ) = ENNReal.ofReal (∫ x, f n x^2 ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hf2 n).integrable_sq
        (Eventually.of_forall (fun x => sq_nonneg (f n x)))]
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_pow (hf0 n x) 2).symm
    rw [he]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfinite : ∀ᵐ x ∂μ, Q x ≠ ∞ := by
    filter_upwards [ae_lt_top (hQ.pow_const 2) (ne_of_lt (hi.trans_lt ENNReal.ofReal_lt_top))] with x hx
    intro he
    simp only [he,ENNReal.top_pow (by norm_num : (2:ℕ) ≠ 0),lt_self_iff_false] at hx
  let P := fun x => (Q x).toReal
  have hP : Measurable P := hQ.ennreal_toReal
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (P x)) ∧ ∀ n, f n x ≤ P x := by
    filter_upwards [hfinite] with x hx
    constructor
    · have h := (ENNReal.continuousAt_toReal hx).tendsto.comp (ht x)
      simpa only [Function.comp_def,ENNReal.toReal_ofReal (hf0 _ _)] using h
    · intro n
      have hle : ENNReal.ofReal (f n x) ≤ Q x := le_iSup (fun n => ENNReal.ofReal (f n x)) n
      simpa only [ENNReal.toReal_ofReal (hf0 _ _)] using ENNReal.toReal_mono hx hle
  have hPint : (∫⁻ x, ENNReal.ofReal (P x^2) ∂μ) ≤ ENNReal.ofReal B := by
    apply le_trans _ hi
    apply lintegral_mono
    intro x
    change ENNReal.ofReal ((Q x).toReal^2) ≤ Q x^2
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2
  have hPi : Integrable (fun x => P x^2) μ :=
    ⟨(hP.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => sq_nonneg (P x)))).mpr
        (hPint.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨P,hP,(fun _ => ENNReal.toReal_nonneg),
    (memLp_two_iff_integrable_sq hP.aestronglyMeasurable).mpr hPi,?_,hlim⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hPi (Eventually.of_forall (fun x => sq_nonneg (P x)))] at hPint
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hPint

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteBallSynthesis
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite ball-synthesis estimate is derived from the published
planar maximal inequality, disjoint payment regions, and Cauchy--Schwarz. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finiteBallDensity_memLp {ι : Type*} (F : Finset ι) (c : ι → ℂ) (d a : ι → ℝ) :
    MemLp (finiteBallDensity F c d a) 2 volume := by
  apply memLp_finsetSum
  intro j _
  exact memLp_indicator_const 2 measurableSet_ball _ (Or.inr measure_ball_lt_top.ne)

 theorem finiteBallDensity_nonneg {ι : Type*} (F : Finset ι) (c : ι → ℂ) {d a : ι → ℝ}
    (ha : ∀ j ∈ F, 0 ≤ a j) (hd : ∀ j ∈ F, 0 ≤ d j) (z : ℂ) :
    0 ≤ finiteBallDensity F c d a z :=
  Finset.sum_nonneg (fun j hj => indicator_nonneg (fun _ _ => div_nonneg (ha j hj) (hd j hj)) z)

 theorem finiteBallDensity_energy_eq {ι : Type*} (F : Finset ι) (c : ι → ℂ) (d a : ι → ℝ) :
    (∫ z, finiteBallDensity F c d a z^2) =
      ∑ j ∈ F, a j/d j*(∫ z in ball (c j) (d j), finiteBallDensity F c d a z) := by
  let S := finiteBallDensity F c d a
  have hS := finiteBallDensity_memLp F c d a
  have hi (j : ι) : Integrable ((ball (c j) (d j)).indicator
      (fun z => (a j/d j)*S z)) volume := by
    have hj := memLp_indicator_const (μ := (volume : Measure ℂ)) 2
      (s := ball (c j) (d j)) measurableSet_ball (a j/d j) (Or.inr measure_ball_lt_top.ne)
    have hh := hj.integrable_mul hS
    change Integrable (fun z => (ball (c j) (d j)).indicator (fun _ => a j/d j) z*S z) volume at hh
    simpa only [← indicator_mul_left] using hh
  have he (z : ℂ) : S z^2 = ∑ j ∈ F, (ball (c j) (d j)).indicator
      (fun z => (a j/d j)*S z) z := by
    calc
      _ = S z*S z := pow_two _
      _ = _ := by conv_lhs => lhs; unfold S finiteBallDensity
                  rw [Finset.sum_mul]
                  simp only [indicator_mul_left]
  change (∫ z, S z^2) = _
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator measurableSet_ball,integral_const_mul]

 theorem finiteBallDensity_filter_ne_zero {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (c : ι → ℂ) (d a : ι → ℝ) :
    finiteBallDensity (F.filter (fun j => a j ≠ 0)) c d a = finiteBallDensity F c d a := by
  classical
  funext z
  simp only [finiteBallDensity,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · rfl
  · have hj : a j = 0 := not_ne_iff.mp h
    simp only [hj,zero_div,indicator_zero]

 theorem exists_finite_ball_synthesis_constant (hmaximal : PlanarMaximalL2) {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι], ∀ (F : Finset ι)
      (c : ι → ℂ) (d a : ι → ℝ) (E : ι → Set ℂ),
      (∀ j ∈ F, 0 < d j) → (∀ j ∈ F, 0 ≤ a j) →
      (∀ j ∈ F, MeasurableSet (E j)) → Set.Pairwise (↑F) (Disjoint on E) →
      (∀ j ∈ F, E j ⊆ ball (c j) (d j)) →
      (∀ j ∈ F, k*d j^2 ≤ volume.real (E j)) →
      (∫ z, finiteBallDensity F c d a z^2) ≤ C*(∑ j ∈ F, a j^2) := by
  obtain ⟨A,hA,hmax⟩ := hmaximal
  let P := (4*Real.pi)^2*Real.pi*A^2
  let C := P/k^2
  have hP : 0 < P := by dsimp [P] <;> positivity
  refine ⟨C,div_pos hP (sq_pos_of_pos hk),?_⟩
  intro ι _ F c d a E hd ha hE hdisj hsub hsize
  let S := finiteBallDensity F c d a
  have hS := finiteBallDensity_memLp F c d a
  have hS0 := finiteBallDensity_nonneg F c ha (fun j hj => (hd j hj).le)
  obtain ⟨m,_,hm0,hm,hmEnergy,hmAvg⟩ := hmax S hS
  let B := ∑ j ∈ F, a j^2
  let Q := ∫ z, S z^2
  let T := ∑ j ∈ F, a j/d j*(∫ z in E j, m z)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQ : 0 ≤ Q := integral_nonneg (fun _ => sq_nonneg _)
  have hp : k*Q ≤ (4*Real.pi)*T := by
    rw [show Q = ∫ z, finiteBallDensity F c d a z^2 from rfl,
      finiteBallDensity_energy_eq,Finset.mul_sum,show T = _ from rfl,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hh := maximal_ball_payment hS hm hm0 hmAvg (hd j hj) hk
      (hE j hj) (hsub j hj) (hsize j hj)
    have hsame : (∫ z in ball (c j) (d j), ‖S z‖) =
        ∫ z in ball (c j) (d j), S z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => Real.norm_of_nonneg (hS0 z))
    rw [hsame] at hh
    first | (convert mul_le_mul_of_nonneg_left hh (div_nonneg (ha j hj) (hd j hj).le) using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left hh (div_nonneg (ha j hj) (hd j hj).le)).trans (le_of_eq (by ring)))
  have hT : T^2 ≤ Real.pi*B*(∫ z, m z^2) :=
    sum_disjoint_ball_payments_sq_le F hd hE hdisj hsub hm hm0
  have hp2 : k^2*Q^2 ≤ (4*Real.pi)^2*T^2 := by
    simpa only [← pow_two,mul_pow] using mul_self_le_mul_self (mul_nonneg hk.le hQ) hp
  have hprod : (k^2*Q)*Q ≤ (P*B)*Q := by
    calc
      _ = k^2*Q^2 := by ring
      _ ≤ (4*Real.pi)^2*T^2 := hp2
      _ ≤ (4*Real.pi)^2*(Real.pi*B*(∫ z, m z^2)) :=
        mul_le_mul_of_nonneg_left hT (sq_nonneg _)
      _ ≤ (4*Real.pi)^2*(Real.pi*B*(A^2*Q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmEnergy
          (mul_nonneg Real.pi_pos.le hB)) (sq_nonneg _)
      _ = (P*B)*Q := by dsimp [P] <;> ring
  by_cases hzero : Q = 0
  · change Q ≤ C*B
    rw [hzero]
    exact mul_nonneg (div_nonneg hP.le (sq_nonneg _)) hB
  · have hQpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hzero)
    have hh : k^2*Q ≤ P*B := (mul_le_mul_iff_left₀ hQpos).mp hprod
    change Q ≤ P/k^2*B
    have hh' : Q ≤ (P*B)/k^2 := (le_div_iff₀ (sq_pos_of_pos hk)).mpr (by nlinarith only [hh])
    simpa only [div_mul_eq_mul_div] using hh'

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountableBallSynthesis
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotone convergence completes ball synthesis for the countable
balloon family. The density is the actual sum of weighted indicators. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_countable_ball_synthesis_constant (hmax : PlanarMaximalL2) {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (d a : ℕ → ℝ) (E : ℕ → Set ℂ),
      (∀ j, 0 < d j) → (∀ j, 0 ≤ a j) → Summable (fun j => a j^2) →
      (∀ j, MeasurableSet (E j)) → Pairwise (Disjoint on E) →
      (∀ j, E j ⊆ ball (c j) (d j)) → (∀ j, a j ≠ 0 → k*d j^2 ≤ volume.real (E j)) →
      MemLp (countableBallDensity c d a) 2 volume ∧
      (∫ z, countableBallDensity c d a z^2) ≤ C*(∑' j, a j^2) ∧
      (∀ᵐ z ∂volume, ∀ n, finiteBallDensity (Finset.range n) c d a z ≤ countableBallDensity c d a z) := by
  obtain ⟨C,hC,hfinite⟩ := exists_finite_ball_synthesis_constant hmax hk
  refine ⟨C,hC,?_⟩
  intro c d a E hd ha ha2 hE hdisj hsub hsize
  let f := fun n => finiteBallDensity (Finset.range n) c d a
  have hf (n : ℕ) : Measurable (f n) := by
    exact Finset.measurable_sum _ (fun j _ => measurable_const.indicator measurableSet_ball)
  have hf0 (n : ℕ) (z : ℂ) : 0 ≤ f n z :=
    finiteBallDensity_nonneg _ c (fun j _ => ha j) (fun j _ => (hd j).le) z
  have hterm (z : ℂ) (j : ℕ) : 0 ≤ (ball (c j) (d j)).indicator (fun _ => a j/d j) z :=
    indicator_nonneg (fun _ _ => div_nonneg (ha j) (hd j).le) z
  have hmono (z : ℂ) : Monotone (fun n => f n z) := by
    intro n m hnm
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm) (fun j _ _ => hterm z j)
  have hB : 0 ≤ C*(∑' j, a j^2) := mul_nonneg hC.le (tsum_nonneg (fun j => sq_nonneg (a j)))
  have hbound (n : ℕ) : (∫ z, f n z^2) ≤ C*(∑' j, a j^2) := by
    classical
    let F := (Finset.range n).filter (fun j => a j ≠ 0)
    have he : f n = finiteBallDensity F c d a :=
      (finiteBallDensity_filter_ne_zero (Finset.range n) c d a).symm
    rw [he]
    exact (hfinite F c d a E (fun j _ => hd j) (fun j _ => ha j)
      (fun j _ => hE j) (fun i _ j _ hij => hdisj hij) (fun j _ => hsub j)
      (fun j hj => hsize j (Finset.mem_filter.mp hj).2)).trans
      (mul_le_mul_of_nonneg_left (ha2.sum_le_tsum _ (fun j _ => sq_nonneg (a j))) hC.le)
  obtain ⟨P,_,_,hP,henergy,hlim⟩ := exists_monotone_L2_limit hf
    (fun n => finiteBallDensity_memLp (Finset.range n) c d a) hf0 hmono hB hbound
  have heq : countableBallDensity c d a =ᵐ[volume] P := by
    filter_upwards [hlim] with z hz
    have hs : HasSum (fun j => (ball (c j) (d j)).indicator (fun _ => a j/d j) z) (P z) :=
      (hasSum_iff_tendsto_nat_of_nonneg (hterm z) (P z)).mpr hz.1
    exact hs.tsum_eq
  refine ⟨hP.ae_eq heq.symm,?_,?_⟩
  · exact (integral_congr_ae (heq.mono (fun _ h => congrArg (fun t : ℝ => t^2) h))).trans_le henergy
  · filter_upwards [heq,hlim] with z hz hl
    rw [hz]
    exact hl.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual trace balloon density is square integrable. Positive
source disks pay for one sublist; reserved pieces pay for the zero-radius
sublist. The two sublists may overlap each other. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem exists_trace_balloon_density (hmax : PlanarMaximalL2)
    (c : ℕ → ℂ) (r d a : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hd : ∀ j, 0 < d j) (ha : ∀ j, 0 ≤ a j)
    (hrd : ∀ j, r j ≤ d j) (hdr : ∀ j, 0 < r j → d j ≤ 2*r j)
    (hdisj : Pairwise (Disjoint on fun j => ball (c j) (r j)))
    (ha2 : Summable (fun j => a j^2)) (hd2 : Summable (fun j => d j^2))
    (htail : ∀ j, r j = 0 →
      (∑' k : ℕ, (if r (k+j+1) = 0 then d (k+j+1) else 0)^2) ≤ d j^2/2) :
    ∃ P : ℂ → ℝ, Measurable P ∧ (∀ z, 0 ≤ P z) ∧ MemLp P 2 volume ∧
      ∀ᵐ z ∂volume, ∀ n, finiteBallDensity (Finset.range n) c d a z ≤ P z := by
  let ap := fun j => if 0 < r j then a j else 0
  let az := fun j => if 0 < r j then 0 else a j
  let dz := fun j => if r j = 0 then d j else 0
  let Ep := fun j => ball (c j) (r j)
  let Ez := reservedBalloon (fun j => ball (c j) (dz j))
  have hap (j : ℕ) : 0 ≤ ap j := by dsimp [ap]; split_ifs; exact ha j; exact le_rfl
  have haz (j : ℕ) : 0 ≤ az j := by dsimp [az]; split_ifs; exact le_rfl; exact ha j
  have hdzn (j : ℕ) : 0 ≤ dz j := by dsimp [dz]; split_ifs; exact (hd j).le; exact le_rfl
  have hdz2 : Summable (fun j => dz j^2) := by
    apply hd2.of_nonneg_of_le (fun _ => sq_nonneg _)
    intro j
    dsimp only [dz]
    split_ifs <;> simp [sq_nonneg]
  have hap2 : Summable (fun j => ap j^2) := by
    apply ha2.of_nonneg_of_le (fun _ => sq_nonneg _)
    intro j
    dsimp only [ap]
    split_ifs <;> simp [sq_nonneg]
  have haz2 : Summable (fun j => az j^2) := by
    apply ha2.of_nonneg_of_le (fun _ => sq_nonneg _)
    intro j
    dsimp only [az]
    split_ifs <;> simp [sq_nonneg]
  obtain ⟨C,_,hC⟩ := exists_countable_ball_synthesis_constant hmax
    (show 0 < Real.pi/4 by positivity)
  have hpsize (j : ℕ) (hj : ap j ≠ 0) : Real.pi/4*d j^2 ≤ volume.real (Ep j) := by
    have hrp : 0 < r j := by
      by_contra h
      exact hj (by simp [ap,h])
    have hs : d j^2 ≤ (2*r j)^2 := pow_le_pow_left₀ (hd j).le (hdr j hrp) 2
    change Real.pi/4*d j^2 ≤ volume.real (ball (c j) (r j))
    rw [show volume.real (ball (c j) (r j)) = Real.pi*r j^2 from real_volume_ball _ (hr j)]
    nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_pos.le]
  have hezsub (j : ℕ) : Ez j ⊆ ball (c j) (d j) := by
    intro z hz
    exact (ball_subset_ball (by dsimp only [dz]; split_ifs; exact le_rfl; exact (hd j).le : dz j ≤ d j)) hz.1
  have hzsize (j : ℕ) (hj : az j ≠ 0) : Real.pi/4*d j^2 ≤ volume.real (Ez j) := by
    have hrz : r j = 0 := by
      have hn : ¬0 < r j := by intro h; exact hj (by simp [az,h])
      exact le_antisymm (le_of_not_gt hn) (hr j)
    have hb := reservedBalloon_area_lower (c := c) hdzn hdz2 j (by
      simpa only [dz,hrz,ite_true, if_true] using htail j hrz)
    have he : dz j = d j := by simp [dz,hrz]
    rw [he] at hb
    change Real.pi/4*d j^2 ≤ volume.real (reservedBalloon (fun i => ball (c i) (dz i)) j)
    nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg (d j))]
  obtain ⟨hP,_,hPbound⟩ := hC c d ap Ep hd hap hap2 (fun _ => measurableSet_ball)
    hdisj (fun j => ball_subset_ball (hrd j)) hpsize
  obtain ⟨hZ,_,hZbound⟩ := hC c d az Ez hd haz haz2
    (reservedBalloon_measurable (fun _ => measurableSet_ball))
    (reservedBalloon_pairwise _) hezsub hzsize
  let S := fun z => countableBallDensity c d ap z+countableBallDensity c d az z
  have hS : MemLp S 2 volume := hP.add hZ
  have hS0 (z : ℂ) : 0 ≤ S z := by
    apply add_nonneg <;> apply tsum_nonneg <;> intro j
    · exact indicator_nonneg (fun _ _ => div_nonneg (hap j) (hd j).le) z
    · exact indicator_nonneg (fun _ _ => div_nonneg (haz j) (hd j).le) z
  let P := fun z => max (hS.aestronglyMeasurable.mk S z) 0
  have hPeq : P =ᵐ[volume] S := by
    filter_upwards [hS.aestronglyMeasurable.ae_eq_mk] with z hz
    change max (hS.aestronglyMeasurable.mk S z) 0 = S z
    rw [← hz,max_eq_left (hS0 z)]
  refine ⟨P,hS.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const,
    (fun _ => le_max_right _ _),hS.ae_eq hPeq.symm,?_⟩
  filter_upwards [hPeq,hPbound,hZbound] with z hz hp hz'
  intro n
  rw [hz]
  have he : finiteBallDensity (Finset.range n) c d a z =
      finiteBallDensity (Finset.range n) c d ap z+finiteBallDensity (Finset.range n) c d az z := by
    simp only [finiteBallDensity,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [ap,az]
    split_ifs <;> simp
  rw [he]
  exact add_le_add (hp n) (hz' n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonRadii
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit shrinking balloon radii. The geometric extra radii reserve
at least half of every zero-radius balloon after all later deletions. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem traceExtraRadius_pos (j : ℕ) : 0 < traceExtraRadius j := by
  exact pow_pos (by norm_num) j

 theorem traceExtraRadius_sq (j : ℕ) : traceExtraRadius j^2 = (1/4:ℝ)^j := by
  dsimp only [traceExtraRadius]
  rw [← pow_mul,Nat.mul_comm,pow_mul]
  norm_num

 theorem traceExtraRadius_summable_sq : Summable (fun j => traceExtraRadius j^2) := by
  simp_rw [traceExtraRadius_sq]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

 theorem traceExtraRadius_tail (j : ℕ) :
    (∑' k : ℕ, traceExtraRadius (k+j+1)^2) = traceExtraRadius j^2/3 := by
  simp_rw [traceExtraRadius_sq,show ∀ k : ℕ, (1/4:ℝ)^(k+j+1) = (1/4)^k*((1/4)^j/4) by
    intro k; rw [pow_add,pow_succ]; ring]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)]
  ring

 theorem traceBalloonRadius_pos {r : ℕ → ℝ} (m j : ℕ) :
    0 < traceBalloonRadius r m j := by
  dsimp only [traceBalloonRadius]
  split_ifs with h
  · exact mul_pos (by positivity) h
  · exact div_pos (traceExtraRadius_pos j) (by positivity)

 theorem traceBalloonRadius_lt {r : ℕ → ℝ} (hr : ∀ j, 0 ≤ r j) (m j : ℕ) :
    r j < traceBalloonRadius r m j := by
  dsimp only [traceBalloonRadius]
  split_ifs with h
  · have : 0 < (1/((m:ℝ)+1))*r j := mul_pos (by positivity) h
    nlinarith
  · have hr0 : r j = 0 := le_antisymm (le_of_not_gt h) (hr j)
    rw [hr0]
    exact div_pos (traceExtraRadius_pos j) (by positivity)

 theorem traceBalloonRadius_le_double {r : ℕ → ℝ} (m j : ℕ) (hr : 0 < r j) :
    traceBalloonRadius r m j ≤ 2*r j := by
  dsimp only [traceBalloonRadius]
  rw [ite_eq_left hr]
  have hi : 1/((m:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  nlinarith

 theorem traceBalloonRadius_summable_sq {r : ℕ → ℝ}
    (hr : Summable (fun j => r j^2)) (m : ℕ) :
    Summable (fun j => traceBalloonRadius r m j^2) := by
  apply ((hr.mul_left 4).add traceExtraRadius_summable_sq).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro j
  by_cases hj : 0 < r j
  · have h := traceBalloonRadius_le_double m j hj
    have hs := pow_le_pow_left₀ (traceBalloonRadius_pos m j).le h 2
    nlinarith [sq_nonneg (traceExtraRadius j)]
  · have hi : traceBalloonRadius r m j ≤ traceExtraRadius j := by
      simp only [traceBalloonRadius,ite_eq_right hj]
      exact (div_le_self (traceExtraRadius_pos j).le (by
        have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith))
    have hs := pow_le_pow_left₀ (traceBalloonRadius_pos m j).le hi 2
    nlinarith [sq_nonneg (r j)]

 theorem traceBalloonRadius_tendsto {r : ℕ → ℝ} (hr : ∀ j, 0 ≤ r j) (j : ℕ) :
    Tendsto (fun m => traceBalloonRadius r m j) atTop (𝓝 (r j)) := by
  by_cases hj : 0 < r j
  · have h := ((tendsto_const_nhds (x := (1:ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const (r j)
    simpa only [traceBalloonRadius,ite_eq_left hj,add_zero,one_mul] using h
  · have hr0 : r j = 0 := le_antisymm (le_of_not_gt hj) (hr j)
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (traceExtraRadius j)
    simpa only [traceBalloonRadius,hr0,lt_self_iff_false,ite_false, if_false,div_eq_mul_inv,one_div,one_mul,mul_zero] using h

 theorem traceBalloonRadius_zero_tail {r : ℕ → ℝ} (m j : ℕ) (hrj : r j = 0) :
    (∑' k : ℕ, (if r (k+j+1) = 0 then traceBalloonRadius r m (k+j+1) else 0)^2) ≤
      traceBalloonRadius r m j^2/2 := by
  have hs0 : Summable (fun k : ℕ => traceExtraRadius (k+j+1)^2) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (j+1)).mpr traceExtraRadius_summable_sq
  have hs : Summable (fun k : ℕ => traceExtraRadius (k+j+1)^2/((m:ℝ)+1)^2) := hs0.div_const _
  have hp (k : ℕ) : (if r (k+j+1) = 0 then traceBalloonRadius r m (k+j+1) else 0)^2 ≤
      traceExtraRadius (k+j+1)^2/((m:ℝ)+1)^2 := by
    split_ifs with h
    · simp only [traceBalloonRadius,h,lt_self_iff_false,ite_false, if_false,div_pow,le_refl]
    · simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      positivity
  have hleft : Summable (fun k : ℕ =>
      (if r (k+j+1) = 0 then traceBalloonRadius r m (k+j+1) else 0)^2) :=
    hs.of_nonneg_of_le (fun _ => sq_nonneg _) hp
  apply (hleft.tsum_le_tsum hp hs).trans
  rw [tsum_div_const,traceExtraRadius_tail]
  simp only [traceBalloonRadius,hrj,lt_self_iff_false,ite_false, if_false,div_pow]
  have hnon : 0 ≤ traceExtraRadius j^2/((m:ℝ)+1)^2 := by positivity
  have he : traceExtraRadius j^2/3/((m:ℝ)+1)^2 =
      (traceExtraRadius j^2/((m:ℝ)+1)^2)/3 := by ring
  rw [he]
  nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedScalarIntervals
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual intervals for the matched disks. Their lengths are square
summable and their centers represent values of the closed correspondence.
Unused natural codes are harmless shrinking intervals at one fixed fiber. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}

 theorem MatchedRoundDisks.source_center_mem (E : D.MatchedRoundDisks) (j : D.IndexedMatchedPair) :
    (E.sourceCenter j : Sphere) ∈ j.val.1 := by
  rw [E.source_eq]
  exact mem_image_of_mem _ (mem_closedBall_self (E.source_nonneg j))

 theorem MatchedRoundDisks.target_center_mem (E : D.MatchedRoundDisks) (j : D.IndexedMatchedPair) :
    (E.targetCenter j : Sphere) ∈ j.val.2 := by
  rw [E.target_eq]
  exact mem_image_of_mem _ (mem_closedBall_self (E.target_nonneg j))

 theorem MatchedRoundDisks.centers_related (E : D.MatchedRoundDisks) (j : D.IndexedMatchedPair) :
    D.componentRelation (E.sourceCenter j : Sphere) (E.targetCenter j : Sphere) := by
  change (E.targetCenter j : Sphere) ∈ D.targetFiber (E.sourceCenter j : Sphere)
  rw [j.property.1.2.2 _ (E.source_center_mem j)]
  exact E.target_center_mem j

 theorem MatchedRoundDisks.scalar_fiber_bound (E : D.MatchedRoundDisks)
    {φ : Sphere → ℝ} {L : ℝ≥0} (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (j : D.IndexedMatchedPair) {q p : Sphere} (hq : q ∈ j.val.1)
    (hp : D.componentRelation q p) : |φ p-φ (E.targetCenter j : Sphere)| ≤ L*E.targetRadius j := by
  have hp' : p ∈ j.val.2 := by
    rw [← j.property.1.2.2 q hq]
    exact hp
  rw [E.target_eq] at hp'
  obtain ⟨z,hz,rfl⟩ := hp'
  exact (hL.dist_le_mul z (E.targetCenter j)).trans
    (mul_le_mul_of_nonneg_left hz L.coe_nonneg)

variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.traceWidth_pos (E : D.MatchedRoundDisks) (L : ℝ≥0) (n : ℕ) :
    0 < E.traceWidth L n :=
  add_pos_of_nonneg_of_pos (mul_nonneg L.coe_nonneg
    (traceEnumeration_nonneg E.target_nonneg n)) (traceExtraRadius_pos n)

 theorem MatchedRoundDisks.traceWidth_summable_sq (E : D.MatchedRoundDisks) (L : ℝ≥0) :
    Summable (fun n => E.traceWidth L n^2) := by
  have hs := (traceEnumeration_summable_sq E.target_summable).mul_left (2*(L:ℝ)^2)
  apply (hs.add (traceExtraRadius_summable_sq.mul_left 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro n
  dsimp only [traceWidth,traceTargetRadius]
  nlinarith [sq_nonneg ((L:ℝ)*traceEnumeration E.targetRadius 0 n-traceExtraRadius n)]

 theorem MatchedRoundDisks.traceWidth_tendsto (E : D.MatchedRoundDisks) (L : ℝ≥0) :
    Tendsto (E.traceWidth L) atTop (𝓝 0) :=
  nonnegative_square_summable_tendsto_zero (fun n => (E.traceWidth_pos L n).le)
    (E.traceWidth_summable_sq L)

 theorem MatchedRoundDisks.traceInterval_length (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ)
    (L : ℝ≥0) (n : ℕ) :
    volume.real (E.traceInterval hG hf φ L n) = 2*E.traceWidth L n := by
  rw [traceInterval,Real.volume_real_Ioo_of_le (by linarith [E.traceWidth_pos L n])]
  ring

 theorem MatchedRoundDisks.traceInterval_summable_sq (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ) (L : ℝ≥0) :
    Summable (fun n => volume.real (E.traceInterval hG hf φ L n)^2) := by
  simpa only [E.traceInterval_length,mul_pow,show (2:ℝ)^2=4 by norm_num] using
    (E.traceWidth_summable_sq L).mul_left 4

 theorem MatchedRoundDisks.traceInterval_represents (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ)
    (L : ℝ≥0) (n : ℕ) (t : ℝ) (ht : t ∈ E.traceInterval hG hf φ L n) :
    ∃ p : Sphere, D.componentRelation (E.traceCenter n : Sphere) p ∧
      |t-φ p| ≤ E.traceWidth L n := by
  have ht' : |t-E.traceScalarCenter hG hf φ n| ≤ E.traceWidth L n := by
    apply abs_le.mpr
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  by_cases hn : n ∈ Set.range (Encodable.encode : D.IndexedMatchedPair → ℕ)
  · obtain ⟨j,rfl⟩ := hn
    refine ⟨(E.targetCenter j : Sphere),?_,?_⟩
    · simpa only [traceCenter,traceEnumeration_encode] using E.centers_related j
    · simpa only [traceScalarCenter,traceEnumeration_encode] using ht'
  · refine ⟨D.selectedTarget hG hf (0 : ℂ),?_,?_⟩
    · simpa only [traceCenter,traceEnumeration_missing _ _ hn] using
        D.selectedTarget_mem hG hf (0 : ℂ)
    · simpa only [traceScalarCenter,traceEnumeration_missing _ _ hn] using ht'

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneComponentRelation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed matched correspondence in the finite source chart. Every
point has a singleton fiber or belongs to one of the actual indexed disks. -/
open Set Function Filter Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem planeRelation_closed (hf : IsConformalEquivalence f G (f '' G)) :
    IsClosed {p : ℂ × Sphere | D.planeRelation p.1 p.2} :=
  (D.componentRelation_closed hf).preimage
    ((OnePoint.continuous_coe.comp continuous_fst).prodMk continuous_snd)

 theorem plane_fiber_singleton_or_indexed
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (z : ℂ) :
    (∀ p, D.planeRelation z p → p = D.selectedTarget hG.1 hf (z : Sphere)) ∨
      ∃ j : D.IndexedMatchedPair, (z : Sphere) ∈ j.val.1 := by
  by_cases hz : (z : Sphere) ∈ G
  · left
    intro p hp
    exact (D.componentRelation_on_domain hz hp).trans (D.selectedTarget_on_domain hG.1 hf hz).symm
  · obtain ⟨P,hP,hPe⟩ := D.exists_matched_pair_of_source hG.1 hf hz
    have hzP : (z : Sphere) ∈ P.1 := by rw [hPe]; exact mem_connectedComponentIn hz
    rcases D.matched_pair_indexed_or_common_point hG hinf hG' hinf' hP with hi | ⟨_,hp⟩
    · exact Or.inr ⟨⟨P,hP,hi⟩,hzP⟩
    · left
      obtain ⟨p,hp⟩ := hp
      have he : D.targetFiber (z : Sphere) = {p} := (hP.2.2 _ hzP).trans hp
      intro t ht
      have ht' : t = p := mem_singleton_iff.mp (he ▸ ht)
      have hs : D.selectedTarget hG.1 hf (z : Sphere) = p :=
        mem_singleton_iff.mp (he ▸ D.selectedTarget_mem hG.1 hf (z : Sphere))
      exact ht'.trans hs.symm

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedMaskSupport
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A target scalar that vanishes near infinity gives a compact source
mask, with anchor zero. This uses the actual closed end correspondence. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem scalar_zero_near_infty (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {φ : Sphere → ℝ} (hφ : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), φ p = 0) :
    ∀ᶠ q in 𝓝 (OnePoint.infty : Sphere), φ (D.selectedTarget hG hf q) = 0 := by
  obtain ⟨Z,hZsub,hZopen,hZinf⟩ := mem_nhds_iff.mp hφ
  obtain ⟨V,hV,hVinf,hrel⟩ := closed_relation_neighborhood (D.componentRelation_closed hf) hZopen
    (K := {OnePoint.infty}) (by
      intro q hq p hp
      have hq' : q = OnePoint.infty := mem_singleton_iff.mp hq
      subst q
      have he : p = OnePoint.infty := (D.componentRelation_on_domain hinf hp).trans hfix
      exact he.symm ▸ hZinf)
  filter_upwards [hV.mem_nhds (hVinf (mem_singleton _))] with q hq
  exact hZsub (hrel q hq _ (D.selectedTarget_mem hG hf q))

 theorem mask_compactSupport (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {φ : Sphere → ℝ} (hφ : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), φ p = 0)
    (cutoff : ℕ → ℂ → ℝ) (I : ℕ → Set ℝ) :
    HasCompactSupport (fun z => infiniteTracePrimitive cutoff I 0 z
      (φ (D.selectedTarget hG hf (z : Sphere)))) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have hz := OnePoint.tendsto_coe_infty.eventually (D.scalar_zero_near_infty hG hinf hf hfix hφ)
  filter_upwards [hz] with z hz
  simp only [hz,infiniteTracePrimitive,intervalIntegral.integral_same,Pi.zero_apply]

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CorrespondenceMaskPlateau
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the open plateau, raw interval membership and continuity in
one neighborhood. These are the exact data needed by Sobolev gluing. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem correspondence_mask_plateau_neighborhood
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    {s : X → Y} (hs : ∀ q, R q (s q)) {φ : Y → ℝ} (hφ : Continuous φ)
    {cutoff : ℕ → X → ℝ} (hc : ∀ j q, cutoff j q ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) (c : ℕ → X) {d ε : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hout : ∀ j q, d j ≤ dist q (c j) → cutoff j q = 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ⊤)
    (hrep : ∀ j t, t ∈ I j → ∃ p, R (c j) p ∧ |t-φ p| ≤ ε j)
    {K Z : Set X} (hK : IsCompact K) (hZ : IsOpen Z) (hKZ : K ⊆ Z)
    {j : ℕ} (hzero : ∀ q ∈ Z, cutoff j q = 0)
    {A B η β : ℝ} (hη : 0 < η) (hIj : I j = Ioo A B) (hβ : β ∈ I j)
    (hmargin : ∀ q ∈ K, ∀ p, R q p → φ p ∈ Ioo (A+η) (B-η)) (a : ℝ) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧
      ContinuousOn (fun q => infiniteTracePrimitive cutoff I a q (φ (s q))) V ∧
      ∀ q ∈ V, cutoff j q = 0 ∧ φ (s q) ∈ I j := by
  obtain ⟨N,V,hV,hKV,hcont,_⟩ := correspondence_mask_indexed_neighborhood hR hs hφ hc hcc c
    hd hε hout hI hIf hrep hK hZ hKZ hzero hη hIj hβ hmargin a
  obtain ⟨W,hW,hKW,hraw⟩ := closed_relation_neighborhood hR ((isOpen_Ioo : IsOpen (Ioo A B)).preimage hφ) (by
    intro q hq p hp
    have h := hmargin q hq p hp
    exact ⟨by linarith [h.1],by linarith [h.2]⟩)
  refine ⟨V ∩ Z ∩ W,(hV.inter hZ).inter hW,
    (fun q hq => ⟨⟨hKV hq,hKZ hq⟩,hKW hq⟩),hcont.mono (fun _ h => h.1.1),?_⟩
  intro q hq
  refine ⟨hzero q hq.1.2,?_⟩
  rw [hIj]
  exact hraw q hq.2 _ (hs q)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScaledCutoffEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dirichlet energy of a smooth planar cutoff is unchanged by dilation.
This supplies the fixed energy budget for disjoint concentric transition
annuli used to make cutoffs of arbitrarily small energy. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem dilatedCutoff_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    ContDiff ℝ ∞ (dilatedCutoff f r) := hf.comp (contDiff_id.const_smul _)

 theorem dilatedCutoff_fderiv {f : ℂ → ℝ} (hf : Differentiable ℝ f) (r : ℝ) (z : ℂ) :
    fderiv ℝ (dilatedCutoff f r) z = r⁻¹ • fderiv ℝ f (r⁻¹ • z) := by
  have hd := (hf (r⁻¹ • z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul r⁻¹)
  change fderiv ℝ (f ∘ fun w : ℂ => r⁻¹ • w) z = _
  rw [hd.fderiv]
  ext w
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CenteredSmallCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-energy smooth cutoffs centered at each actual omitted source
point, with their support inside a prescribed ball. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem translatedCutoff_fderiv {f : ℂ → ℝ} (hf : Differentiable ℝ f) (c z : ℂ) :
    fderiv ℝ (translatedCutoff f c) z = fderiv ℝ f (z-c) := by
  have hd := (hf (z-c)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
  change fderiv ℝ (fun w : ℂ => f (w-c)) z = _
  simpa only [id_eq, Function.comp_def, ContinuousLinearMap.comp_id] using hd.fderiv

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonCutoff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth radial balloon cutoffs with one scale-independent derivative
constant for each fixed inner-radius ratio. Their derivatives vanish
outside the open outer balloon, not just outside its closure. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem exists_trace_balloon_cutoffs {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℂ, ∀ d : ℝ, 0 < d →
      ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧
        (∀ z, f z ∈ Icc (0:ℝ) 1) ∧
        (∀ z, ‖z-c‖ ≤ α*d → f z = 0) ∧
        (∀ z, d ≤ ‖z-c‖ → f z = 1) ∧
        (∀ z, ‖fderiv ℝ f z‖ ≤ (ball c d).indicator (fun _ => C/d) z) := by
  let β := (α+1)/2
  have hαβ : α < β := by dsimp [β] <;> linarith
  have hβ1 : β < 1 := by dsimp [β] <;> linarith
  let ψ : ContDiffBump (0 : ℂ) := ⟨α,β,hα,hαβ⟩
  have hψ : ContDiff ℝ ∞ (ψ : ℂ → ℝ) := ψ.contDiff
  have hdψ : Continuous (fderiv ℝ (ψ : ℂ → ℝ)) :=
    (hψ.fderiv_right (m := (↑(⊤ : ℕ∞))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  obtain ⟨D,hD⟩ := hdψ.norm.bounded_above_of_compact_support
    ((ψ.hasCompactSupport.fderiv (𝕜 := ℝ)).norm)
  let C := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hDbound (z : ℂ) : ‖fderiv ℝ (ψ : ℂ → ℝ) z‖ ≤ C := by
    have hh : ‖fderiv ℝ (ψ : ℂ → ℝ) z‖ ≤ D := by simpa only [norm_norm] using hD z
    exact hh.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro c d hd
  let φ := translatedCutoff (dilatedCutoff ψ d) c
  let f := fun z => 1-φ z
  have hφ : ContDiff ℝ ∞ φ :=
    (dilatedCutoff_smooth hψ d).comp (contDiff_id.sub contDiff_const)
  have he (z : ℂ) : φ z = ψ (d⁻¹ • (z-c)) := rfl
  have hder (z : ℂ) : fderiv ℝ f z = -(d⁻¹ • fderiv ℝ (ψ : ℂ → ℝ) (d⁻¹ • (z-c))) := by
    rw [show f = (fun z => 1-φ z) from rfl,fderiv_const_sub,
      translatedCutoff_fderiv ((dilatedCutoff_smooth hψ d).differentiable (by simp)),
      dilatedCutoff_fderiv (hψ.differentiable (by simp))]
  have hn (z : ℂ) : ‖d⁻¹ • (z-c)‖ = ‖z-c‖/d := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]
    ring
  refine ⟨f,contDiff_const.sub hφ,?_,?_,?_,?_⟩
  · intro z
    change 1-φ z ∈ Icc (0:ℝ) 1
    rw [he]
    exact ⟨sub_nonneg.mpr ψ.le_one,sub_le_self _ ψ.nonneg⟩
  · intro z hz
    have hx : d⁻¹ • (z-c) ∈ closedBall (0 : ℂ) ψ.rIn := by
      rw [mem_closedBall,dist_zero_right,hn]
      exact (div_le_iff₀ hd).mpr hz
    change 1-φ z = 0
    rw [he,ψ.one_of_mem_closedBall hx,sub_self]
  · intro z hz
    have hx : ψ.rOut ≤ dist (d⁻¹ • (z-c)) (0 : ℂ) := by
      rw [dist_zero_right,hn]
      exact hβ1.le.trans ((one_le_div hd).mpr hz)
    change 1-φ z = 1
    rw [he,ψ.zero_of_le_dist hx,sub_zero]
  · intro z
    by_cases hz : z ∈ ball c d
    · rw [indicator_of_mem hz _,hder,norm_neg,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hd)]
      simpa only [div_eq_mul_inv,mul_comm] using
        mul_le_mul_of_nonneg_left (hDbound (d⁻¹ • (z-c))) (inv_nonneg.mpr hd.le)
    · have hdist : d ≤ ‖z-c‖ := by simpa only [mem_ball,dist_eq_norm,not_lt] using hz
      have hzero : fderiv ℝ (ψ : ℂ → ℝ) (d⁻¹ • (z-c)) = 0 := by
        by_contra hne
        have hx := support_fderiv_subset ℝ hne
        rw [ψ.tsupport_eq,mem_closedBall,dist_zero_right,hn] at hx
        have hl : 1 ≤ ‖z-c‖/d := (one_le_div hd).mpr hdist
        exact (not_le_of_gt hβ1) (hl.trans hx)
      rw [indicator_of_notMem hz _,hder,hzero,smul_zero,neg_zero,norm_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonSystem
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct each complete balloon system: shrinking radii, a smooth
cutoff around every closed component, and one square-integrable density
paying all finite sums of the cutoff derivatives. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem traceBalloonInnerRatio_bounds (m : ℕ) :
    0 < traceBalloonInnerRatio m ∧ traceBalloonInnerRatio m < 1 := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  constructor
  · exact div_pos (by positivity) (by positivity)
  · apply (div_lt_one (by positivity)).mpr
    linarith

 theorem traceBalloonRadius_inner {r : ℕ → ℝ} (hr : ∀ j, 0 ≤ r j) (m j : ℕ) :
    r j < traceBalloonInnerRatio m*traceBalloonRadius r m j := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hj : 0 < r j
  · simp only [traceBalloonRadius,ite_eq_left hj,traceBalloonInnerRatio]
    have he : (2*(m:ℝ)+3)/(2*(m:ℝ)+4)*(1+1/((m:ℝ)+1))*r j =
        r j+(r j)/(2*((m:ℝ)+1)) := by field_simp <;> ring
    rw [← mul_assoc,he]
    exact lt_add_of_pos_right _ (div_pos hj (by positivity))
  · have hz : r j = 0 := le_antisymm (le_of_not_gt hj) (hr j)
    rw [hz]
    exact mul_pos (traceBalloonInnerRatio_bounds m).1 (traceBalloonRadius_pos m j)

 theorem exists_trace_balloon_system (hmax : PlanarMaximalL2)
    (c : ℕ → ℂ) (r a : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (ha : ∀ j, 0 ≤ a j)
    (hdisj : Pairwise (Disjoint on fun j => ball (c j) (r j)))
    (hr2 : Summable (fun j => r j^2)) (ha2 : Summable (fun j => a j^2)) (m : ℕ) :
    ∃ (C : ℝ) (cutoff : ℕ → ℂ → ℝ) (P : ℂ → ℝ), 0 < C ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (cutoff j)) ∧ (∀ j z, cutoff j z ∈ Icc (0:ℝ) 1) ∧
      (∀ j z, ‖z-c j‖ ≤ traceBalloonInnerRatio m*traceBalloonRadius r m j → cutoff j z = 0) ∧
      (∀ j z, traceBalloonRadius r m j ≤ ‖z-c j‖ → cutoff j z = 1) ∧
      (∀ j z, ‖fderiv ℝ (cutoff j) z‖ ≤
        (ball (c j) (traceBalloonRadius r m j)).indicator (fun _ => C/traceBalloonRadius r m j) z) ∧
      Measurable P ∧ (∀ z, 0 ≤ P z) ∧ MemLp P 2 volume ∧
      (∀ᵐ z ∂volume, ∀ n, (∑ j ∈ Finset.range n, a j*‖fderiv ℝ (cutoff j) z‖) ≤ P z) := by
  obtain ⟨C,hC,hcut⟩ := exists_trace_balloon_cutoffs
    (traceBalloonInnerRatio_bounds m).1 (traceBalloonInnerRatio_bounds m).2
  choose cutoff hs hu hz ho hg using (fun j => hcut (c j) (traceBalloonRadius r m j) (traceBalloonRadius_pos m j))
  obtain ⟨P,hPm,hP0,hP2,hPb⟩ := exists_trace_balloon_density hmax c r
    (traceBalloonRadius r m) a hr (fun j => traceBalloonRadius_pos m j) ha
    (fun j => (traceBalloonRadius_lt hr m j).le) (fun j => traceBalloonRadius_le_double m j)
    hdisj ha2 (traceBalloonRadius_summable_sq hr2 m) (fun j => traceBalloonRadius_zero_tail m j)
  refine ⟨C,cutoff,(fun z => C*P z),hC,hs,hu,hz,ho,hg,
    measurable_const.mul hPm,(fun z => mul_nonneg hC.le (hP0 z)),hP2.const_mul C,?_⟩
  filter_upwards [hPb] with z hzb
  intro n
  calc
    _ ≤ ∑ j ∈ Finset.range n, a j*(ball (c j) (traceBalloonRadius r m j)).indicator
        (fun _ => C/traceBalloonRadius r m j) z :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hg j z) (ha j))
    _ = C*finiteBallDensity (Finset.range n) c (traceBalloonRadius r m) a z := by
      rw [finiteBallDensity,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : z ∈ ball (c j) (traceBalloonRadius r m j)
      · simp only [indicator_of_mem h]
        ring
      · simp only [indicator_of_notMem h,mul_zero]
    _ ≤ C*P z := mul_le_mul_of_nonneg_left (hzb n) hC.le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedMaskContinuity
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and open zero-cutoff neighborhoods of the actual matched
component mask. Point-to-disk pairs are handled by their whole source fiber. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.mask_indexed_neighborhood (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    {φ : Sphere → ℝ} (hφ : Continuous φ) {L : ℝ≥0}
    (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (m : ℕ) {cutoff : ℕ → ℂ → ℝ} (hc : ∀ n z, cutoff n z ∈ Icc (0:ℝ) 1)
    (hcc : ∀ n, Continuous (cutoff n))
    (hzero : ∀ n z, ‖z-E.traceCenter n‖ ≤
      traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n → cutoff n z = 0)
    (hout : ∀ n z, traceBalloonRadius E.traceRadius m n ≤ ‖z-E.traceCenter n‖ → cutoff n z = 1)
    (a : ℝ) (j : D.IndexedMatchedPair) :
    ∃ V : Set ℂ, IsOpen V ∧ closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ V ∧
      ContinuousOn (fun z => infiniteTracePrimitive cutoff (E.traceInterval hG hf φ L) a z
        (φ (D.selectedTarget hG hf (z : Sphere)))) V ∧
      ∀ z ∈ V, cutoff (Encodable.encode j) z = 0 ∧
        φ (D.selectedTarget hG hf (z : Sphere)) ∈ E.traceInterval hG hf φ L (Encodable.encode j) := by
  let n := Encodable.encode j
  let K := closedBall (E.sourceCenter j) (E.sourceRadius j)
  let Z := ball (E.sourceCenter j)
    (traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n)
  have hrad : E.sourceRadius j < traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n := by
    simpa only [n,traceRadius,traceEnumeration_encode] using
      traceBalloonRadius_inner (traceEnumeration_nonneg E.source_nonneg) m n
  have hKZ : K ⊆ Z := fun z hz => lt_of_le_of_lt hz hrad
  have hwidth : E.traceWidth L n = L*E.targetRadius j+traceExtraRadius n := by
    simp only [traceWidth,traceTargetRadius,n,traceEnumeration_encode]
  have hcenter : E.traceScalarCenter hG hf φ n = φ (E.targetCenter j : Sphere) := by
    simp only [traceScalarCenter,n,traceEnumeration_encode]
  apply correspondence_mask_plateau_neighborhood (D.planeRelation_closed hf)
    (fun z => D.selectedTarget_mem hG hf (z : Sphere)) hφ hc hcc E.traceCenter
    (nonnegative_square_summable_tendsto_zero (fun k => (traceBalloonRadius_pos m k).le)
      (traceBalloonRadius_summable_sq (traceEnumeration_summable_sq E.source_summable) m))
    (E.traceWidth_tendsto L) (by simpa only [dist_eq_norm,traceRadius] using hout)
    (fun _ => measurableSet_Ioo) (fun _ => by simp)
    (E.traceInterval_represents hG hf φ L) (isCompact_closedBall _ _) isOpen_ball hKZ
    (j := n) (by
      intro z hz
      apply hzero
      have hz' : ‖z-E.sourceCenter j‖ < traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n := by simpa only [mem_ball,dist_eq_norm] using hz
      simpa only [traceCenter,n,traceEnumeration_encode] using hz'.le)
    (η := traceExtraRadius n/2) (half_pos (traceExtraRadius_pos n)) rfl
    (β := E.traceScalarCenter hG hf φ n) (by
      exact ⟨sub_lt_self _ (E.traceWidth_pos L n),lt_add_of_pos_right _ (E.traceWidth_pos L n)⟩)
    (by
      intro z hz p hp
      have hz' : (z : Sphere) ∈ j.val.1 := by
        rw [E.source_eq]
        exact mem_image_of_mem _ hz
      have h := abs_le.mp (E.scalar_fiber_bound hL j hz' hp)
      rw [hcenter,hwidth]
      constructor <;> linarith [h.1,h.2,traceExtraRadius_pos n]) a

 theorem MatchedRoundDisks.mask_continuous (E : D.MatchedRoundDisks)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {φ : Sphere → ℝ} (hφ : Continuous φ) {L : ℝ≥0}
    (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (m : ℕ) {cutoff : ℕ → ℂ → ℝ} (hc : ∀ n z, cutoff n z ∈ Icc (0:ℝ) 1)
    (hcc : ∀ n, Continuous (cutoff n))
    (hzero : ∀ n z, ‖z-E.traceCenter n‖ ≤
      traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n → cutoff n z = 0)
    (hout : ∀ n z, traceBalloonRadius E.traceRadius m n ≤ ‖z-E.traceCenter n‖ → cutoff n z = 1)
    (a : ℝ) : Continuous (fun z => infiniteTracePrimitive cutoff (E.traceInterval hG.1 hf φ L) a z
      (φ (D.selectedTarget hG.1 hf (z : Sphere)))) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rcases D.plane_fiber_singleton_or_indexed hG hinf hf hG' hinf' z with hs | ⟨j,hj⟩
  · exact correspondence_mask_continuousAt_singleton (D.planeRelation_closed hf)
      (fun z => D.selectedTarget_mem hG.1 hf (z : Sphere)) hφ hc hcc E.traceCenter
      (nonnegative_square_summable_tendsto_zero (fun k => (traceBalloonRadius_pos m k).le)
        (traceBalloonRadius_summable_sq (traceEnumeration_summable_sq E.source_summable) m))
      (E.traceWidth_tendsto L) (by simpa only [dist_eq_norm,traceRadius] using hout)
      (fun _ => measurableSet_Ioo) (fun _ => by simp)
      (E.traceInterval_represents hG.1 hf φ L) hs a
  · obtain ⟨V,hV,hKV,hcont,_⟩ := E.mask_indexed_neighborhood hG.1 hf hφ hL m hc hcc hzero hout a j
    have hz : z ∈ V := by
      apply hKV
      rw [E.source_eq,OnePoint.coe_injective.mem_set_image] at hj
      exact hj
    exact hcont.continuousAt (hV.mem_nhds hz)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedResidualDust
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covering the indexed pairs removes every non-point component. The
remaining closed set is removable dust on the original boundary. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem unindexed_components_singleton
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {q : Sphere} (hq : q ∈ Gᶜ) (hnot : ∀ j : D.IndexedMatchedPair, q ∉ j.val.1) :
    connectedComponentIn Gᶜ q = {q} ∧ ∃ p, D.targetFiber q = {p} := by
  obtain ⟨P,hP,hPe⟩ := D.exists_matched_pair_of_source hG.1 hf hq
  have hqP : q ∈ P.1 := by rw [hPe]; exact mem_connectedComponentIn hq
  rcases D.matched_pair_indexed_or_common_point hG hinf hG' hinf' hP with hi | ⟨hs,ht⟩
  · exact (hnot ⟨P,hP,hi⟩ hqP).elim
  · obtain ⟨x,hx⟩ := hs
    obtain ⟨p,hp⟩ := ht
    have hqx : q = x := mem_singleton_iff.mp (hx ▸ hqP)
    refine ⟨hPe.symm.trans (hx.trans (congrArg singleton hqx.symm)),p,?_⟩
    exact (hP.2.2 q hqP).trans hp

 theorem indexed_cover_residual_dust
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {O : Set Sphere} (hO : IsOpen O) (hGO : G ⊆ O)
    (hcover : ∀ j : D.IndexedMatchedPair, j.val.1 ⊆ O) :
    IsCompact Oᶜ ∧ IsTotallyDisconnected Oᶜ ∧ Oᶜ ⊆ frontier G ∧
      ∀ q ∈ Oᶜ, connectedComponentIn Gᶜ q = {q} ∧ ∃ p, D.targetFiber q = {p} := by
  have hsingle (q : Sphere) (hq : q ∈ Oᶜ) :=
    D.unindexed_components_singleton hG hinf hf hG' hinf'
      (fun h => hq (hGO h)) (fun j hj => hq (hcover j hj))
  refine ⟨hO.isClosed_compl.isCompact,?_,?_,hsingle⟩
  · intro S hS hSc x hx y hy
    have hycc := hSc.subset_connectedComponentIn hx
      (fun z hz hzg => hS hz (hGO hzg)) hy
    change y ∈ connectedComponentIn Gᶜ x at hycc
    rw [(hsingle x (hS hx)).1,mem_singleton_iff] at hycc
    exact hycc.symm
  · intro q hq
    have hproper : Gᶜ ≠ univ := by
      intro he
      have hi : OnePoint.infty ∈ Gᶜ := he.symm ▸ mem_univ _
      exact hi hinf
    obtain ⟨p,hp,hpf⟩ := component_meets_frontier hG.1.isClosed_compl hproper
      (show q ∈ Gᶜ from fun h => hq (hGO h))
    have hpq : p = q := mem_singleton_iff.mp ((hsingle q hq).1 ▸ hp)
    simpa only [frontier_compl,hpq] using hpf

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedIndexedNeighborhood
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrink each indexed plateau to its connected open component. It
still contains the whole disk and meets the original domain. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}

 theorem MatchedRoundDisks.connected_neighborhood (E : D.MatchedRoundDisks)
    (j : D.IndexedMatchedPair) {V : Set ℂ} (hV : IsOpen V)
    (hKV : closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ V) :
    ∃ W : Set ℂ, IsOpen W ∧ IsConnected W ∧ W ⊆ V ∧
      closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ W ∧
      (W ∩ {z : ℂ | (z : Sphere) ∈ G}).Nonempty := by
  let K := closedBall (E.sourceCenter j) (E.sourceRadius j)
  let W := connectedComponentIn V (E.sourceCenter j)
  have hcK : E.sourceCenter j ∈ K := mem_closedBall_self (E.source_nonneg j)
  have hcV : E.sourceCenter j ∈ V := hKV hcK
  have hKW : K ⊆ W := (isConnected_closedBall (E.source_nonneg j)).isPreconnected.subset_connectedComponentIn hcK hKV
  have hWopen : IsOpen W := hV.connectedComponentIn
  have hWconn : IsConnected W := isConnected_connectedComponentIn_iff.mpr hcV
  refine ⟨W,hWopen,hWconn,connectedComponentIn_subset _ _,hKW,?_⟩
  by_contra hnone
  have havoid : ((↑) : ℂ → Sphere) '' W ⊆ Gᶜ := by
    rintro _ ⟨z,hz,rfl⟩ hzg
    exact hnone ⟨z,hz,hzg⟩
  have hcim : (E.sourceCenter j : Sphere) ∈ ((↑) : ℂ → Sphere) '' W :=
    mem_image_of_mem _ (mem_connectedComponentIn hcV)
  have him := (hWconn.isPreconnected.image _ OnePoint.continuous_coe.continuousOn).subset_connectedComponentIn hcim havoid
  have hceq : connectedComponentIn Gᶜ (E.sourceCenter j : Sphere) = j.val.1 :=
    (j.property.1.1.eq_component_of_mem (E.source_center_mem j)).symm
  have hWK : W ⊆ K := by
    intro z hz
    have h := him (mem_image_of_mem _ hz)
    rw [hceq,E.source_eq,OnePoint.coe_injective.mem_set_image] at h
    exact h
  have he : K = W := Subset.antisymm hKW hWK
  have hKopen : IsOpen K := he ▸ hWopen
  exact (isCompact_closedBall (E.sourceCenter j) (E.sourceRadius j)).ne_univ
    ((show IsClopen K from ⟨isClosed_closedBall,hKopen⟩).eq_univ ⟨_,hcK⟩)

 theorem connected_indexed_union {ι : Type*} (hG : IsConnected G)
    (hinf : OnePoint.infty ∈ G) {W : ι → Set ℂ}
    (hW : ∀ j, IsConnected (W j))
    (hmeet : ∀ j, (W j ∩ {z : ℂ | (z : Sphere) ∈ G}).Nonempty) :
    IsConnected (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j) := by
  let O := G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j
  refine ⟨⟨OnePoint.infty,Or.inl hinf⟩,isPreconnected_of_forall OnePoint.infty ?_⟩
  intro y hy
  rcases hy with hy | hy
  · exact ⟨G,subset_union_left,hinf,hy,hG.isPreconnected⟩
  · obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    have him := (hW j).image _ OnePoint.continuous_coe.continuousOn
    have hmeet : (G ∩ ((↑) : ℂ → Sphere) '' W j).Nonempty := by
      obtain ⟨z,hz,hzg⟩ := hmeet j
      exact ⟨(z : Sphere),hzg,mem_image_of_mem _ hz⟩
    refine ⟨G ∪ ((↑) : ℂ → Sphere) '' W j,?_,Or.inl hinf,Or.inr hj,(hG.union hmeet him).isPreconnected⟩
    exact union_subset subset_union_left (fun z hz => Or.inr (mem_iUnion.mpr ⟨j,hz⟩))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedMaskDomain
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The open domain of the actual mask is connected, and its residual
complement is removable dust on the original circle-domain boundary. -/
open Set Function Filter Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.exists_mask_domain (E : D.MatchedRoundDisks)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G))
    {φ : Sphere → ℝ} (hφ : Continuous φ) {L : ℝ≥0}
    (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (m : ℕ) {cutoff : ℕ → ℂ → ℝ} (hc : ∀ n z, cutoff n z ∈ Icc (0:ℝ) 1)
    (hcc : ∀ n, Continuous (cutoff n))
    (hzero : ∀ n z, ‖z-E.traceCenter n‖ ≤
      traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n → cutoff n z = 0)
    (hout : ∀ n z, traceBalloonRadius E.traceRadius m n ≤ ‖z-E.traceCenter n‖ → cutoff n z = 1) :
    ∃ W : D.IndexedMatchedPair → Set ℂ,
      (∀ j, IsOpen (W j)) ∧
      (∀ j, closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ W j) ∧
      (∀ j z, z ∈ W j → cutoff (Encodable.encode j) z = 0 ∧
        φ (D.selectedTarget hG.1 hf (z : Sphere)) ∈ E.traceInterval hG.1 hf φ L (Encodable.encode j)) ∧
      IsOpen (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j) ∧
      IsConnected (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j) ∧
      IsTotallyDisconnected (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j)ᶜ ∧
      IsConformallyRemovable (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j)ᶜ := by
  have hlocal (j : D.IndexedMatchedPair) : ∃ W : Set ℂ,
      IsOpen W ∧ IsConnected W ∧ closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ W ∧
      (W ∩ {z : ℂ | (z : Sphere) ∈ G}).Nonempty ∧
      ∀ z ∈ W, cutoff (Encodable.encode j) z = 0 ∧
        φ (D.selectedTarget hG.1 hf (z : Sphere)) ∈ E.traceInterval hG.1 hf φ L (Encodable.encode j) := by
    obtain ⟨V,hV,hKV,_,hv⟩ := E.mask_indexed_neighborhood hG.1 hf hφ hL m hc hcc hzero hout 0 j
    obtain ⟨W,hW,hWc,hWV,hKW,hm⟩ := E.connected_neighborhood j hV hKV
    exact ⟨W,hW,hWc,hKW,hm,fun z hz => hv z (hWV hz)⟩
  choose W hW hWc hKW hm hp using hlocal
  let O := G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j
  have hO : IsOpen O := hG.1.union (isOpen_iUnion (fun j => OnePoint.isOpen_image_coe.mpr (hW j)))
  have hcover (j : D.IndexedMatchedPair) : j.val.1 ⊆ O := by
    rw [E.source_eq]
    rintro _ ⟨z,hz,rfl⟩
    exact Or.inr (mem_iUnion.mpr ⟨j,mem_image_of_mem _ (hKW j hz)⟩)
  have hdust := D.indexed_cover_residual_dust hG hinf hf hG' hinf' hO subset_union_left hcover
  exact ⟨W,hW,hKW,hp,hO,connected_indexed_union hG.2.1 hinf hWc hm,hdust.2.1,
    hrem.of_isCompact_subset hdust.1 hdust.2.2.1⟩

end MatchedConformalEnds
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

 theorem conductivity_system_iff {k aX aY vX vY : ℝ} (hk : 0 ≤ k) :
    planarDbar aX aY vX vY = ((k - 1) / (k + 1) : ℝ) • star (planarDz aX aY vX vY) ↔
      aX = k * vY ∧ aY = -k * vX := by
  have hd : k + 1 ≠ 0 := by linarith
  have dzr (a b c d : ℝ) : (planarDz a b c d).re = (a + d) / 2 := by
    simp [planarDz]
  have dzi (a b c d : ℝ) : (planarDz a b c d).im = (c - b) / 2 := by
    simp [planarDz]
  have dbr (a b c d : ℝ) : (planarDbar a b c d).re = (a - d) / 2 := by
    simp [planarDbar]
  have dbi (a b c d : ℝ) : (planarDbar a b c d).im = (c + b) / 2 := by
    simp [planarDbar]
  have sr (q : ℝ) (z : ℂ) : (q • star z).re = q * z.re := by
    simp only [Complex.smul_re, Complex.star_def, Complex.conj_re, smul_eq_mul]
  have si (q : ℝ) (z : ℂ) : (q • star z).im = -(q * z.im) := by
    simp only [Complex.smul_im, Complex.star_def, Complex.conj_im, smul_eq_mul, mul_neg]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    rw [dbr, sr, dzr] at hr
    rw [dbi, si, dzi] at hi
    field_simp at hr hi
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    apply Complex.ext
    · rw [dbr, sr, dzr]
      field_simp
    · rw [dbi, si, dzi]
      field_simp
      ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-valued conductivity coefficient. Its strict contraction
constant is (n-1)/(n+1), and the constructed density vanishes off F. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem conductivityRatio_lt_one (n : ℕ) (hn : 1 ≤ n) : conductivityRatio n hn < 1 := by
  change ((n : ℝ) - 1) / ((n : ℝ) + 1) < 1
  apply (div_lt_one (by positivity)).mpr
  linarith

 theorem conductivityCoefficient_memLp {F : Set EuclideanPlane} (hF : IsCompact F) (n : ℕ) :
    MemLp (conductivityCoefficient F n) 2 volume :=
  memLp_indicator_const 2 hF.measurableSet _ (Or.inr hF.measure_lt_top.ne)

 theorem conductivityCoefficient_bound (F : Set EuclideanPlane) (n : ℕ) (hn : 1 ≤ n) :
    ∀ x, ‖conductivityCoefficient F n x‖ ≤ conductivityRatio n hn := by
  intro x
  by_cases hx : x ∈ F
  · simp only [conductivityCoefficient, indicator_of_mem hx, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (conductivityRatio n hn).2)
  · simp only [conductivityCoefficient, indicator_of_notMem hx, norm_zero]
    exact (conductivityRatio n hn).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalRealBeltrami
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise classical real-coefficient principal Beltrami input.

Published source: Clop and Cruz, *Weighted estimates for Beltrami
equations*, Ann. Acad. Sci. Fenn. Math. 38 (2013), 91–113,
DOI 10.5186/aasfm.2013.3818, section 4, opening paragraph, p. 107.
Their theorem states existence of a principal W^{1,2}_loc plane homeomorphism
for compactly supported measurable coefficients mu, nu with
|mu|+|nu| bounded by k<1. We use only mu=0 and real nu=q.

No height, energy inequality, extremality, circle model, or limiting
assertion is included in this input. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem conductivityCoefficient_ratio (F : Set EuclideanPlane) (n : ℕ) (x : EuclideanPlane) :
    conductivityCoefficient F n x =
      (conductivityValue F n x - 1) / (conductivityValue F n x + 1) := by
  classical
  by_cases hx : x ∈ F <;> simp [conductivityCoefficient, conductivityValue, hx]

 theorem exists_principal_conductivity_coordinate (hprincipal : PrincipalRealBeltrami)
    {F : Set EuclideanPlane} (hF : IsCompact F) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z - z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0 := by
  obtain ⟨φ, D, ht, he⟩ := hprincipal (conductivityCoefficient F n)
    (conductivityCoefficient_memLp hF n).aestronglyMeasurable
    ⟨F, hF, fun x hx => indicator_of_notMem hx _⟩
    (conductivityRatio n hn) (conductivityRatio_lt_one n hn)
    (Eventually.of_forall (conductivityCoefficient_bound F n hn))
  refine ⟨φ, D, ht, ?_⟩
  filter_upwards [he] with x hx
  have hk : 0 ≤ conductivityValue F n x := by
    classical
    unfold conductivityValue
    split <;> positivity
  apply (conductivity_system_iff hk).mp
  rwa [conductivityCoefficient_ratio] at hx

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

 theorem principal_bigO_of_exterior_holomorphic {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  let u := invertedPrincipalRemainder F
  have hu : AnalyticAt ℂ u 0 := invertedPrincipalRemainder_analytic hF ht
  have hu0 : u 0 = 0 := Function.update_self _ _ _
  let v := dslope u 0
  have hv : AnalyticAt ℂ v 0 := analyticAt_dslope_zero hu
  have hb : (fun z : ℂ => v z⁻¹) =O[cobounded ℂ] (fun _ => (1 : ℂ)) := by
    simpa only [Function.comp_def] using
      (hv.continuousAt.isBigO (F := ℂ)).comp_tendsto (tendsto_inv₀_cobounded (α := ℂ))
  have hp := (isBigO_refl (fun z : ℂ => z⁻¹) (cobounded ℂ)).mul hb
  apply hp.congr'
  · have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
      rw [Metric.cobounded_eq_cocompact]
      exact (isCompact_singleton.compl_mem_cocompact : {0}ᶜ ∈ cocompact ℂ)
    filter_upwards [hn] with z hz
    have hh := sub_smul_dslope u 0 z⁻¹
    simp only [sub_zero, smul_eq_mul] at hh
    change z⁻¹ * v z⁻¹ = u z⁻¹ - u 0 at hh
    rw [hu0, sub_zero] at hh
    simpa only [u, invertedPrincipalRemainder,
      Function.update_of_ne (inv_ne_zero hz), inv_inv] using hh
  · exact Eventually.of_forall (fun z => mul_one z⁻¹)

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

 theorem exists_principal_conductivity_holomorphic (hprincipal : PrincipalRealBeltrami)
    {F : Set EuclideanPlane} (hF : IsCompact F) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z-z) (cobounded ℂ) (𝓝 0) ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) ∧
      DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ ∧
      (fun z => φ z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  obtain ⟨φ, D, ht, hsys⟩ := exists_principal_conductivity_coordinate hprincipal hF n hn
  have hh := D.conductivity_holomorphic_off φ.continuous hF.isClosed n hsys
  have hclosed := (hF.image complexPlaneCoordinates.continuous).isClosed
  have hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ φ z := by
    have hmem : ∀ᶠ z in cobounded ℂ, z ∈ (complexPlaneCoordinates '' F)ᶜ := by
      rw [Metric.cobounded_eq_cocompact]
      exact (hF.image complexPlaneCoordinates.continuous).compl_mem_cocompact
    exact hmem.mono fun z hz => hh.differentiableAt (hclosed.isOpen_compl.mem_nhds hz)
  exact ⟨φ, D, ht, hsys, hh, principal_bigO_of_exterior_holomorphic hd ht⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HolomorphicHomeomorph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A holomorphic plane homeomorphism has a holomorphic inverse on the
image domain. Isolated critical points are removed from the continuous
inverse; the chain rule then excludes them altogether. -/
open Set Filter Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphicHomeomorph_deriv_not_locally_zero
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : ¬ ∀ᶠ w in 𝓝 z, deriv φ w = 0 := by
  intro hzero
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp ((show ∀ᶠ w in 𝓝 z, w ∈ U from hU.mem_nhds hz).and hzero)
  have hsub : ball z r ⊆ U := fun w hw => (hball (by simpa only [mem_ball] using hw)).1
  obtain ⟨c, hc⟩ := isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball z r).isPreconnected (hφ.mono hsub)
    (fun w hw => (hball (by simpa only [mem_ball] using hw)).2)
  let w : ℂ := z + (r/2 : ℝ)
  have hw : w ∈ ball z r := by
    rw [mem_ball, dist_eq_norm]
    dsimp only [w]
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have heq : w = z := φ.injective ((hc w hw).trans (hc z (mem_ball_self hr)).symm)
  have hr0 : (r/2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact hr0 (Complex.ofReal_injective (add_left_cancel (show z + (r/2 : ℝ) = z+0 by
    simpa only [add_zero] using heq)))

 theorem holomorphicHomeomorph_inverse_differentiableAt
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : DifferentiableAt ℂ φ.symm (φ z) := by
  have ha := hφ.analyticAt (hU.mem_nhds hz)
  have hn : ∀ᶠ w in 𝓝[≠] z, deriv φ w ≠ 0 :=
    ha.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (holomorphicHomeomorph_deriv_not_locally_zero φ hU hφ hz)
  have ht : Tendsto φ.symm (𝓝[≠] (φ z)) (𝓝[≠] z) := by
    change map φ.symm (𝓝[≠] (φ z)) ≤ 𝓝[≠] z
    rw [φ.symm.map_punctured_nhds_eq, φ.symm_apply_apply]
  apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ?_ φ.symm.continuous.continuousAt).differentiableAt
  have hu : ∀ᶠ y in 𝓝 (φ z), φ.symm y ∈ U := by
    have ht₀ : Tendsto φ.symm (𝓝 (φ z)) (𝓝 z) := by
      simpa only [φ.symm_apply_apply] using φ.symm.continuous.tendsto (φ z)
    exact ht₀.eventually (hU.mem_nhds hz)
  filter_upwards [ht.eventually hn, hu.filter_mono nhdsWithin_le_nhds] with y hy hyU
  have hcont : ContDiffAt ℂ 1 φ (φ.symm y) :=
    (hφ.analyticAt (hU.mem_nhds hyU)).contDiffAt
  have hs := hcont.hasStrictDerivAt'
    ((hφ _ hyU).differentiableAt (hU.mem_nhds hyU)).hasDerivAt (by norm_num)
  have hi := hs.to_local_left_inverse hy (Eventually.of_forall φ.symm_apply_apply)
  simpa only [φ.apply_symm_apply] using hi.hasDerivAt.differentiableAt

 theorem holomorphicHomeomorph_deriv_ne_zero
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : deriv φ z ≠ 0 := by
  have hf := ((hφ z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hi := (holomorphicHomeomorph_inverse_differentiableAt φ hU hφ hz).hasDerivAt
  have hh := (hi.comp z hf).deriv
  have hid : ((φ.symm : ℂ → ℂ) ∘ (φ : ℂ → ℂ)) = id := funext φ.symm_apply_apply
  have hidder : deriv (id : ℂ → ℂ) z = 1 := (hasDerivAt_id z).deriv
  rw [hid, hidder] at hh
  intro hzero
  rw [hzero, mul_zero] at hh
  exact one_ne_zero hh

 theorem holomorphicHomeomorph_conformal (φ : ℂ ≃ₜ ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (hb : (fun z => φ z-z) =O[Bornology.cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalOn φ.onePointCongr (((↑) : ℂ → Sphere) '' U ∪ {OnePoint.infty}) := by
  have he : (φ.onePointCongr : Sphere → Sphere) = extendAtInfinity φ := by
    funext p
    cases p using OnePoint.rec <;> rfl
  rw [he]
  exact isConformalOn_extendAtInfinity hU hφ
    (fun z hz => holomorphicHomeomorph_deriv_ne_zero φ hU hφ hz) hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoordinateLines
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate lines in the actual Euclidean Sobolev plane. Their
one-dimensional derivatives and total energies are the physical partials. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physicalCoordinateLine_contDiff (i : Fin 2) (y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCoordinateLine i y) := by
  unfold physicalCoordinateLine
  split <;> fun_prop

 theorem physicalCoordinateLine_deriv {f : EuclideanPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) (y x : ℝ) :
    deriv (fun t => f (physicalCoordinateLine i y t)) x =
      fderiv ℝ f (physicalCoordinateLine i y x) (EuclideanSpace.single i 1) := by
  have h0 := (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h1 := (hasDerivAt_const x y).prodMk (hasDerivAt_id x)
  have he0 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt x h0
  have he1 := euclideanPlaneCoordinates.symm.hasFDerivAt.comp_hasDerivAt x h1
  fin_cases i
  · simpa [physicalCoordinateLine,Function.comp_def,
      show euclideanPlaneCoordinates.symm (1,0) = EuclideanSpace.single (0 : Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 0] using
      ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt x he0).deriv
  · simpa [physicalCoordinateLine,Function.comp_def,
      show euclideanPlaneCoordinates.symm (0,1) = EuclideanSpace.single (1 : Fin 2) 1 from
        euclideanPlaneCoordinates_symm_axis 1] using
      ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt x he1).deriv

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskAEPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial payment needs only an almost-everywhere density bound. This
version applies to the actual L² sum furnished by ball synthesis. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem trace_primitive_line_payment_ae
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P : ℝ → ℝ} {L R : ℝ}
    (hg : ∀ j, IntervalIntegrable (g j) volume L R) (hP : IntervalIntegrable P volume L R)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n, ∀ᵐ s ∂volume.restrict (uIoc L R),
      ∑ j ∈ Finset.range n, volume.real (I j)*g j s ≤ P s)
    (a t : ℝ) {x y : ℝ} (hx : x ∈ uIcc L R) (hy : y ∈ uIcc L R) :
    |infiniteTracePrimitive cutoff I a x t-infiniteTracePrimitive cutoff I a y t| ≤
      ∫ s in uIoc x y, P s := by
  have hsub : uIoc x y ⊆ uIoc L R :=
    uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx hy)
  have hg' (j : ℕ) : IntegrableOn (g j) (uIoc x y) volume := (hg j).def'.mono_set hsub
  have hP' : IntegrableOn P (uIoc x y) volume := hP.def'.mono_set hsub
  have hfinite (n : ℕ) :
      |finiteTracePrimitive cutoff I a x t n-finiteTracePrimitive cutoff I a y t n| ≤
        ∫ s in uIoc x y, P s := by
    apply (finiteTracePrimitive_variation hc hI hIf x y a t n).trans
    calc
      _ ≤ ∑ j ∈ Finset.range n, volume.real (I j)*(∫ s in uIoc x y, g j s) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hcut j x hx y hy) (measureReal_nonneg)
      _ = ∫ s in uIoc x y, ∑ j ∈ Finset.range n, volume.real (I j)*g j s := by
        rw [integral_finsetSum _ (fun j _ => (hg' j).const_mul _)]
        exact Finset.sum_congr rfl (fun j _ => (integral_const_mul _ _).symm)
      _ ≤ ∫ s in uIoc x y, P s := by
        apply integral_mono_ae (integrable_finsetSum _ (fun j _ => (hg' j).const_mul _)) hP'
        exact ae_restrict_of_ae_restrict_of_subset hsub (hdom n)
  exact le_of_tendsto
    (((finiteTracePrimitive_tendsto hc hI x a t).sub
      (finiteTracePrimitive_tendsto hc hI y a t)).abs)
    (Eventually.of_forall hfinite)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TracePrimitiveMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and a uniform bound for the actual infinite primitive;
the raw endpoint only needs to be measurable. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finiteTraceMask_comp {X Y : Type*} (cutoff : ℕ → X → ℝ)
    (I : ℕ → Set ℝ) (φ : Y → X) (y : Y) (t : ℝ) (n : ℕ) :
    finiteTraceMask (fun j z => cutoff j (φ z)) I y t n =
      finiteTraceMask cutoff I (φ y) t n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteTraceMask,ih]

 theorem infiniteTraceMask_comp {X Y : Type*} (cutoff : ℕ → X → ℝ)
    (I : ℕ → Set ℝ) (φ : Y → X) (y : Y) (t : ℝ) :
    infiniteTraceMask (fun j z => cutoff j (φ z)) I y t =
      infiniteTraceMask cutoff I (φ y) t := by
  simp only [infiniteTraceMask,finiteTraceMask_comp]

 theorem infiniteTracePrimitive_comp {X Y : Type*} (cutoff : ℕ → X → ℝ)
    (I : ℕ → Set ℝ) (φ : Y → X) (a : ℝ) (y : Y) (t : ℝ) :
    infiniteTracePrimitive (fun j z => cutoff j (φ z)) I a y t =
      infiniteTracePrimitive cutoff I a (φ y) t := by
  simp only [infiniteTracePrimitive,infiniteTraceMask_comp]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonRealCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed physical balloon system in the real product
coordinates used by the rectangle Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_trace_balloon_real_system (hmax : PlanarMaximalL2)
    (c : ℕ → ℂ) (r a : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (ha : ∀ j, 0 ≤ a j)
    (hdisj : Pairwise (Disjoint on fun j => Metric.ball (c j) (r j)))
    (hr2 : Summable (fun j => r j^2)) (ha2 : Summable (fun j => a j^2)) (m : ℕ) :
    ∃ (cutoff : ℕ → (ℝ × ℝ) → ℝ) (P : (ℝ × ℝ) → ℝ),
      (∀ j, ContDiff ℝ 1 (cutoff j)) ∧ (∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) ∧
      (∀ j x, ‖Complex.equivRealProdCLM.symm x-c j‖ ≤
        traceBalloonInnerRatio m*traceBalloonRadius r m j → cutoff j x = 0) ∧
      (∀ j x, traceBalloonRadius r m j ≤ ‖Complex.equivRealProdCLM.symm x-c j‖ → cutoff j x = 1) ∧
      Measurable P ∧ (∀ x, 0 ≤ P x) ∧ MemLp P 2 volume ∧
      (∀ᵐ x ∂volume, ∀ n, ∑ j ∈ Finset.range n, a j*‖fderiv ℝ (cutoff j) x‖ ≤ P x) := by
  obtain ⟨C,cut,P,_,hcut,hunit,hzero,hout,_,hPm,hP0,hP2,hdom⟩ :=
    exists_trace_balloon_system hmax c r a hr ha hdisj hr2 ha2 m
  let T := Complex.equivRealProdCLM.symm
  let L : ℝ := ‖T.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  have hmp : MeasurePreserving T volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  refine ⟨(fun j x => cut j (T x)),(fun x => L*P (T x)),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    exact ((hcut j).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp T.contDiff
  · exact fun j x => hunit j (T x)
  · exact fun j x hx => hzero j (T x) hx
  · exact fun j x hx => hout j (T x) hx
  · exact measurable_const.mul (hPm.comp T.continuous.measurable)
  · exact fun x => mul_nonneg hL (hP0 _)
  · exact (hP2.comp_measurePreserving hmp).const_mul L
  · filter_upwards [hmp.quasiMeasurePreserving.ae hdom] with x hx
    intro n
    calc
      _ ≤ ∑ j ∈ Finset.range n, a j*(‖fderiv ℝ (cut j) (T x)‖*L) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (ha j)
        change ‖fderiv ℝ (cut j ∘ T) x‖ ≤ ‖fderiv ℝ (cut j) (T x)‖*L
        rw [fderiv_comp x ((hcut j).differentiable (by simp) _) T.differentiableAt,T.fderiv]
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = L*(∑ j ∈ Finset.range n, a j*‖fderiv ℝ (cut j) (T x)‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ L*P (T x) := mul_le_mul_of_nonneg_left (hx n) hL

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteBalloonAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite prefix of shrinking balloons is eventually avoided on
an open neighborhood of a point outside the limiting closed disks. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem traceBalloonRadius_le_first {r : ℕ → ℝ} (m j : ℕ) :
    traceBalloonRadius r m j ≤ traceBalloonRadius r 0 j := by
  by_cases hj : 0 < r j
  · have he : traceBalloonRadius r 0 j = 2*r j := by
      norm_num [traceBalloonRadius,hj]
    rw [he]
    exact traceBalloonRadius_le_double m j hj
  · simp only [traceBalloonRadius,ite_eq_right hj,Nat.cast_zero,zero_add,div_one]
    apply div_le_self (traceExtraRadius_pos j).le
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith

 theorem exists_finite_balloon_avoidance {c : ℕ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ j, 0 ≤ r j) {z : ℂ} (hz : ∀ j, r j < ‖z-c j‖) (N : ℕ) :
    ∃ (m : ℕ) (V : Set ℂ), IsOpen V ∧ z ∈ V ∧
      ∀ w ∈ V, ∀ j < N, traceBalloonRadius r m j ≤ ‖w-c j‖ := by
  have he (j : ℕ) : ∀ᶠ m in atTop, traceBalloonRadius r m j < ‖z-c j‖ :=
    (traceBalloonRadius_tendsto hr j).eventually (gt_mem_nhds (hz j))
  have hall : ∀ᶠ m in atTop, ∀ j ∈ Finset.range N, traceBalloonRadius r m j < ‖z-c j‖ :=
    (Finset.eventually_all (Finset.range N)).mpr (fun j _ => he j)
  obtain ⟨m,hm⟩ := hall.exists
  let V := ⋂ j ∈ Finset.range N, {w : ℂ | traceBalloonRadius r m j < ‖w-c j‖}
  have hV : IsOpen V := isOpen_biInter_finset (fun j _ => isOpen_lt continuous_const (by fun_prop))
  refine ⟨m,V,hV,mem_iInter₂.mpr hm,?_⟩
  intro w hw j hj
  exact (mem_iInter₂.mp hw j (Finset.mem_range.mpr hj)).le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedCommonPoints
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common point set uses the full matched component family. The
single unused-code center may be omitted during local compression and
restored at the end, since a singleton has null scalar image. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem commonPointPlane_singletons
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {z : ℂ} (hz : z ∈ D.commonPointPlane) :
    connectedComponentIn Gᶜ (z : Sphere) = {(z : Sphere)} ∧
      ∃ p, D.targetFiber (z : Sphere) = {p} :=
  D.unindexed_components_singleton hG hinf hf hH hinf' hz.1 hz.2

variable {D} [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.commonPoint_gap (E : D.MatchedRoundDisks)
    {z : ℂ} (hz : z ∈ D.commonPointPlane) (hz0 : z ≠ 0) (n : ℕ) :
    E.traceRadius n < ‖z-E.traceCenter n‖ := by
  by_cases hn : n ∈ Set.range (Encodable.encode : D.IndexedMatchedPair → ℕ)
  · obtain ⟨j,rfl⟩ := hn
    simp only [traceRadius,traceCenter,traceEnumeration_encode]
    apply lt_of_not_ge
    intro h
    exact hz.2 j (by rw [E.source_eq]; exact mem_image_of_mem _ (by simpa only [mem_closedBall,dist_eq_norm] using h))
  · simp only [traceRadius,traceCenter,traceEnumeration_missing _ _ hn,sub_zero]
    exact norm_pos_iff.mpr hz0

 theorem MatchedRoundDisks.commonPoint_prefix_avoidance (E : D.MatchedRoundDisks)
    {z : ℂ} (hz : z ∈ D.commonPointPlane) (hz0 : z ≠ 0) (N : ℕ) :
    ∃ (m : ℕ) (V : Set ℂ), IsOpen V ∧ z ∈ V ∧
      ∀ w ∈ V, ∀ j < N, traceBalloonRadius E.traceRadius m j ≤ ‖w-E.traceCenter j‖ :=
  exists_finite_balloon_avoidance (traceEnumeration_nonneg E.source_nonneg)
    (E.commonPoint_gap hz hz0) N

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalMobiusIdentity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A principally normalized Möbius transformation is the identity.
The finite-coordinate remainder is entire and tends to zero at infinity. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_mobius_identity (M : Mobius)
    (hnorm : IsPrincipalNormalized (fun p : Sphere => M • p)) :
    ∀ p : Sphere, M • p = p := by
  have hc : M 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hnorm.1
  have hd : M 1 1 ≠ 0 := by
    intro hd
    apply M.det_ne_zero
    simp [Matrix.det_fin_two,hc,hd]
  have hfinite (z : ℂ) : M • (z : Sphere) =
      (((M 0 0 * z + M 0 1) / M 1 1 : ℂ) : Sphere) := by
    rw [OnePoint.smul_some_eq_ite]
    simp only [hc,zero_mul,zero_add,ite_eq_right hd]
  let R : ℂ → ℂ := fun z => (M 0 0 * z + M 0 1) / M 1 1 - z
  have hR : Differentiable ℂ R := by
    dsimp only [R]
    fun_prop
  have ht : Tendsto R (Filter.cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    have hh := principal_remainder_tendsto_zero hnorm.2
    simpa only [hfinite,finiteCoord_coe] using hh
  have hzero := hR.eq_const_of_tendsto_cocompact ht
  intro p
  cases p using OnePoint.rec with
  | infty => exact hnorm.1
  | coe z =>
    rw [hfinite]
    apply congrArg ((↑) : ℂ → Sphere)
    have hz : R z = 0 := congrFun hzero z
    exact sub_eq_zero.mp hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundedSphereHomotopy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded-displacement plane map extends to a sphere map homotopic
to the identity by the straight-line homotopy. Uniform properness proves
joint continuity at infinity. -/
open Set Function Filter Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

 theorem continuous_straightSphereHomotopy {F : ℂ → ℂ} (hF : Continuous F)
    {C : ℝ} (_hC : 0 ≤ C) (hbound : ∀ z, ‖F z-z‖ ≤ C) :
    Continuous (straightSphereHomotopy F) := by
  have hdiff (s : unitInterval) (z : ℂ) : ‖(z+(s:ℝ) • (F z-z))-z‖ ≤ C := by
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg s.property.1]
    exact (mul_le_mul s.property.2 (hbound z) (norm_nonneg _) zero_le_one).trans_eq (one_mul C)
  rw [continuous_iff_continuousAt]
  rintro ⟨s,p⟩
  cases p using OnePoint.rec with
  | coe z =>
    have hc : ContinuousAt finiteCoord (z : Sphere) :=
      (continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hsnd : ContinuousAt (fun t : unitInterval × Sphere => t.2) (s,(z : Sphere)) :=
      continuous_snd.continuousAt
    have hcoord : ContinuousAt (fun t : unitInterval × Sphere => finiteCoord t.2)
        (s,(z : Sphere)) := hc.comp_of_eq hsnd rfl
    have hg : ContinuousAt (fun t : unitInterval × Sphere =>
        (finiteCoord t.2+(t.1:ℝ) • (F (finiteCoord t.2)-finiteCoord t.2) : ℂ)) (s,(z:Sphere)) :=
      hcoord.add
        ((continuous_subtype_val.comp continuous_fst).continuousAt.smul
          ((hF.continuousAt.comp hcoord).sub
            hcoord))
    apply (OnePoint.continuous_coe.continuousAt.comp hg).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually
      (isClosed_singleton.isOpen_compl.mem_nhds (show (z:Sphere) ∉ {OnePoint.infty} by simp))] with t ht
    obtain ⟨w,hw⟩ := OnePoint.ne_infty_iff_exists.mp ht
    simp only [straightSphereHomotopy,Function.comp_apply]
    rw [← hw]
    simp only [extendAtInfinity_coe,finiteCoord_coe]
  | infty =>
    change Tendsto (straightSphereHomotopy F) (𝓝 (s,OnePoint.infty)) (𝓝 OnePoint.infty)
    apply _root_.tendsto_nhds.mpr
    intro O hO hOO
    have hK := ((OnePoint.isOpen_iff_of_mem hOO).mp hO).2
    obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
    let B := ((↑) : ℂ → Sphere) '' closedBall 0 (R+C)
    have hB : IsClosed B :=
      (OnePoint.isClosed_image_coe).mpr ⟨isClosed_closedBall,isCompact_closedBall _ _⟩
    have hBinf : OnePoint.infty ∉ B := OnePoint.infty_notMem_image_coe
    filter_upwards [continuous_snd.continuousAt.eventually
      (hB.isOpen_compl.mem_nhds hBinf)] with t ht
    change straightSphereHomotopy F t ∈ O
    cases hp : t.2 using OnePoint.rec with
    | infty => simpa only [straightSphereHomotopy,hp,extendAtInfinity_infty] using hOO
    | coe z =>
      have hz : R+C < ‖z‖ := by
        have hn : z ∉ closedBall 0 (R+C) := by
          intro hz
          exact ht ⟨z,hz,hp.symm⟩
        simpa only [mem_closedBall_zero_iff,not_le] using hn
      change extendAtInfinity (fun z => z+(t.1:ℝ) • (F z-z)) t.2 ∈ O
      rw [hp,extendAtInfinity_coe]
      by_contra hn
      have hsmall : ‖z+(t.1:ℝ) • (F z-z)‖ ≤ R := hR _ hn
      have htriangle := norm_le_norm_sub_add z (z+(t.1:ℝ) • (F z-z))
      rw [norm_sub_rev] at htriangle
      have hd := hdiff t.1 z
      linarith

 theorem homotopic_id_of_bounded_displacement {F : ℂ → ℂ} (hF : Continuous F)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, ‖F z-z‖ ≤ C)
    (hExt : Continuous (extendAtInfinity F)) :
    ContinuousMap.Homotopic (⟨extendAtInfinity F,hExt⟩ : C(Sphere,Sphere)) (ContinuousMap.id Sphere) := by
  apply ContinuousMap.Homotopic.symm
  refine ⟨{
    toFun := straightSphereHomotopy F
    continuous_toFun := continuous_straightSphereHomotopy hF hC hbound
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    cases x using OnePoint.rec <;> simp [straightSphereHomotopy,extendAtInfinity]
  · intro x
    cases x using OnePoint.rec <;> simp [straightSphereHomotopy,extendAtInfinity]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrincipalHomeomorphOrientation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Principal normalization gives bounded displacement on the entire
plane. Its straight-line sphere homotopy supplies the orientation class
used in the definition of conformal removability. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_homeomorph_orientation (H : Sphere ≃ₜ Sphere)
    (hnorm : IsPrincipalNormalized H) : OrientationPreserving H := by
  let F := fun z : ℂ => finiteCoord (H (z : Sphere))
  have hfinite (z : ℂ) : H (z : Sphere) ≠ OnePoint.infty := by
    intro he
    have hh : (z : Sphere) = OnePoint.infty := H.injective (he.trans hnorm.1.symm)
    exact OnePoint.coe_ne_infty z hh
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro z
    have hc : ContinuousAt finiteCoord (H (z : Sphere)) :=
      (continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds (hfinite z))
    have hh : ContinuousAt (fun z : ℂ => H (z : Sphere)) z :=
      (H.continuous.comp OnePoint.continuous_coe).continuousAt
    exact hc.comp_of_eq hh rfl
  have hzero := principal_remainder_tendsto_zero hnorm.2
  have hsmall : ∀ᶠ z in Filter.cocompact ℂ, ‖F z-z‖ ≤ 1 := by
    rw [← Metric.cobounded_eq_cocompact]
    have hn := hzero.norm
    simp only [norm_zero] at hn
    exact (hn.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))).mono (fun _ h => h.le)
  obtain ⟨K,hK,hKout⟩ := Filter.mem_cocompact.mp hsmall
  obtain ⟨R,hR⟩ := (hK.image (hF.sub continuous_id)).isBounded.exists_norm_le
  have hbound (z : ℂ) : ‖F z-z‖ ≤ max R 1 := by
    by_cases hz : z ∈ K
    · exact (hR _ (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    · exact (hKout hz).trans (le_max_right _ _)
  have hExt : extendAtInfinity F = H := by
    funext p
    cases p using OnePoint.rec with
    | infty => exact hnorm.1.symm
    | coe z => exact CannonMobius.coe_coordinate (hfinite z)
  have hh := homotopic_id_of_bounded_displacement hF
    (show (0:ℝ) ≤ max R 1 by exact zero_le_one.trans (le_max_right _ _)) hbound
    (hExt.symm ▸ H.continuous)
  unfold OrientationPreserving
  simpa only [hExt] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ConformalEqOn
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conformality is unchanged by equality on an open source set. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem IsConformalAt.congr_of_eventuallyEq {f g : Sphere → Sphere} {p : Sphere}
    (hf : IsConformalAt f p) (he : g =ᶠ[𝓝 p] f) : IsConformalAt g p := by
  have hp : g p = f p := he.eq_of_nhds
  refine ⟨hf.1.congr_of_eventuallyEq he, hf.2.choose, hf.2.choose_spec.1, ?_⟩
  apply hf.2.choose_spec.2.congr_of_eventuallyEq
  have hc : Tendsto (chartSymm p) (𝓝 (chart p p)) (𝓝 p) := by
    simpa only [chartSymm_chart_self] using
      (continuous_chartSymm p).tendsto (chart p p)
  filter_upwards [hc.eventually he] with z hz
  rw [hp,hz]

 theorem IsConformalOn.congr_eqOn {G : Set Sphere} {f g : Sphere → Sphere}
    (hf : IsConformalOn f G) (hG : IsOpen G) (he : EqOn g f G) : IsConformalOn g G := by
  intro p hp
  apply (hf p hp).congr_of_eventuallyEq
  filter_upwards [hG.mem_nhds hp] with x hx
  exact he hx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RemovableNormalizedExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normalized homeomorphic conformal extension across a removable
complement is the identity. All normalization and orientation properties
are derived from the extension and its prescribed exterior germ. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_normalized_extension {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) {f g : Sphere → Sphere}
    (hf : IsPrincipalNormalized f) (he : EqOn g f G) : IsPrincipalNormalized g := by
  refine ⟨(he hinf).trans hf.1, ?_⟩
  apply hf.2.congr' _ EventuallyEq.rfl
  have hm := OnePoint.tendsto_coe_infty (hG.mem_nhds hinf)
  change {z : ℂ | (z : Sphere) ∈ G} ∈ Filter.coclosedCompact ℂ at hm
  rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at hm
  filter_upwards [hm] with z hz
  rw [he hz]

 theorem removable_normalized_extension_eq_id {G : Set Sphere}
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hrem : IsConformallyRemovable Gᶜ) {f : Sphere → Sphere}
    (hf : IsConformalOn f G) (hnorm : IsPrincipalNormalized f)
    (H : Sphere ≃ₜ Sphere) (he : EqOn H f G) : ∀ p, H p = p := by
  have hH := principal_normalized_extension hG hinf hnorm he
  have hconf : IsConformalOn H Gᶜᶜ := by
    rw [compl_compl]
    exact hf.congr_eqOn hG he
  obtain ⟨M,hM⟩ := hrem.2 H (principal_homeomorph_orientation H hH) hconf
  have hn : IsPrincipalNormalized (fun p : Sphere => M • p) := by
    have heq : (fun p : Sphere => M • p) = H := funext (fun p => (hM p).symm)
    rw [heq]
    exact hH
  exact fun p => (hM p).trans (principal_mobius_identity M hn p)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RemovableAreaZero
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact removable set in the finite chart has zero planar area.
A principal real Beltrami solution with conductivity two on that set
must be the identity. Uniqueness of its weak derivatives then forces
the set to be null. Only the already recorded principal Beltrami input
is used. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 private theorem weak_coordinate_one (i : Fin 2) (R : ℝ) :
    DeGiorgi.HasWeakPartialDeriv i (fun _ : EuclideanPlane => (1 : ℝ))
      (fun x => x i) (ball 0 R) := by
  let L : EuclideanPlane →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap
  have hL : (fun x : EuclideanPlane => x i) = L := rfl
  have hh := weakPartial_of_smooth_on (U := ball 0 R) isOpen_ball L.contDiff.contDiffOn i
  have hd : (fun x => fderiv ℝ L x (EuclideanSpace.single i 1)) =
      (fun _ : EuclideanPlane => (1 : ℝ)) := by
    funext x
    rw [L.fderiv]
    simp [L]
  rw [hd] at hh
  simpa only [hL] using hh

 theorem removable_physical_compact_volume_zero
    (hprincipal : PrincipalRealBeltrami) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hrem : IsConformallyRemovable (planeSphere '' K)) :
    volume K = 0 := by
  obtain ⟨φ,D,ht,hsys,hh,hbig⟩ := exists_principal_conductivity_holomorphic hprincipal hK 2 (by omega)
  let G := (planeSphere '' K)ᶜ
  have hG : IsOpen G := (hK.image continuous_planeSphere).isClosed.isOpen_compl
  have hinf : OnePoint.infty ∈ G := by
    rintro ⟨x,hx,he⟩
    exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) he
  have hsets : (((↑) : ℂ → Sphere) '' (complexPlaneCoordinates '' K)ᶜ ∪ {OnePoint.infty}) = G := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [G,planeSphere]
    | coe z => simp [G,planeSphere]
  have hconf : IsConformalOn φ.onePointCongr G := by
    rw [← hsets]
    exact holomorphicHomeomorph_conformal φ
      (hK.image complexPlaneCoordinates.continuous).isClosed.isOpen_compl hh hbig
  have hext : (φ.onePointCongr : Sphere → Sphere) = extendAtInfinity φ := by
    funext p
    cases p using OnePoint.rec <;> rfl
  have hnorm : IsPrincipalNormalized φ.onePointCongr := by
    rw [hext]
    exact isPrincipalNormalized_extendAtInfinity hbig
  have hid := removable_normalized_extension_eq_id hG hinf
    (by simpa only [G,compl_compl] using hrem) hconf hnorm φ.onePointCongr
    (fun _ _ => rfl)
  have hφ (z : ℂ) : φ z = z := OnePoint.coe_injective (hid (z : Sphere))
  obtain ⟨R,hKR⟩ := hK.isBounded.subset_ball (0 : EuclideanPlane)
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) R)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
  have hwR : DeGiorgi.HasWeakPartialDeriv (0 : Fin 2)
      (fun x => D.realGradient x 0) (fun x : EuclideanPlane => x 0) (ball 0 R) := by
    simpa only [hφ,complexPlaneCoordinates_apply] using
      weakPartial_restrict_from_univ (D.real_weak 0) (ball 0 R)
  have hwI : DeGiorgi.HasWeakPartialDeriv (1 : Fin 2)
      (fun x => D.imagGradient x 1) (fun x : EuclideanPlane => x 1) (ball 0 R) := by
    simpa only [hφ,complexPlaneCoordinates_apply] using
      weakPartial_restrict_from_univ (D.imag_weak 1) (ball 0 R)
  have hr : (fun x => D.realGradient x 0) =ᵐ[volume.restrict (ball 0 R)] fun _ => 1 :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq isOpen_ball hwR (weak_coordinate_one 0 R)
      ((D.real_memLp R 0).locallyIntegrable (by norm_num)) (locallyIntegrable_const 1)
  have hi : (fun x => D.imagGradient x 1) =ᵐ[volume.restrict (ball 0 R)] fun _ => 1 :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq isOpen_ball hwI (weak_coordinate_one 1 R)
      ((D.imag_memLp R 1).locallyIntegrable (by norm_num)) (locallyIntegrable_const 1)
  have hnull : ∀ᵐ x ∂volume, x ∉ K := by
    have hr' := (ae_restrict_iff' measurableSet_ball).mp hr
    have hi' := (ae_restrict_iff' measurableSet_ball).mp hi
    filter_upwards [hsys,hr',hi'] with x hx hxr hxi hxK
    have he := hx.1
    rw [hxr (hKR hxK),hxi (hKR hxK)] at he
    have hv : conductivityValue K 2 x = 2 := by simp [conductivityValue,hxK]
    rw [hv] at he
    norm_num at he
  simpa only [not_not,Set.ofPred_mem_eq] using (ae_iff.mp hnull)

 theorem removable_complement_volume_zero
    (hprincipal : PrincipalRealBeltrami) {G : Set Sphere}
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hrem : IsConformallyRemovable Gᶜ) :
    volume (physicalPlaneDomain G)ᶜ = 0 := by
  have hno : OnePoint.infty ∉ Gᶜ := fun h => h hinf
  have hK := hG.isClosed_compl.isCompact.image_of_continuousOn
    (continuousOn_finiteCoord_of_avoids_infty hno)
  have heq : complexPlaneCoordinates.symm '' (finiteCoord '' Gᶜ) =
      (physicalPlaneDomain G)ᶜ := by
    ext x
    constructor
    · rintro ⟨z,⟨p,hp,rfl⟩,rfl⟩
      change (complexPlaneCoordinates (complexPlaneCoordinates.symm (finiteCoord p)) : Sphere) ∉ G
      rw [complexPlaneCoordinates.apply_symm_apply]
      have hc : ((finiteCoord p : ℂ) : Sphere) = p :=
        CannonMobius.coe_coordinate (fun he => hno (he ▸ hp))
      rwa [hc]
    · intro hx
      exact ⟨complexPlaneCoordinates x,⟨planeSphere x,hx,rfl⟩,
        complexPlaneCoordinates.symm_apply_apply x⟩
  have hcompact : IsCompact (physicalPlaneDomain G)ᶜ := by
    rw [← heq]
    exact hK.image complexPlaneCoordinates.symm.continuous
  have himage : planeSphere '' (physicalPlaneDomain G)ᶜ = Gᶜ := by
    ext p
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hp
      obtain ⟨x,rfl⟩ := exists_planeSphere_eq (fun he => hno (he ▸ hp))
      exact ⟨x,hp,rfl⟩
  apply removable_physical_compact_volume_zero hprincipal hcompact
  rwa [himage]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalLineFubini
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini on the two physical coordinate line families. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physicalCoordinatePlane_measurePreserving (i : Fin 2) :
    MeasurePreserving (fun p : ℝ × ℝ => physicalCoordinateLine i p.1 p.2)
      (volume.prod volume) volume := by
  have he : MeasurePreserving euclideanPlaneCoordinates.symm (volume.prod volume) volume := by
    simpa only [← Measure.volume_eq_prod] using euclideanPlaneCoordinates_symm_measurePreserving
  fin_cases i
  · simpa [physicalCoordinateLine,Function.comp_def,Prod.swap] using
      he.comp (Measure.measurePreserving_swap (μ := volume) (ν := volume))
  · simpa [physicalCoordinateLine] using he

 theorem ae_ae_physicalCoordinateLine {p : EuclideanPlane → Prop}
    (hp : ∀ᵐ z ∂volume, p z) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ᵐ x ∂volume, p (physicalCoordinateLine i y x) := by
  exact Measure.ae_ae_of_ae_prod ((physicalCoordinatePlane_measurePreserving i).quasiMeasurePreserving.ae hp)

 theorem memLp_physicalCoordinateLine_ae {P : EuclideanPlane → ℝ}
    (hP : Measurable P) (hL : MemLp P 2 volume) (i : Fin 2) :
    ∀ᵐ y ∂volume, MemLp (fun x => P (physicalCoordinateLine i y x)) 2 volume := by
  have hs := (physicalCoordinatePlane_measurePreserving i).integrable_comp_of_integrable hL.integrable_sq
  filter_upwards [hs.prod_right_ae] with y hy
  exact (memLp_two_iff_integrable_sq (hP.comp (physicalCoordinateLine_contDiff i y).continuous.measurable).aestronglyMeasurable).mpr hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RealCoordinateLines
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product and complex coordinates of the physical line families. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem realCoordinateLine_contDiff (i : Fin 2) (y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (realCoordinateLine i y) := by
  unfold realCoordinateLine
  split <;> fun_prop

 theorem realCoordinateLine_physical (i : Fin 2) (y x : ℝ) :
    euclideanPlaneCoordinates (physicalCoordinateLine i y x) = realCoordinateLine i y x := by
  unfold physicalCoordinateLine realCoordinateLine
  split <;> exact euclideanPlaneCoordinates.apply_symm_apply _

 theorem realCoordinatePlane_measurePreserving (i : Fin 2) :
    MeasurePreserving (fun p : ℝ × ℝ => realCoordinateLine i p.1 p.2)
      (volume.prod volume) volume := by
  have h := euclideanPlaneCoordinates_measurePreserving.comp
    (physicalCoordinatePlane_measurePreserving i)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact (realCoordinateLine_physical i p.1 p.2).symm

 theorem ae_ae_realCoordinateLine {p : (ℝ × ℝ) → Prop}
    (hp : ∀ᵐ z ∂volume, p z) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ᵐ x ∂volume, p (realCoordinateLine i y x) :=
  Measure.ae_ae_of_ae_prod ((realCoordinatePlane_measurePreserving i).quasiMeasurePreserving.ae hp)

 theorem memLp_realCoordinateLine_ae {P : (ℝ × ℝ) → ℝ}
    (hP : Measurable P) (hL : MemLp P 2 volume) (i : Fin 2) :
    ∀ᵐ y ∂volume, MemLp (fun x => P (realCoordinateLine i y x)) 2 volume := by
  have hs := (realCoordinatePlane_measurePreserving i).integrable_comp_of_integrable hL.integrable_sq
  filter_upwards [hs.prod_right_ae] with y hy
  exact (memLp_two_iff_integrable_sq (hP.comp (realCoordinateLine_contDiff i y).continuous.measurable).aestronglyMeasurable).mpr hy

 theorem realCoordinateLine_deriv {f : (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (y x : ℝ) :
    deriv (fun t => f (realCoordinateLine i y t)) x =
      fderiv ℝ f (realCoordinateLine i y x) (if i = 0 then (1,0) else (0,1)) := by
  fin_cases i
  · simpa [realCoordinateLine,Function.comp_def] using
      ((hf.differentiable_one (x,y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv
  · simpa [realCoordinateLine,Function.comp_def] using
      ((hf.differentiable_one (y,x)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))).deriv

 theorem realCoordinateLine_abs_deriv_le {f : (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (y x : ℝ) :
    |deriv (fun t => f (realCoordinateLine i y t)) x| ≤ ‖fderiv ℝ f (realCoordinateLine i y x)‖ := by
  rw [realCoordinateLine_deriv hf,← Real.norm_eq_abs]
  apply ContinuousLinearMap.unit_le_opNorm
  split <;> simp

 theorem complexCoordinateLine_transverse_le (i : Fin 2) (y x : ℝ) (c : ℂ) :
    |y-transverseCoordinate i c| ≤ ‖complexCoordinateLine i y x-c‖ := by
  fin_cases i
  · simpa [complexCoordinateLine,realCoordinateLine,transverseCoordinate] using
      Complex.abs_im_le_norm (complexCoordinateLine 0 y x-c)
  · simpa [complexCoordinateLine,realCoordinateLine,transverseCoordinate] using
      Complex.abs_re_le_norm (complexCoordinateLine 1 y x-c)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CommonPointNullSet
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common point set is contained in the removable boundary and
therefore has null intersections with almost every coordinate line. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem commonPointPlane_subset_frontier
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {z : ℂ} (hz : z ∈ D.commonPointPlane) : (z : Sphere) ∈ frontier G := by
  have hs := (D.commonPointPlane_singletons hG hinf hf hH hinf' hz).1
  have hproper : Gᶜ ≠ univ := by
    intro he
    exact (show OnePoint.infty ∈ Gᶜ from he.symm ▸ mem_univ _) hinf
  obtain ⟨p,hp,hpf⟩ := component_meets_frontier hG.1.isClosed_compl hproper hz.1
  have hpz : p = (z : Sphere) := mem_singleton_iff.mp (hs ▸ hp)
  simpa only [frontier_compl,hpz] using hpf

 theorem commonPointPlane_line_null
    (hprincipal : PrincipalRealBeltrami)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G)) (i : Fin 2) :
    ∀ᵐ y ∂volume, volume {x | complexCoordinateLine i y x ∈ D.commonPointPlane} = 0 := by
  have hn : OnePoint.infty ∈ (frontier G)ᶜ := by
    intro hx
    exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hG.1) hx hinf
  have hvol := removable_complement_volume_zero hprincipal isClosed_frontier.isOpen_compl hn
    (by simpa only [compl_compl] using hrem)
  have havoid : ∀ᵐ z ∂volume, planeSphere z ∉ frontier G := by
    apply ae_iff.mpr
    convert hvol using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  have hc : ∀ᵐ z ∂volume, Complex.equivRealProdCLM.symm z ∉ D.commonPointPlane := by
    have hmp := euclideanPlaneCoordinates_symm_measurePreserving
    filter_upwards [hmp.quasiMeasurePreserving.ae havoid] with z hz
    intro hcommon
    apply hz
    convert D.commonPointPlane_subset_frontier hG hinf hf hH hinf' hcommon using 1
    all_goals try with_reducible_and_instances rfl
    simp only [planeSphere,complexPlaneCoordinates,ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  filter_upwards [ae_ae_realCoordinateLine hc i] with y hy
  simpa only [not_not,complexCoordinateLine] using (ae_iff.mp hy)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedRealMaskSobolev
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the proved open-set Sobolev gluing to the constructed masks.
The only scalar hypotheses concern the actual smooth pullback on the original domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem realPlaneDomain_open {G : Set Sphere} (hG : IsOpen G) : IsOpen (realPlaneDomain G) :=
  hG.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedRealMaskConstruction
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of every mask system, including its actual L² paying
density, continuous compact scalar, and connected residual-dust domain. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.exists_real_mask (E : D.MatchedRoundDisks)
    (hmax : PlanarMaximalL2) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G))
    {φ : Sphere → ℝ} (hφ : Continuous φ) {L : ℝ≥0}
    (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (hφzero : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), φ p = 0) (m : ℕ) :
    Nonempty (MatchedRealMask E hG.1 hf φ L m) := by
  let I := E.traceInterval hG.1 hf φ L
  let a := fun n => volume.real (I n)
  obtain ⟨cut,P,hs,hu,hz,ho,hPm,hP0,hP2,hpay⟩ := exists_trace_balloon_real_system hmax
    E.traceCenter E.traceRadius a (traceEnumeration_nonneg E.source_nonneg)
    (fun _ => measureReal_nonneg)
    (traceEnumeration_ball_disjoint (fun i j h => (E.source_disjoint h).mono
      ball_subset_closedBall ball_subset_closedBall) 0)
    (traceEnumeration_summable_sq E.source_summable) (E.traceInterval_summable_sq hG.1 hf φ L) m
  let ccut := fun n z => cut n (Complex.equivRealProdCLM z)
  have hcu (n : ℕ) (z : ℂ) : ccut n z ∈ Icc (0:ℝ) 1 := hu n _
  have hcc (n : ℕ) : Continuous (ccut n) := (hs n).continuous.comp Complex.equivRealProdCLM.continuous
  have hcz (n : ℕ) (z : ℂ) (h : ‖z-E.traceCenter n‖ ≤
      traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n) : ccut n z = 0 := by
    apply hz
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  have hco (n : ℕ) (z : ℂ) (h : traceBalloonRadius E.traceRadius m n ≤ ‖z-E.traceCenter n‖) : ccut n z = 1 := by
    apply ho
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  obtain ⟨W,hW,hWK,hWz,hO,hOc,hOd,hOr⟩ := E.exists_mask_domain hG hinf hf hG' hinf' hrem
    hφ hL m hcu hcc hcz hco
  let U := fun z => infiniteTracePrimitive ccut I 0 z (φ (D.selectedTarget hG.1 hf (z : Sphere)))
  have hUc : Continuous U := E.mask_continuous hG hinf hf hG' hinf' hφ hL m hcu hcc hcz hco 0
  have hUs : HasCompactSupport U := D.mask_compactSupport hG.1 hinf hf hfix hφzero ccut I
  have hEq : D.realMaskValue E hG.1 hf φ L cut = U ∘ Complex.equivRealProdCLM.symm := by
    funext p
    simp only [realMaskValue,realSelectedScalar,U,ccut,I,comp_apply,
      infiniteTracePrimitive_comp,ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨⟨cut,hs,hu,hz,ho,P,hPm,hP0,hP2,hpay,W,hW,hWK,?_,?_,?_,hO,hOc,hOd,hOr⟩⟩
  · exact hWz
  · rw [hEq]
    exact hUc.comp Complex.equivRealProdCLM.symm.continuous
  · rw [hEq]
    exact hUs.comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPullbackFiniteEnergy
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth target scalar has finite pullback differential.
This is derived from conformal energy transport, not assumed for the mask. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer MatchedConformalEnds
attribute [local instance] sphereMetric sphereBorel

 theorem smooth_pullback_finite_energy
    {f fi : Sphere → Sphere} {G H : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi G H) (hG : IsOpen G) (hH : IsOpen H)
    (hinf : OnePoint.infty ∈ G) (hfix : f OnePoint.infty = OnePoint.infty)
    (hfic : IsConformalOn fi H) {Φ : EuclideanPlane → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : HasCompactSupport Φ) :
    ContDiffOn ℝ 1 (Φ ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap f) (realPlaneDomain G) ∧
      MemLp (fderiv ℝ (Φ ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap f)) 2
        (volume.restrict (realPlaneDomain G)) := by
  have hparts (i : Fin 2) : MemLp (fun x => fderiv ℝ Φ x (EuclideanSpace.single i 1)) 2 volume :=
    ((hΦ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hΦs.fderiv_apply (𝕜 := ℝ) _)
  obtain ⟨hw,hD,_⟩ := smooth_plane_energy_transport heq.symm hH hG
    (heq.infty_mem_target hinf hfix) (heq.inverse_fixes_infty hinf hfix) hfic
    hΦ.contDiffOn (fun i => (hparts i).restrict _)
  let w := planeInverseTransport f Φ
  let b := Φ ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap f
  have he : b = w ∘ euclideanPlaneCoordinates.symm := by
    funext p
    simp only [b,w,planeInverseTransport,comp_apply,ContinuousLinearEquiv.apply_symm_apply]
  have hbin : MapsTo euclideanPlaneCoordinates.symm (realPlaneDomain G) (physicalPlaneDomain G) := by
    intro p hp
    change euclideanPlaneCoordinates.symm p ∈ euclideanPlaneCoordinates ⁻¹' realPlaneDomain G
    simpa only [mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hp
  have hbc : ContDiffOn ℝ 1 b (realPlaneDomain G) := by
    rw [he]
    exact hw.comp euclideanPlaneCoordinates.symm.contDiff.contDiffOn hbin
  refine ⟨hbc,?_⟩
  have hw2 : MemLp (fderiv ℝ w) 2 (volume.restrict (physicalPlaneDomain G)) := by
    apply ((hD 0).norm.add (hD 1).norm).of_le
      ((measurable_fderiv ℝ w).aestronglyMeasurable)
    filter_upwards [] with x
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact planeCovector_norm_le _
  have hmp : MeasurePreserving euclideanPlaneCoordinates.symm (volume.restrict (realPlaneDomain G))
      (volume.restrict (physicalPlaneDomain G)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
      (isOpen_physicalPlaneDomain hG).measurableSet using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  have hmaj := (hw2.norm.comp_measurePreserving hmp).mul_const ‖euclideanPlaneCoordinates.symm.toContinuousLinearMap‖
  apply hmaj.of_le (measurable_fderiv ℝ b).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (realPlaneDomain_open hG).measurableSet] with p hp
  simp only [comp_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),he,
    fderiv_comp p ((hw.contDiffAt ((isOpen_physicalPlaneDomain hG).mem_nhds (hbin hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      euclideanPlaneCoordinates.symm.differentiableAt,euclideanPlaneCoordinates.symm.fderiv]
  exact ContinuousLinearMap.opNorm_comp_le _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SmoothMatchedScalar
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact smooth target scalar supplies all analytic hypotheses of
the actual matched mask. In particular its source differential is L². -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer MatchedConformalEnds
attribute [local instance] sphereMetric sphereBorel

 theorem smooth_compact_sphere_scalar {Φ : EuclideanPlane → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    Continuous (sphereFromPlaneFunction Φ) ∧
      (∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), sphereFromPlaneFunction Φ p = 0) ∧
      ∃ L : ℝ≥0, LipschitzWith L (fun z : ℂ => sphereFromPlaneFunction Φ (z : Sphere)) := by
  refine ⟨continuous_sphereFromPlaneFunction hΦ.continuous hs,
    sphereFromPlaneFunction_zero_near_infty hs,?_⟩
  let g := Φ ∘ complexPlaneCoordinates.symm
  have hg : ContDiff ℝ ∞ g := hΦ.comp complexPlaneCoordinates.symm.contDiff
  have hgs : HasCompactSupport g := hs.comp_homeomorph complexPlaneCoordinates.symm.toHomeomorph
  obtain ⟨B,hB⟩ := (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).bounded_above_of_compact_support (hgs.fderiv ℝ)
  let L : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hl : LipschitzWith L g := lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) (by
    intro z
    change ‖fderiv ℝ g z‖ ≤ max B 0
    exact (hB z).trans (le_max_left _ _))
  have he : (fun z : ℂ => sphereFromPlaneFunction Φ (z : Sphere)) = g :=
    funext (fun z => sphereFromPlaneFunction_coe Φ z)
  rw [he]
  exact ⟨L,hl⟩

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem smooth_selected_scalar_finite_energy
    (hG : IsOpen G) (hH : IsOpen (f '' G)) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    ContDiffOn ℝ 1 (D.realSelectedScalar hG hf (sphereFromPlaneFunction Φ)) (realPlaneDomain G) ∧
      MemLp (fderiv ℝ (D.realSelectedScalar hG hf (sphereFromPlaneFunction Φ))) 2
        (volume.restrict (realPlaneDomain G)) := by
  have hfull := hf
  obtain ⟨hfc,hmap,fi,hfic,himap,hl,hr⟩ := hf
  let heq : IsSmoothSphereEquivalence f fi G (f '' G) :=
    ⟨fun p hp => hfc.isSmoothSphereAt hG hp,hmap,
      fun p hp => hfic.isSmoothSphereAt hH hp,himap,hl,hr⟩
  obtain ⟨hb,hb2⟩ := smooth_pullback_finite_energy heq hG hH hinf hfix hfic hΦ hs
  have he : EqOn (D.realSelectedScalar hG hfull (sphereFromPlaneFunction Φ))
      (Φ ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap f) (realPlaneDomain G) := by
    intro p hp
    rw [realSelectedScalar,D.selectedTarget_on_domain hG hfull hp]
    have hfin := heq.finite_forward hinf hfix hp
    simp only [sphereFromPlaneFunction,ite_eq_right hfin,comp_apply,sphereRealMap]
    rfl
  refine ⟨hb.congr (fun p hp => he hp),?_⟩
  apply hb2.ae_eq
  filter_upwards [ae_restrict_mem (realPlaneDomain_open hG).measurableSet] with p hp
  exact (he.eventuallyEq_of_mem ((realPlaneDomain_open hG).mem_nhds hp)).fderiv_eq.symm

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_GlobalSmoothMatchedMasks
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every compact smooth target test has an actual countable family of
global Sobolev masks. The scalar, its energy, the open domain and the
removable residual dust have all been constructed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 local instance localInst_r3452f0_1 : BorelSpace Sphere := ⟨rfl⟩
theorem MatchedRoundDisks.exists_global_smooth_masks (E : D.MatchedRoundDisks)
    (hmax : PlanarMaximalL2)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G))
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    ∃ L : ℝ≥0, ∀ m : ℕ, ∃ M : MatchedRealMask E hG.1 hf (sphereFromPlaneFunction Φ) L m,
      Nonempty (DeGiorgi.MemW1pWitness 2
        (D.realMaskValue E hG.1 hf (sphereFromPlaneFunction Φ) L M.cutoff ∘ euclideanPlaneCoordinates) univ) := by
  obtain ⟨hφ,hφzero,L,hL⟩ := smooth_compact_sphere_scalar hΦ hs
  obtain ⟨hb,hb2⟩ := D.smooth_selected_scalar_finite_energy hG.1 hH.1 hinf hf hfix hΦ hs
  refine ⟨L,fun m => ?_⟩
  obtain ⟨M⟩ := E.exists_real_mask hmax hG hinf hf hfix hH hinf' hrem hφ hL hφzero m
  exact ⟨M,M.global_sobolev_of_published_inputs hsolver hprincipal hsob hcross hplane hcoarea hLusin
    hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hinf hb hb2⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceIntervalPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interval payment kills the compressed trace on a null subset of a
line. Countable local covers and tail compression then recover the full
uncompressed trace, including noninjective compressions. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem real_null_image_of_interval_payment
    (κ : Measure ℝ) [IsFiniteMeasure κ] [κ.OuterRegular]
    {C V : Set ℝ} (hV : IsOpen V) (hC : κ (C ∩ V) = 0) (v : ℝ → ℝ)
    (hpay : ∀ x ∈ C ∩ V, ∀ y ∈ C ∩ V, x ≤ y → Icc x y ⊆ V →
      |v y-v x| ≤ κ.real (Icc x y)) : volume (v '' (C ∩ V)) = 0 := by
  apply null_image_inter_open_of_connected_open_oscillation hV hC v zero_le_one
  intro U hUV _ hU x hx y hy
  have hforward (x : ℝ) (hx : x ∈ C ∩ U) (y : ℝ) (hy : y ∈ C ∩ U) (hxy : x ≤ y) :
      |v y-v x| ≤ κ.real U := by
    have hi : Icc x y ⊆ U := hU.isPreconnected.ordConnected.out hx.2 hy.2
    exact (hpay x ⟨hx.1,hUV hx.2⟩ y ⟨hy.1,hUV hy.2⟩ hxy (hi.trans hUV)).trans
      (measureReal_mono hi)
  rw [one_mul]
  rcases le_total x y with h | h
  · simpa only [abs_sub_comm] using hforward x hx y hy h
  · exact hforward y hy x hx h

 theorem null_image_of_local_null_image
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {C : Set X} {v : X → ℝ}
    (hlocal : ∀ x ∈ C, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ volume (v '' (C ∩ V)) = 0) :
    volume (v '' C) = 0 := by
  classical
  choose V hV hxV hn using (fun x : C => hlocal x x.property)
  obtain ⟨S,hSc,hS⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  let : Countable S := hSc.to_subtype
  have hc : v '' C ⊆ ⋃ x : S, v '' (C ∩ V x.val) := by
    rintro _ ⟨x,hx,rfl⟩
    have hxc : x ∈ ⋃ i ∈ S, V i := by rw [hS]; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hxc
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,x,⟨hx,hxi⟩,rfl⟩
  exact measure_mono_null hc (measure_iUnion_null (fun x : S => hn x.val))

 theorem compression_comparison {X : Type*} (F : X → ℝ → ℝ) (b : X → ℝ)
    (H : ℝ → ℝ) (hH : Monotone H) {x y : X} {c : ℝ}
    (hinc : ∀ z s t, s ≤ t → H t-H s ≤ F z t-F z s)
    (hvar : ∀ t, |F x t-F y t| ≤ c) :
    |H (b x)-H (b y)| ≤ |F x (b x)-F y (b y)|+c := by
  rcases le_total (b x) (b y) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (hH h))]
    have hi := hinc x (b x) (b y) h
    have hv := (le_abs_self (F x (b y)-F y (b y))).trans (hvar (b y))
    have hu := neg_le_abs (F x (b x)-F y (b y))
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (hH h))]
    have hi := hinc y (b y) (b x) h
    have hv := (neg_le_abs (F x (b x)-F y (b x))).trans (hvar (b x))
    have hu := le_abs_self (F x (b x)-F y (b y))
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceCompressionPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An inactive prefix lets scalar tail compression be compared with the
actual infinite mask. The spatial payment is valid across all component
types; continuity of the unmasked scalar is not required. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem infiniteTraceMask_eq_one {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ} {x : X} {t : ℝ}
    (h : ∀ j, t ∈ I j → cutoff j x = 1) : infiniteTraceMask cutoff I x t = 1 := by
  apply tendsto_nhds_unique (finiteTraceMask_tendsto hc I x t)
  exact tendsto_const_nhds.congr' (Eventually.of_forall (fun n =>
    (finiteTraceMask_eq_one (fun j _ => h j)).symm))

 theorem traceCompression_increment_le {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) {E : Set ℝ} (hE : MeasurableSet E)
    (x : X) (hactive : ∀ j t, t ∈ I j → t ∉ E → cutoff j x = 1)
    (a : ℝ) {s t : ℝ} (hst : s ≤ t) :
    traceCompression E a t-traceCompression E a s ≤
      infiniteTracePrimitive cutoff I a x t-infiniteTracePrimitive cutoff I a x s := by
  rw [traceCompression_sub hE]
  rw [infiniteTracePrimitive,infiniteTracePrimitive,
    intervalIntegral.integral_interval_sub_left
      (infiniteTraceMask_intervalIntegrable hc hI x a t)
      (infiniteTraceMask_intervalIntegrable hc hI x a s)]
  apply intervalIntegral.integral_mono_on hst
    (traceCompression_intervalIntegrable hE s t)
    (infiniteTraceMask_intervalIntegrable hc hI x s t)
  intro u _
  by_cases hu : u ∈ E
  · rw [indicator_of_notMem (show u ∉ Eᶜ from fun h => h hu) _]
    exact (infiniteTraceMask_bounds hc I x u).1
  · rw [indicator_of_mem hu _,infiniteTraceMask_eq_one hc (fun j hj => hactive j u hj hu)]

 theorem masked_trace_compression_payment {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) {E : Set ℝ} (hE : MeasurableSet E)
    {V : Set X} (hactive : ∀ z ∈ V, ∀ j t, t ∈ I j → t ∉ E → cutoff j z = 1)
    (a : ℝ) (b : X → ℝ) {x y : X} (hx : x ∈ V) (hy : y ∈ V) {p : ℝ}
    (hpay : ∀ t, |infiniteTracePrimitive cutoff I a x t-
      infiniteTracePrimitive cutoff I a y t| ≤ p) :
    |traceCompression E a (b x)-traceCompression E a (b y)| ≤
      |infiniteTracePrimitive cutoff I a x (b x)-
        infiniteTracePrimitive cutoff I a y (b y)|+p := by
  let F : V → ℝ → ℝ := fun z => infiniteTracePrimitive cutoff I a z.val
  let B : V → ℝ := fun z => b z.val
  exact compression_comparison F B (traceCompression E a) (traceCompression_monotone hE a)
    (fun z _ _ hst => traceCompression_increment_le hc hI hE z.val
      (hactive z z.property) a hst) (x := ⟨x,hx⟩) (y := ⟨y,hy⟩) hpay

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceIntegralNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A locally integrable line payment kills the outer length of the
image of a null set. Measurability of that image is unnecessary. This
also assembles the local compressed traces for all vanishing tails. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem real_null_image_of_integrable_payment {C V : Set ℝ}
    (hV : IsOpen V) (hC : volume C = 0) (v : ℝ → ℝ)
    {g : ℝ → ℝ} (hg : Integrable g volume) (hgn : ∀ᵐ x ∂volume, 0 ≤ g x)
    (hpay : ∀ x ∈ C ∩ V, ∀ y ∈ C ∩ V, x ≤ y → Icc x y ⊆ V →
      |v y-v x| ≤ ∫ t in Icc x y, g t) : volume (v '' (C ∩ V)) = 0 := by
  let κ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (g x))
  let : IsFiniteMeasure κ := ⟨by
    change volume.withDensity (fun x => ENNReal.ofReal (g x)) univ < ∞
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hg hgn]
    exact ENNReal.ofReal_lt_top⟩
  have hκ : κ (C ∩ V) = 0 :=
    withDensity_absolutelyContinuous volume _ (measure_mono_null inter_subset_left hC)
  apply real_null_image_of_interval_payment κ hV hκ v
  intro x hx y hy hxy hi
  apply (hpay x hx y hy hxy hi).trans_eq
  change (∫ t in Icc x y, g t) = (volume.withDensity (fun x => ENNReal.ofReal (g x)) (Icc x y)).toReal
  rw [withDensity_apply _ measurableSet_Icc]
  exact integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hgn) hg.restrict.aestronglyMeasurable

 theorem null_of_local_compressed_integral_payments {C : Set ℝ}
    (hC : volume C = 0) (b : ℝ → ℝ) {E : ℕ → Set ℝ}
    (hE : ∀ n, MeasurableSet (E n)) (a : ℝ)
    (htail : Tendsto (fun n => volume (E n)) atTop (𝓝 0))
    (hlocal : ∀ n x, x ∈ C → ∃ V : Set ℝ, IsOpen V ∧ x ∈ V ∧
      ∃ g : ℝ → ℝ, Integrable g volume ∧ (∀ᵐ t ∂volume, 0 ≤ g t) ∧
        ∀ y ∈ C ∩ V, ∀ z ∈ C ∩ V, y ≤ z → Icc y z ⊆ V →
          |traceCompression (E n) a (b z)-traceCompression (E n) a (b y)| ≤
            ∫ t in Icc y z, g t) : volume (b '' C) = 0 := by
  apply null_of_tail_compressions hE a _ htail
  intro n
  rw [image_image]
  apply null_image_of_local_null_image
  intro x hx
  obtain ⟨V,hV,hxV,g,hg,hgn,hpay⟩ := hlocal n x hx
  exact ⟨V,hV,hxV,real_null_image_of_integrable_payment hV hC
    (fun y => traceCompression (E n) a (b y)) hg hgn hpay⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceLineTails
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tonelli's theorem selects lines with finite total interval cost.
The union of the remaining active intervals consequently has vanishing
outer length. Overlaps between the intervals require no disjointness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem ae_finite_line_incidence {A : ℕ → Set ℝ}
    (hA : ∀ j, MeasurableSet (A j)) (a : ℕ → ℝ≥0∞)
    (hsum : (∑' j, a j * volume (A j)) ≠ ∞) :
    ∀ᵐ t ∂volume, (∑' j, (A j).indicator (fun _ => a j) t) < ∞ := by
  have hm (j : ℕ) : Measurable ((A j).indicator (fun _ : ℝ => a j)) :=
    measurable_const.indicator (hA j)
  apply ae_lt_top (Measurable.tsum hm)
  rw [lintegral_tsum (fun j => (hm j).aemeasurable)]
  simpa only [lintegral_indicator (hA _),lintegral_const,Measure.restrict_apply_univ] using hsum

 theorem lineTailIntervals_measurable {I A : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (t : ℝ) (N : ℕ) :
    MeasurableSet (lineTailIntervals I A t N) := by
  apply MeasurableSet.iUnion
  intro k
  split_ifs
  · exact hI _
  · exact MeasurableSet.empty

 theorem lineTailIntervals_volume_tendsto {I A : ℕ → Set ℝ} {t : ℝ}
    (hfinite : (∑' j, (A j).indicator (fun _ => volume (I j)) t) ≠ ∞) :
    Tendsto (fun N => volume (lineTailIntervals I A t N)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add _ hfinite) (fun _ => bot_le)
  intro N
  apply (measure_iUnion_le _).trans
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases ht : t ∈ A (k+N)
  · simp [ht]
  · simp [ht]

 theorem ae_lineTailIntervals_volume_tendsto {I A : ℕ → Set ℝ}
    (hA : ∀ j, MeasurableSet (A j))
    (hsum : (∑' j, volume (I j)*volume (A j)) ≠ ∞) :
    ∀ᵐ t ∂volume, Tendsto (fun N => volume (lineTailIntervals I A t N)) atTop (𝓝 0) := by
  filter_upwards [ae_finite_line_incidence hA (fun j => volume (I j)) hsum] with t ht
  exact lineTailIntervals_volume_tendsto ht.ne

/-- Square-summable interval lengths and balloon radii pay for almost
all transverse lines. The center positions are unrestricted. -/
 theorem ae_balloon_line_tails {I : ℕ → Set ℝ} {d : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (c : ℕ → ℝ)
    (hI : ∀ j, volume (I j) ≠ ∞)
    (hIsq : Summable (fun j => volume.real (I j)^2))
    (hdsq : Summable (fun j => d j^2)) :
    ∀ᵐ t ∂volume, Tendsto (fun N => volume
      (lineTailIntervals I (fun j => Ioo (c j-d j) (c j+d j)) t N)) atTop (𝓝 0) := by
  apply ae_lineTailIntervals_volume_tendsto (fun _ => measurableSet_Ioo)
  have hs := (LengthArea.summable_mul_of_squares hIsq hdsq).mul_right 2
  have he (j : ℕ) : volume (I j)*volume (Ioo (c j-d j) (c j+d j)) =
      ENNReal.ofReal (volume.real (I j)*d j*2) := by
    simp only [measureReal_def]
    rw [Real.volume_Ioo,show c j+d j-(c j-d j) = d j*2 by ring,
      ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (hd j)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (hI j),
      ENNReal.ofReal_mul (hd j),mul_assoc]
  simpa only [he] using hs.tsum_ofReal_ne_top

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2Series
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise sum of the cutoff differential norms is itself in L2,
with the sum of their L2 norms as a bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem l2_series_of_summable_norms {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (g : ℕ → X → ℝ)
    (hg : ∀ n, MemLp (g n) 2 μ)
    (hs : Summable (fun n => (eLpNorm (g n) 2 μ).toReal)) :
    MemLp (fun z => ∑' n, g n z) 2 μ ∧
      (eLpNorm (fun z => ∑' n, g n z) 2 μ).toReal ≤
        ∑' n, (eLpNorm (g n) 2 μ).toReal := by
  let F : ℕ → Lp ℝ 2 μ := fun n => (hg n).toLp (g n)
  have hnorm : Summable (fun n => ‖F n‖) := by
    simpa only [F, Lp.norm_toLp] using hs
  have hfinite : (∑' n, ‖F n‖ₑ) ≠ (⊤ : ℝ≥0∞) := by
    have hh := hs.tsum_ofReal_lt_top
    have he (n : ℕ) : ENNReal.ofReal (eLpNorm (g n) 2 μ).toReal = eLpNorm (g n) 2 μ :=
      ENNReal.ofReal_toReal (hg n).eLpNorm_ne_top
    simp_rw [he] at hh
    simpa only [F, Lp.enorm_toLp] using hh.ne
  have hvalues : ∀ᵐ z ∂μ, ∀ n, F n z = g n z :=
    ae_all_iff.mpr (fun n => (hg n).coeFn_toLp)
  have hae : (⇑(∑' n, F n) : X → ℝ) =ᵐ[μ] (fun z => ∑' n, g n z) := by
    filter_upwards [Lp.coeFn_tsum hfinite, hvalues] with z hz hv
    rw [hz]
    exact tsum_congr hv
  refine ⟨(Lp.memLp (∑' n, F n)).ae_eq hae, ?_⟩
  rw [← eLpNorm_congr_ae hae, ← Lp.norm_def]
  simpa only [F, Lp.norm_toLp] using norm_tsum_le_tsum_norm hnorm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2DominatingSubsequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L² convergence admits a cofinal subsequence with one L²
pointwise majorant. This will pass smooth line payments to a continuous
Sobolev limit without assuming an ACL representative theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_L2_dominating_subsequence {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 2 μ) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (P : X → ℝ), Tendsto σ atTop atTop ∧ Measurable P ∧
      (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧ (∀ᵐ x ∂μ, ∀ n, |f (σ n) x| ≤ P x) := by
  let δ := fun n : ℕ => (1/2:ℝ)^n
  have hδ (n : ℕ) : 0 < δ n := pow_pos (by norm_num) n
  have hδs : Summable δ := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun n => (eLpNorm (fun x => f n x-g x) 2 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp hlim
  have hchoose (n : ℕ) : ∃ k, n ≤ k ∧ (eLpNorm (fun x => f k x-g x) 2 μ).toReal ≤ δ n := by
    obtain ⟨k,hk,hke⟩ := ((eventually_ge_atTop n).and (ht.eventually (gt_mem_nhds (hδ n)))).exists
    exact ⟨k,hk,hke.le⟩
  choose σ hσ hb using hchoose
  have hσt : Tendsto σ atTop atTop := tendsto_atTop_mono hσ tendsto_id
  let e := fun n x => f (σ n) x-g x
  have he (n : ℕ) : MemLp (e n) 2 μ := (hf _).sub hg
  have hes : Summable (fun n => (eLpNorm (e n) 2 μ).toReal) :=
    hδs.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) hb
  have hef : (∑' n, eLpNorm (e n) 2 μ) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) hδs.tsum_ofReal_lt_top
    rw [← ENNReal.ofReal_toReal (he n).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hser := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 2) (fun n => (he n).1) hef
  have hn : Summable (fun n => (eLpNorm (fun x => ‖e n x‖) 2 μ).toReal) := by
    simpa only [eLpNorm_norm _] using hes
  have hsum := (l2_series_of_summable_norms (fun n x => ‖e n x‖) (fun n => (he n).norm) hn).1
  let Q := fun x => ‖g x‖+∑' n, ‖e n x‖
  have hQ : MemLp Q 2 μ := hg.norm.add hsum
  have hQ0 (x : X) : 0 ≤ Q x := add_nonneg (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _))
  let P := fun x => max (hQ.aestronglyMeasurable.mk Q x) 0
  have hPQ : P =ᵐ[μ] Q := by
    filter_upwards [hQ.aestronglyMeasurable.ae_eq_mk] with x hx
    change max (hQ.aestronglyMeasurable.mk Q x) 0 = Q x
    rw [← hx,max_eq_left (hQ0 x)]
  refine ⟨σ,P,hσt,hQ.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const,
    (fun _ => le_max_right _ _),hQ.ae_eq hPQ.symm,?_⟩
  filter_upwards [hPQ,hser] with x hx hxs
  intro n
  rw [hx]
  have heq : f (σ n) x = g x+e n x := by dsimp only [e] <;> ring
  calc
    _ = ‖f (σ n) x‖ := Real.norm_eq_abs _ |>.symm
    _ ≤ ‖g x‖+‖e n x‖ := by rw [heq]; exact norm_add_le _ _
    _ ≤ Q x := by
      dsimp only [Q]
      exact add_le_add_right (hxs.le_tsum n (fun _ _ => norm_nonneg _)) _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevTypicalLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous compact Sobolev function admits an actual L² payment
for all intervals on almost every coordinate line. Strong mollification
and a summably convergent subsequence supply the payment. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_line_increment_payment_ae {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {x y : ℝ}
    (hg : IntervalIntegrable g volume x y)
    (hb : ∀ᵐ t ∂volume, |deriv f t| ≤ g t) :
    |f x-f y| ≤ ∫ t in uIoc x y, g t := by
  have hi : IntervalIntegrable (deriv f) volume x y :=
    hf.continuous_deriv_one.intervalIntegrable x y
  have he := intervalIntegral.integral_deriv_eq_sub
    (fun z (_ : z ∈ uIcc y x) => hf.differentiable_one z) hi.symm
  rw [← he,← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  rw [uIoc_comm y x]
  apply integral_mono_ae hi.norm.def' hg.def'
  exact ae_restrict_of_ae hb

 theorem sobolev_typical_line_payment {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∃ P : EuclideanPlane → ℝ, Measurable P ∧ (∀ z, 0 ≤ P z) ∧ MemLp P 2 volume ∧
      ∀ᵐ y ∂volume, LocallyIntegrable (fun t => P (physicalCoordinateLine i y t)) volume ∧
        ∀ x z : ℝ, |u (physicalCoordinateLine i y x)-u (physicalCoordinateLine i y z)| ≤
          ∫ t in uIoc x z, P (physicalCoordinateLine i y t) := by
  have hg : MemLp (fun x => W.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
  obtain ⟨σ,P,hσ,hP,hP0,hPL,hdom⟩ := exists_L2_dominating_subsequence
    (fun n => planarMollification_partial_memLp W hs n i) hg
    (planarMollification_tendsto_gradient_L2 W i)
  refine ⟨P,hP,hP0,hPL,?_⟩
  filter_upwards [memLp_physicalCoordinateLine_ae hP hPL i,
    ae_ae_physicalCoordinateLine hdom i] with y hy hd
  have hloc := hy.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨hloc,fun x z => ?_⟩
  have hpay (n : ℕ) :
      |planarMollification u (σ n) (physicalCoordinateLine i y x)-
       planarMollification u (σ n) (physicalCoordinateLine i y z)| ≤
        ∫ t in uIoc x z, P (physicalCoordinateLine i y t) := by
    have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using W.memLp
    have hf : ContDiff ℝ 1 (planarMollification u (σ n)) :=
      (planarMollification_smooth (huL.locallyIntegrable (by norm_num)) (σ n)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    apply smooth_line_increment_payment_ae (hf.comp ((physicalCoordinateLine_contDiff i y).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))
      (intervalIntegrable_iff.mpr ((hloc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc))
    filter_upwards [hd] with t ht
    simpa only [Function.comp_def,physicalCoordinateLine_deriv hf] using ht n
  exact le_of_tendsto (((planarMollification_tendsto_of_continuous hu _).comp hσ).sub
    ((planarMollification_tendsto_of_continuous hu _).comp hσ)).abs (Eventually.of_forall hpay)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedLineNullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local inactivity of each finite prefix, vanishing active tails and
actual line payments force the unmasked trace of a null set to be null. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem null_image_of_masked_line_payments
    {C : Set ℝ} (hC : volume C = 0) (b : ℝ → ℝ)
    {I A : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j))
    (hIf : ∀ j, volume (I j) ≠ ∞) (τ : ℝ)
    (htail : Tendsto (fun N => volume (lineTailIntervals I A τ N)) atTop (𝓝 0))
    (cut : ℕ → ℕ → ℝ → ℝ) (hc : ∀ m j, ContDiff ℝ 1 (cut m j))
    (hunit : ∀ m j x, cut m j x ∈ Icc (0:ℝ) 1)
    (P Q : ℕ → ℝ → ℝ)
    (hPloc : ∀ m, LocallyIntegrable (P m) volume)
    (hQloc : ∀ m, LocallyIntegrable (Q m) volume)
    (hP0 : ∀ m t, 0 ≤ P m t) (hQ0 : ∀ m t, 0 ≤ Q m t)
    (hdom : ∀ m, ∀ᵐ t ∂volume, ∀ n, ∑ j ∈ Finset.range n,
      volume.real (I j)*|deriv (cut m j) t| ≤ P m t)
    (hpay : ∀ m x y, |infiniteTracePrimitive (cut m) I 0 x (b x)-
      infiniteTracePrimitive (cut m) I 0 y (b y)| ≤ ∫ t in uIoc x y, Q m t)
    (houter : ∀ m j, τ ∉ A j → ∀ x, cut m j x = 1)
    (hprefix : ∀ N x, x ∈ C → ∃ m V, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ j < N, cut m j y = 1) : volume (b '' C) = 0 := by
  classical
  apply null_of_local_compressed_integral_payments hC b
    (fun N => lineTailIntervals_measurable hI τ N) 0 htail
  intro N x hx
  obtain ⟨m,V,hV,hxV,hpre⟩ := hprefix N x hx
  let J := Ioo (x-1) (x+1)
  let K := Icc (x-1) (x+1)
  let g := K.indicator (fun t => Q m t+P m t)
  have hK : MeasurableSet K := measurableSet_Icc
  have hg : Integrable g volume :=
    (integrable_indicator_iff hK).mpr (((hQloc m).add (hPloc m)).integrableOn_isCompact isCompact_Icc)
  refine ⟨V ∩ J,hV.inter isOpen_Ioo,⟨hxV,by dsimp only [J]; constructor <;> linarith⟩,
    g,hg,Eventually.of_forall (fun t => ?_),?_⟩
  · exact indicator_nonneg (fun t _ => add_nonneg (hQ0 m t) (hP0 m t)) _
  intro y hy z hz hyz _
  have hactive : ∀ w ∈ V, ∀ j t, t ∈ I j → t ∉ lineTailIntervals I A τ N → cut m j w = 1 := by
    intro w hw j t ht hnot
    by_cases hj : j < N
    · exact hpre w hw j hj
    by_cases hτ : τ ∈ A j
    · exfalso
      apply hnot
      apply mem_iUnion.mpr
      refine ⟨j-N,?_⟩
      simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt hj),ite_eq_left hτ] using ht
    · exact houter m j hτ w
  have hPint : IntervalIntegrable (P m) volume y z :=
    intervalIntegrable_iff.mpr (((hPloc m).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hQint : IntervalIntegrable (Q m) volume y z :=
    intervalIntegrable_iff.mpr (((hQloc m).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hsp (t : ℝ) : |infiniteTracePrimitive (cut m) I 0 y t-
      infiniteTracePrimitive (cut m) I 0 z t| ≤ ∫ s in uIoc y z, P m s := by
    apply trace_primitive_line_payment_ae (hunit m) hI hIf
      (fun j => (hc m j).continuous_deriv_one.abs.intervalIntegrable y z) hPint
      (fun j a _ d _ => smooth_line_increment_payment_ae (hc m j)
        ((hc m j).continuous_deriv_one.abs.intervalIntegrable a d)
        (Eventually.of_forall (fun _ => le_rfl)))
      (fun n => ae_restrict_of_ae ((hdom m).mono (fun _ ht => ht n))) 0 t
      (left_mem_uIcc) (right_mem_uIcc)
  have hp := masked_trace_compression_payment (hunit m) hI
    (lineTailIntervals_measurable hI τ N) hactive 0 b hy.2.1 hz.2.1 hsp
  have hp' : |traceCompression (lineTailIntervals I A τ N) 0 (b z)-
      traceCompression (lineTailIntervals I A τ N) 0 (b y)| ≤
      ∫ t in Icc y z, Q m t+P m t := by
    rw [abs_sub_comm]
    apply hp.trans
    apply (add_le_add (hpay m y z) le_rfl).trans_eq
    rw [← integral_add hQint.def' hPint.def',uIoc_of_le hyz,← integral_Icc_eq_integral_Ioc]
  apply hp'.trans_eq
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only [g]
  rw [indicator_of_mem]
  constructor
  · exact le_trans (show x-1 ≤ y from hy.2.2.1.le) ht.1
  · exact le_trans ht.2 (show z ≤ x+1 from hz.2.2.2.le)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedMaskLineNull
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global Sobolev masks imply null scalar traces on the
common point set. Every parameter comes from the matched disks and the
constructed masks; finite-prefix inactivity is proved from their radii. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.commonPoint_trace_null_of_masks (E : D.MatchedRoundDisks)
    (hprincipal : PrincipalRealBeltrami)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G)) (φ : Sphere → ℝ) (L : ℝ≥0)
    (M : ∀ m, MatchedRealMask E hG.1 hf φ L m)
    (W : ∀ m, DeGiorgi.MemW1pWitness 2
      (D.realMaskValue E hG.1 hf φ L (M m).cutoff ∘ euclideanPlaneCoordinates) univ)
    (i : Fin 2) :
    ∀ᵐ y ∂volume, volume ((fun x => D.realSelectedScalar hG.1 hf φ (realCoordinateLine i y x)) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0 := by
  let I := E.traceInterval hG.1 hf φ L
  let A := fun j => Ioo (transverseCoordinate i (E.traceCenter j)-traceBalloonRadius E.traceRadius 0 j)
    (transverseCoordinate i (E.traceCenter j)+traceBalloonRadius E.traceRadius 0 j)
  have hI (j : ℕ) : MeasurableSet (I j) := measurableSet_Ioo
  have hIf (j : ℕ) : volume (I j) ≠ ∞ := by
    dsimp only [I,MatchedRoundDisks.traceInterval]
    exact ne_of_lt measure_Ioo_lt_top
  have htail := ae_balloon_line_tails
    (fun j => (traceBalloonRadius_pos (r := E.traceRadius) 0 j).le)
    (fun j => transverseCoordinate i (E.traceCenter j)) hIf
    (E.traceInterval_summable_sq hG.1 hf φ L)
    (traceBalloonRadius_summable_sq (traceEnumeration_summable_sq E.source_summable) 0)
  have hq (m : ℕ) := sobolev_typical_line_payment
    ((M m).continuous.comp euclideanPlaneCoordinates.continuous)
    ((M m).compact.comp_homeomorph euclideanPlaneCoordinates.toHomeomorph) (W m) i
  choose Q hQ hQ0 hQL hQpay using hq
  have hp (m : ℕ) := memLp_realCoordinateLine_ae
    (M m).density_measurable (M m).density_memLp i
  have hd (m : ℕ) := ae_ae_realCoordinateLine (M m).pays i
  filter_upwards [D.commonPointPlane_line_null hprincipal hG hinf hf hH hinf' hrem i,
    htail,ae_all_iff.mpr hQpay,ae_all_iff.mpr hp,ae_all_iff.mpr hd] with y hnull ht hqline hpline hdline
  let C := {x | complexCoordinateLine i y x ∈ D.commonPointPlane ∧ complexCoordinateLine i y x ≠ 0}
  have hC : volume C = 0 := measure_mono_null (fun _ hx => hx.1) hnull
  have htrace : volume ((fun x => D.realSelectedScalar hG.1 hf φ (realCoordinateLine i y x)) '' C) = 0 := by
    apply null_image_of_masked_line_payments hC _ hI hIf y ht
      (fun m j x => (M m).cutoff j (realCoordinateLine i y x))
      (fun m j => ((M m).smooth j).comp ((realCoordinateLine_contDiff i y).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))
      (fun m j x => (M m).unit j _)
      (fun m t => (M m).density (realCoordinateLine i y t))
      (fun m t => Q m (physicalCoordinateLine i y t))
      (fun m => (hpline m).locallyIntegrable (by norm_num))
      (fun m => (hqline m).1)
      (fun m t => (M m).density_nonneg _) (fun m t => hQ0 m _)
    · intro m
      filter_upwards [hdline m] with t ht
      intro n
      apply le_trans _ (ht n)
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (realCoordinateLine_abs_deriv_le ((M m).smooth j) i y t) measureReal_nonneg
    · intro m x z
      convert (hqline m).2 x z using 1
      all_goals try with_reducible_and_instances rfl
      simp only [Function.comp_apply,realCoordinateLine_physical,realMaskValue,
        infiniteTracePrimitive_comp,I]
    · intro m j hy x
      apply (M m).outer
      apply (traceBalloonRadius_le_first m j).trans
      apply le_of_not_gt
      intro hlt
      apply hy
      have h := (complexCoordinateLine_transverse_le i y x (E.traceCenter j)).trans_lt hlt
      exact ⟨by linarith [(abs_lt.mp h).1],by linarith [(abs_lt.mp h).2]⟩
    · intro N x hx
      obtain ⟨m,V,hV,hxV,hpre⟩ := E.commonPoint_prefix_avoidance hx.1 hx.2 N
      refine ⟨m,(complexCoordinateLine i y) ⁻¹' V,?_,hxV,?_⟩
      · exact hV.preimage (Complex.equivRealProdCLM.symm.continuous.comp
          (realCoordinateLine_contDiff i y).continuous)
      · intro z hz j hj
        exact (M m).outer j _ (hpre _ hz j hj)
  have hextra : volume ((fun x => D.realSelectedScalar hG.1 hf φ (realCoordinateLine i y x)) ''
      {x | complexCoordinateLine i y x = 0}) = 0 := by
    apply measure_mono_null _ (measure_singleton (D.realSelectedScalar hG.1 hf φ (0,0)))
    rintro _ ⟨x,hx,rfl⟩
    apply mem_singleton_iff.mpr
    have he : realCoordinateLine i y x = (0,0) := by
      apply Complex.equivRealProdCLM.symm.injective
      exact hx
    exact congrArg (D.realSelectedScalar hG.1 hf φ) he
  apply measure_mono_null _ (measure_union_null htrace hextra)
  rintro _ ⟨x,hx,rfl⟩
  by_cases hz : complexCoordinateLine i y x = 0
  · exact Or.inr ⟨x,hz,rfl⟩
  · exact Or.inl ⟨x,⟨hx,hz⟩,rfl⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SmoothCommonPointTrace
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common point trace of every compact smooth target scalar is null
on almost every axial line, using only the recorded published inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 local instance localInst_r3452f0_2 : BorelSpace Sphere := ⟨rfl⟩
theorem MatchedRoundDisks.smooth_commonPoint_trace_null_of_published_inputs (E : D.MatchedRoundDisks)
    (hmax : PlanarMaximalL2)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G))
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    ∀ i : Fin 2, ∀ᵐ y ∂volume,
      volume ((fun x => D.realSelectedScalar hG.1 hf (sphereFromPlaneFunction Φ)
        (realCoordinateLine i y x)) '' {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0 := by
  obtain ⟨L,hM⟩ := E.exists_global_smooth_masks hmax hsolver hprincipal hsob hcross hplane hcoarea hLusin
    hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hG hinf hf hfix hH hinf' hrem hΦ hs
  choose M hW using hM
  let W := fun m => Classical.choice (hW m)
  exact fun i => E.commonPoint_trace_null_of_masks hprincipal hG hinf hf hH hinf' hrem
    (sphereFromPlaneFunction Φ) L M W i

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactCoordinateTest
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An axial coordinate on a bounded sphere complement can be represented
by a smooth compact planar test. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_71
theorem exists_smooth_compact_coordinate_test {H : Set Sphere}
    (hH : IsOpen H) (hinf : OnePoint.infty ∈ H) (i : Fin 2) :
    ∃ Φ : EuclideanPlane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      ∀ z : ℂ, (z : Sphere) ∈ Hᶜ →
        sphereFromPlaneFunction Φ (z : Sphere) = (complexPlaneCoordinates.symm z) i := by
  have hK : IsCompact (physicalPlaneDomain H)ᶜ := by
    have hh := (isCompact_finite_preimage hH.isClosed_compl (not_not.mpr hinf)).image
      complexPlaneCoordinates.symm.continuous
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_compl_iff,physicalPlaneDomain,mem_preimage,mem_image]
    constructor
    · intro hx
      exact ⟨complexPlaneCoordinates x,hx,complexPlaneCoordinates.symm_apply_apply x⟩
    · rintro ⟨z,hz,rfl⟩
      simpa only [planeSphere,ContinuousLinearEquiv.apply_symm_apply] using hz
  obtain ⟨η,V,hη,hsη,_,_,_,hKV,hηV⟩ :=
    exists_smooth_compact_cutoff_one_near hK isOpen_univ (subset_univ _)
  refine ⟨(fun x => η x*x i),hη.mul (by fun_prop),hsη.mul_right,?_⟩
  intro z hz
  rw [sphereFromPlaneFunction_coe]
  have hx : complexPlaneCoordinates.symm z ∈ (physicalPlaneDomain H)ᶜ := by
    simpa only [mem_compl_iff,physicalPlaneDomain,mem_preimage,planeSphere,
      ContinuousLinearEquiv.apply_symm_apply] using hz
  rw [hηV _ (hKV hx),one_mul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedCoordinateTest
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact scalar test recovers each actual finite target coordinate
on all source complementary components. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_72
theorem selectedTarget_outside (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q : Sphere} (hq : q ∈ Gᶜ) :
    D.selectedTarget hG hf q ∈ (f '' G)ᶜ := by
  obtain ⟨p,_,he⟩ := D.componentRelation_source_fiber hG hf hq
  have hm : D.selectedTarget hG hf q ∈ {p' | D.componentRelation q p'} :=
    D.selectedTarget_mem hG hf q
  rw [he] at hm
  exact connectedComponentIn_subset _ _ hm

 theorem exists_smooth_selected_coordinate_test
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsOpen (f '' G)) (hinf' : OnePoint.infty ∈ f '' G) (k : Fin 2) :
    ∃ Φ : EuclideanPlane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      ∀ z : ℂ, (z : Sphere) ∈ Gᶜ →
        D.realSelectedScalar hG hf (sphereFromPlaneFunction Φ) (Complex.equivRealProdCLM z) =
          (complexPlaneCoordinates.symm (finiteCoord (D.selectedTarget hG hf (z : Sphere)))) k := by
  obtain ⟨Φ,hΦ,hs,hcoord⟩ := exists_smooth_compact_coordinate_test hH hinf' k
  refine ⟨Φ,hΦ,hs,?_⟩
  intro z hz
  have hp := D.selectedTarget_outside hG hf hz
  unfold realSelectedScalar
  rw [ContinuousLinearEquiv.symm_apply_apply]
  generalize hq : D.selectedTarget hG hf (z : Sphere) = q at hp ⊢
  cases q using OnePoint.rec with
  | infty => exact (hp hinf').elim
  | coe w => simpa only [finiteCoord_coe] using hcoord w hp

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialCommonPointTrace
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact four axial trace conclusions for the singleton-to-singleton
part of the matched correspondence, from the recorded published inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_78
theorem MatchedRoundDisks.axial_commonPoint_trace_null_of_published_inputs (E : D.MatchedRoundDisks)
    (hmax : PlanarMaximalL2)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G)) :
    ∀ i k : Fin 2, ∀ᵐ y ∂volume,
      volume ((fun x => (complexPlaneCoordinates.symm (finiteCoord
        (D.selectedTarget hG.1 hf (complexCoordinateLine i y x : Sphere)))) k) ''
        {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0 := by
  intro i k
  obtain ⟨Φ,hΦ,hs,hcoord⟩ := D.exists_smooth_selected_coordinate_test hG.1 hf hH.1 hinf' k
  have ht := E.smooth_commonPoint_trace_null_of_published_inputs hmax hsolver hprincipal hsob hcross
    hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite
    hmontel hhurwitz hzero harcs hstandard hpath hdual hlift hG hinf hf hfix hH hinf' hrem hΦ hs i
  filter_upwards [ht] with y hy
  have he : ((fun x => (complexPlaneCoordinates.symm (finiteCoord
        (D.selectedTarget hG.1 hf (complexCoordinateLine i y x : Sphere)))) k) ''
        {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) =
      ((fun x => D.realSelectedScalar hG.1 hf (sphereFromPlaneFunction Φ)
        (realCoordinateLine i y x)) '' {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) := by
    apply image_congr
    intro x hx
    have hh := hcoord (complexCoordinateLine i y x) hx.1
    simpa only [complexCoordinateLine,ContinuousLinearEquiv.apply_symm_apply] using hh.symm
  rw [he]
  exact hy

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConditionalNormalizedRigidity
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Principal normalized rigidity from exactly the recorded published inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_79
theorem normalized_identity_of_published_inputs
    (hmax : PlanarMaximalL2)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hareaBound : ExteriorOmittedAreaTheorem)
    {G : Set Sphere} {f : Sphere → Sphere}
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hnorm : IsPrincipalNormalized f)
    (hH : IsCircleDomain (f '' G)) (hrem : IsConformallyRemovable (frontier G)) :
    ∀ p ∈ G, f p = p := by
  classical
  obtain ⟨D⟩ := exists_matched_conformal_ends hsard hsch hG.1 hG.2.1 hinf hf hnorm.1
  let : Countable D.IndexedMatchedPair := D.indexedMatchedPair_countable hG.1 hf
  let : Encodable D.IndexedMatchedPair := Encodable.ofCountable _
  have hinf' : OnePoint.infty ∈ f '' G := hnorm.1 ▸ mem_image_of_mem f hinf
  obtain ⟨E⟩ := D.exists_matched_round_disks hG hinf hf hH hinf'
  have ht := E.axial_commonPoint_trace_null_of_published_inputs hmax hsolver hprincipal hsob hcross
    hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite
    hmontel hhurwitz hzero harcs hstandard hpath hdual hlift hG hinf hf hnorm.1 hH hinf' hrem
  exact D.normalized_identity_of_trace hareaBound E hG hinf hf hnorm hH (fun i => ht i i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RemovabilityMobiusTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugating the test homeomorphisms transports conformal removability
through a conformal Möbius homeomorphism. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem orientationPreserving_conjugate (e H : Sphere ≃ₜ Sphere)
    (hH : OrientationPreserving H) : OrientationPreserving ((e.trans H).trans e.symm) := by
  have hh := (ContinuousMap.Homotopic.refl (⟨e.symm,e.symm.continuous⟩ : C(Sphere,Sphere))).comp
    (hH.comp (ContinuousMap.Homotopic.refl (⟨e,e.continuous⟩ : C(Sphere,Sphere))))
  have hi : (⟨e.symm,e.symm.continuous⟩ : C(Sphere,Sphere)).comp
      ((ContinuousMap.id Sphere).comp (⟨e,e.continuous⟩ : C(Sphere,Sphere))) =
        ContinuousMap.id Sphere := by
    ext p
    exact e.symm_apply_apply p
  rw [hi] at hh
  exact hh

 theorem IsConformallyRemovable.image_mobius {E : Set Sphere}
    (hE : IsConformallyRemovable E) (M : Mobius) (e : Sphere ≃ₜ Sphere)
    (hM : ∀ p, e p = M • p)
    (he : ∀ p, IsConformalAt e p) (hi : ∀ p, IsConformalAt e.symm p) :
    IsConformallyRemovable (e '' E) := by
  refine ⟨hE.1.image e.continuous,?_⟩
  intro H hor hconf
  let K := (e.trans H).trans e.symm
  have hKconf : IsConformalOn K Eᶜ := by
    intro p hp
    have hpe : e p ∈ (e '' E)ᶜ := by
      rintro ⟨q,hq,heq⟩
      exact hp ((e.injective heq) ▸ hq)
    have hinner : IsConformalAt (H ∘ e) p := (hconf (e p) hpe).comp (he p)
    exact IsConformalAt.comp (f := H ∘ e) (g := e.symm) (hi (H (e p))) hinner
  obtain ⟨N,hN⟩ := hE.2 K (orientationPreserving_conjugate e H hor) hKconf
  refine ⟨M*N*M⁻¹,?_⟩
  intro q
  have h := congrArg e (hN (e.symm q))
  change e (e.symm (H (e (e.symm q)))) = e (N • e.symm q) at h
  simp only [e.apply_symm_apply] at h
  have hinv : e.symm q = M⁻¹ • q := by
    apply e.injective
    rw [e.apply_symm_apply,hM]
    simp
  rw [hM,hinv] at h
  simpa only [mul_smul] using h

 theorem IsConformallyRemovable.frontier_pointToInfinity {G : Set Sphere}
    (hG : IsConformallyRemovable (frontier G)) (p : Sphere) :
    IsConformallyRemovable (frontier (pointToInfinity p '' G)) := by
  rw [← (pointToInfinity p).image_frontier]
  exact hG.image_mobius (pointToInfinityMobius p) (pointToInfinity p)
    (pointToInfinity_eq_smul p) (isConformalAt_pointToInfinity p)
    (isConformalAt_pointToInfinity_symm p)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RigidityNormalizationReduction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The principal identity statement implies the exact, unnormalized
removability-to-rigidity statement. All normalizers are explicit Möbius maps. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem circleDomainRemovabilityRigidity_of_principal_identity
    (hidentity : ∀ {G : Set Sphere} {f : Sphere → Sphere}, IsCircleDomain G →
      OnePoint.infty ∈ G → IsConformalEquivalence f G (f '' G) →
      IsPrincipalNormalized f → IsCircleDomain (f '' G) →
      IsConformallyRemovable (frontier G) → ∀ p ∈ G, f p = p) :
    CircleDomainRemovabilityRigidity := by
  intro U V f hU hV hrem hf
  obtain ⟨p,hp⟩ := hU.2.1.nonempty
  let A := pointToInfinity p
  let B := pointToInfinity (f p)
  let U' := A '' U
  have hA : IsConformalEquivalence A.symm U' U := by
    refine ⟨fun q _ => isConformalAt_pointToInfinity_symm p q,?_,A,
      fun q _ => isConformalAt_pointToInfinity p q,?_,?_,?_⟩
    · rintro q ⟨x,hx,rfl⟩
      simpa only [A.symm_apply_apply] using hx
    · exact mapsTo_image _ _
    · exact fun q _ => A.apply_symm_apply q
    · exact fun q _ => A.symm_apply_apply q
  let f₀ := B ∘ f ∘ A.symm
  have hf₀ : IsConformalEquivalence f₀ U' (B '' V) :=
    hA.trans (hf.trans (isConformalEquivalence_pointToInfinity (f p) V))
  have hU' : IsCircleDomain U' := pointToInfinity_preserves_circleDomain p hU
  have hinf : OnePoint.infty ∈ U' := by
    rw [← pointToInfinity_apply_self p]
    exact mem_image_of_mem A hp
  have hAi : A.symm OnePoint.infty = p := by
    rw [← pointToInfinity_apply_self p]
    exact A.symm_apply_apply p
  have hfix : f₀ OnePoint.infty = OnePoint.infty := by
    dsimp only [f₀,Function.comp_apply]
    rw [hAi]
    exact pointToInfinity_apply_self (f p)
  obtain ⟨a,b,ha,hnorm⟩ := principal_normalize_at_infty hU'.1 hf₀.1 hf₀.bijOn.injOn hinf hfix
  let C := affineSphere a b ha
  let f₁ := C ∘ f₀
  have hC : IsConformalEquivalence C (B '' V) (C '' (B '' V)) :=
    isConformalEquivalence_of_homeomorph C _ (fun q _ => isConformalAt_affineSphere a b ha q)
      (fun q _ => isConformalAt_affineSphere_symm a b ha q)
  have hf₁ : IsConformalEquivalence f₁ U' (C '' (B '' V)) := hf₀.trans hC
  have hc : IsCircleDomain (C '' (B '' V)) :=
    isCircleDomain_image_mobius (pointToInfinity_preserves_circleDomain (f p) hV)
      (affineMobius a b ha) C (affineSphere_eq_smul a b ha)
  have hrem' : IsConformallyRemovable (frontier U') := hrem.frontier_pointToInfinity p
  have he := hf₁.bijOn.image_eq
  have hid := hidentity hU' hinf (he.symm ▸ hf₁) hnorm (he.symm ▸ hc) hrem'
  refine ⟨(affineMobius a b ha * pointToInfinityMobius (f p))⁻¹ * pointToInfinityMobius p,?_⟩
  intro q hq
  have hh := hid (A q) (mem_image_of_mem A hq)
  change C (B (f (A.symm (A q)))) = A q at hh
  rw [A.symm_apply_apply] at hh
  change affineSphere a b ha (pointToInfinity (f p) (f q)) = pointToInfinity p q at hh
  have hh' : (affineMobius a b ha * pointToInfinityMobius (f p)) • f q =
      pointToInfinityMobius p • q := by
    simpa only [affineSphere_eq_smul,pointToInfinity_eq_smul,mul_smul] using hh
  have hh'' := congrArg (fun x : Sphere =>
    (affineMobius a b ha * pointToInfinityMobius (f p))⁻¹ • x) hh'
  rw [inv_smul_smul] at hh''
  simpa only [mul_smul] using hh''

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConditionalRigidity
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Paper 047-01, Introduction, thm:main. The exact unrestricted
removability-to-rigidity theorem from the recorded published inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_80
theorem circleDomainRemovabilityRigidity_of_scalar_solver_oai
    (hmax : PlanarMaximalL2)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hareaBound : ExteriorOmittedAreaTheorem)
    : CircleDomainRemovabilityRigidity := by
  apply circleDomainRemovabilityRigidity_of_principal_identity
  intro G f hG hinf hf hnorm hH hrem
  exact normalized_identity_of_published_inputs hmax hsolver hprincipal hsob hcross
    hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite
    hmontel hhurwitz hzero harcs hstandard hpath hdual hlift hareaBound hG hinf hf hnorm hH hrem

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver_oai := @OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver_oai
