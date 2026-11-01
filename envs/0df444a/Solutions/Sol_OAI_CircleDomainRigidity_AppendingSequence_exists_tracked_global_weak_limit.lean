-- Prove2me | solution 1 for OAI.CircleDomainRigidity.AppendingSequence.exists_tracked_global_weak_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:43:56.606244+00:00
-- url     : https://prove2.me/submissions/2d295cac-b9be-41c8-92cb-05367821e072

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010

section
-- module Solutions.Q146_CD.KLS_Sobolev_Witnesses
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem MemW1pWitness.weakGrad_norm_memLp
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hw : MemW1pWitness p f Ω μ) :
    MemLp (fun x => ‖hw.weakGrad x‖) p (μ.restrict Ω) := by
  let _ := (inferInstance : NeZero d)
  exact hw.weakGrad_memLp.norm

end DeGiorgi

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy paid by a line crossing a barrier

A barrier that is zero at an end of `[-L, L]` and equals one somewhere
on the segment has squared derivative integral at least `1 / (2 * L)`.
This follows from the fundamental theorem of calculus and the integral
Cauchy–Schwarz inequality.

Both absolutely continuous and `C¹` restrictions satisfy this estimate.
Fubini's theorem gives the rectangular energy lower bound when horizontal
slices are almost everywhere absolutely continuous.
-/

open MeasureTheory Set

namespace CircleDomainRigidity

/-- Cauchy–Schwarz against the constant function on a finite interval,
written without square roots. -/
theorem integral_sq_le_length_mul_integral_sq {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * (∫ x in a..b, g x ^ 2) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let J := ∫ x in a..b, g x
  have hpoly : (fun x => ((b - a) * g x - J) ^ 2) =
      (fun x => (b - a) ^ 2 * g x ^ 2 - (2 * (b - a) * J) * g x + J ^ 2) := by
    funext x
    ring
  have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
    (fun x => sq_nonneg ((b - a) * g x - J))
  rw [hpoly, intervalIntegral.integral_add
      ((hg2.const_mul _).sub (hg.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub (hg2.const_mul _) (hg.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hnonneg
  have hmul : (b - a) * J ^ 2 ≤
      (b - a) * ((b - a) * (∫ x in a..b, g x ^ 2)) := by
    dsimp [J] at *
    nlinarith
  exact le_of_mul_le_mul_left hmul (sub_pos.mpr hab)

end CircleDomainRigidity

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
-- module Solutions.Q146_CD.CircleDomains_Selection_ExteriorDecay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform principal remainder estimate

The same coefficient-area input gives decay at infinity, uniformly in
the finite model. This is stronger than a uniform bounded remainder and
preserves the zero constant term when passing to a limit.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem norm_exterior_series_le_two_inv {c : ℕ → ℂ} {z w : ℂ}
    (hc : ∀ n, ‖c n‖ ≤ 1) (hz : 2 ≤ ‖z‖)
    (hw : HasSum (fun n => c n * (z⁻¹) ^ (n + 1)) w) : ‖w‖ ≤ 2 * ‖z‖⁻¹ := by
  let r : ℝ := ‖z‖⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (norm_nonneg z)
  have hrhalf : r ≤ 1 / 2 := by
    dsimp only [r]
    simpa only [one_div] using
      (inv_le_inv₀ (by linarith : 0 < ‖z‖) (by norm_num : (0 : ℝ) < 2)).mpr hz
  have hr1 : r < 1 := by linarith
  have hg : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have hle := hw.norm_le_of_bounded hg (fun n => show ‖c n * (z⁻¹) ^ (n + 1)‖ ≤ r ^ (n + 1) from by
    rw [norm_mul, norm_pow, norm_inv]
    exact mul_le_of_le_one_left (pow_nonneg hr0 _) (hc n))
  refine hle.trans ?_
  change r / (1 - r) ≤ 2 * r
  apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
  nlinarith [mul_nonneg hr0 (show 0 ≤ 1 - 2 * r by linarith)]

theorem ExteriorCoefficientAreaTheorem.exterior_decay
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 1 < ‖z‖}) (hinj : InjOn F {z | 1 < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * ‖z‖⁻¹ := by
  obtain ⟨c, hc, hbound, hseries⟩ := harea F hF hinj hnorm
  intro z hz
  exact norm_exterior_series_le_two_inv (norm_coefficient_le_one hc hbound) hz
    (hseries z (by linarith))

theorem ExteriorCoefficientAreaTheorem.scaled_exterior_decay
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hinj : InjOn F {z | R < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnormR : ‖(R : ℂ)‖ = R := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let H : ℂ → ℂ := fun z => F ((R : ℂ) * z) / (R : ℂ)
  have harg {z : ℂ} (hz : 1 < ‖z‖) : R < ‖(R : ℂ) * z‖ := by
    rw [norm_mul, hnormR]
    nlinarith
  have hH : DifferentiableOn ℂ H {z | 1 < ‖z‖} := by
    intro z hz
    have hfd := (hF _ (harg hz)).differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (harg hz))
    exact ((hfd.comp z ((differentiableAt_id.const_mul (R : ℂ)))).div_const _).differentiableWithinAt
  have hHi : InjOn H {z | 1 < ‖z‖} := by
    intro z hz w hw heq
    have heq' : F ((R : ℂ) * z) = F ((R : ℂ) * w) := (div_left_inj' hRc).mp heq
    exact mul_left_cancel₀ hRc (hinj (harg hz) (harg hw) heq')
  have hnH := principal_remainder_rescale hRc hnorm
  intro z hz
  have hnormquot : ‖z / (R : ℂ)‖ = ‖z‖ / R := by rw [norm_div, hnormR]
  have hquot : 2 ≤ ‖z / (R : ℂ)‖ := by
    rw [hnormquot]
    exact (le_div_iff₀ hR).mpr (by linarith)
  have hb := harea.exterior_decay hH hHi hnH (z / (R : ℂ)) hquot
  have heq : H (z / (R : ℂ)) - z / (R : ℂ) = (F z - z) / (R : ℂ) := by
    dsimp only [H]
    rw [mul_div_cancel₀ z hRc]
    ring
  rw [heq, norm_div, hnormR, hnormquot] at hb
  have hzn : 0 < ‖z‖ := by linarith
  have hb' := (div_le_iff₀ hR).mp hb
  calc
    ‖F z - z‖ ≤ 2 * (‖z‖ / R)⁻¹ * R := hb'
    _ = 2 * R ^ 2 / ‖z‖ := by field_simp

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

end CircleDomainRigidity

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
-- module Solutions.Q146_CD.CircleDomains_Uniformization_PrincipalCoefficientLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first principal coefficient as a limit. Composition adds the actual
coefficients, and the published area theorem bounds each coefficient on a
fixed exterior disk. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem hasPrincipalCoefficient_of_expansion {F T : ℂ → ℂ} {b : ℂ}
    (hT : ContinuousAt T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = b*z⁻¹+z⁻¹^2*T z⁻¹) :
    HasPrincipalCoefficient F b := by
  have hi := tendsto_inv₀_cobounded (α := ℂ)
  have hlim := (tendsto_const_nhds (x := b)).add (hi.mul (hT.tendsto.comp hi))
  simp only [zero_mul, add_zero] at hlim
  apply hlim.congr'
  have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
    rw [Metric.cobounded_eq_cocompact]
    exact isCompact_singleton.compl_mem_cocompact
  filter_upwards [hn] with z hz
  dsimp only [Function.comp_apply]
  rw [hexp z hz]
  field_simp

 theorem exists_principal_coefficient {F : ℂ → ℂ}
    (hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∃ b, HasPrincipalCoefficient F b := by
  obtain ⟨b, T, hT, hexp⟩ := principal_exterior_expansion hd (principal_remainder_tendsto_zero hn)
  exact ⟨b, hasPrincipalCoefficient_of_expansion hT.continuousAt hexp⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactScalarModel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar models with a globally deformed round complement. This is the
smaller class needed for coefficient extremality: it contains the actual
circle models and is closed under plane homeomorphisms. The deformation
retains every complementary component, rather than just its boundary. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 namespace CompactScalarModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem normalized (M : CompactScalarModel G u) :
    IsPrincipalNormalized (extendAtInfinity M.function) :=
  isPrincipalNormalized_extendAtInfinity M.coefficient_limit.bigO

 theorem image_open (M : CompactScalarModel G u) :
    IsOpen (extendAtInfinity M.function '' G) := by
  rw [M.image_eq]
  exact M.deformation.onePointCongr.isOpenMap _ M.round_circle.1

 end CompactScalarModel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CutoffEnergyAlgebra
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary two-coordinate product estimate for a compact cutoff. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem plane_norm_sq (v : EuclideanPlane) : ‖v‖^2 = v 0^2+v 1^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

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
-- module Solutions.Q146_CD.CircleDomains_Topology_ProjectionJordanCap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous extension of the inverse carries a matched closed Jordan
cap into its source cap. The boundary identity prevents crossing the source
curve, and a domain point identifies the correct side. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem inverse_projection_matched_cap
    {G : Set Sphere} (hG : IsOpen G) {f P : Sphere → Sphere}
    (hP : Continuous P)
    (hInv : ∀ x ∈ G, P (f x) = x)
    (hOut : ∀ y ∉ f '' G, P y ∈ Gᶜ)
    (H J : ℂ ≃ₜ ℂ)
    (hFront : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hBoundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J))
    (hSide : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J)) :
    P '' closedTerminalCap J ⊆ closedTerminalCap H := by
  let U : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior H
  let V : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  have hU : IsOpen U := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hV : IsOpen V := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hUF : frontier U = ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) :=
    frontier_sphere_image_jordanInterior H
  have hVF : frontier V = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) :=
    frontier_sphere_image_jordanInterior J
  have hAvoid : Disjoint (P '' V) (frontier U) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, hy, rfl⟩ hpy
    have hpyG : P y ∈ G := hFront (hUF ▸ hpy)
    have hyf : y = f (P y) :=
      (inverse_projection_fiber_on_domain hInv hOut hpyG).mp rfl
    have hyFront : y ∈ frontier V := by
      rw [hVF, ← hBoundary, hyf]
      exact mem_image_of_mem _ (hUF ▸ hpy)
    exact hyFront.2 (hV.interior_eq.symm ▸ hy)
  have hMeet : (P '' V ∩ U).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior H).nonempty
    have hzF : (z : Sphere) ∈ frontier U := hUF.symm ▸ ⟨z, hz, rfl⟩
    obtain ⟨x, hxG, hxU⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hzF)
      G (hG.mem_nhds (hFront ⟨z, hz, rfl⟩))
    have hfx : f x ∈ V := by
      have hh : f x ∈ f '' G ∩ V := hSide ▸ mem_image_of_mem f ⟨hxG, hxU⟩
      exact hh.2
    exact ⟨P (f x), ⟨f x, hfx, rfl⟩, by simpa only [hInv x hxG] using hxU⟩
  have hCover : P '' V ⊆ U ∪ (closure U)ᶜ := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact Or.inl hyU
    · exact Or.inr fun hycl => Set.disjoint_left.mp hAvoid hy
        ⟨hycl, by simpa only [hU.interior_eq] using hyU⟩
  have hconn : IsPreconnected V :=
    (isConnected_jordanInterior J).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hsub : P '' V ⊆ U := (hconn.image P hP.continuousOn).subset_left_of_subset_union
    hU isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ (subset_closure h₁)) hCover hMeet
  have hcl : P '' closure V ⊆ closure U :=
    hP.continuousOn.image_closure.trans (closure_mono hsub)
  simpa only [U, V, closedTerminalCap, closure_sphere_image_jordanInterior] using hcl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProjectionEndFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fibers of the continuous inverse projection are the complementary
components when the original complement is dust, by the matched Jordan
exhaustion. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem inverse_projection_component_eq_fiber
    {G : Set Sphere} (hG : IsOpen G) (hTD : IsTotallyDisconnected Gᶜ)
    {f P : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hP : Continuous P) (hInv : ∀ x ∈ G, P (f x) = x)
    (hOut : ∀ y ∉ f '' G, P y ∈ Gᶜ)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n+1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    connectedComponentIn (f '' G)ᶜ p = P ⁻¹' {P p} := by
  have hfront (n : ℕ) (i : Fin (C n).count) :
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i)) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hh : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨i, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hh
  have hcap (n : ℕ) (i : Fin (C n).count) := inverse_projection_matched_cap hG hP hInv hOut
    ((C n).disk i) (J n i) (hfront n i) (hboundary n i) (hside n i)
  have hvalue (b : (n : ℕ) → Fin (C n).count) (q : Sphere) (hq : q ∈ Gᶜ)
      (hs : connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)))
      {z : Sphere} (hz : z ∈ ⋂ n, closedTerminalCap (J n (b n))) : P z = q := by
    have hmem : P z ∈ connectedComponentIn Gᶜ q := by
      rw [hs]
      exact mem_iInter.mpr fun n => hcap n (b n) (mem_image_of_mem P (mem_iInter.mp hz n))
    have hsingle : connectedComponentIn Gᶜ q = {q} :=
      (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn hq)
    simpa only [hsingle, mem_singleton_iff] using hmem
  obtain ⟨b, q, hq, hs, ht, _⟩ := corresponding_source_end_of_target hG hf hi C J
    hstrict hcover hJd hJe hboundary hside hp
  have hpp : P p = q := hvalue b q hq hs (ht ▸ mem_connectedComponentIn hp)
  apply Subset.antisymm
  · intro z hz
    change P z = P p
    exact (hvalue b q hq hs (ht ▸ hz)).trans hpp.symm
  · intro z hz
    have he : P z = P p := hz
    have hzOut : z ∈ (f '' G)ᶜ := by
      rintro ⟨x, hx, rfl⟩
      exact hOut p hp (by rw [← he, hInv x hx]; exact hx)
    obtain ⟨b', q', hq', hs', ht', _⟩ := corresponding_source_end_of_target hG hf hi C J
      hstrict hcover hJd hJe hboundary hside hzOut
    have hqq : q' = q := (hvalue b' q' hq' hs' (ht' ▸ mem_connectedComponentIn hzOut)).symm.trans
      (he.trans hpp)
    have hb : b' = b := by
      funext n
      by_contra hne
      have hq₁ : q ∈ closedTerminalCap ((C n).disk (b n)) :=
        mem_iInter.mp (hs ▸ mem_connectedComponentIn hq) n
      have hq₂ : q ∈ closedTerminalCap ((C n).disk (b' n)) := by
        rw [← hqq]
        exact mem_iInter.mp (hs' ▸ mem_connectedComponentIn hq') n
      exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (C n).disk (C n).disjoint hne) hq₂ hq₁
    rw [ht]
    rw [hb] at ht'
    exact ht' ▸ mem_connectedComponentIn hzOut

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelScalarPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact global Sobolev target scalar constant on the omitted
components descends to a compact continuous source scalar, with the
conformally transported Sobolev witness on the source domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem planeInverseTransport_extendAtInfinity (f : ℂ → ℂ)
    (v : EuclideanPlane → ℝ) (x : EuclideanPlane) :
    planeInverseTransport (extendAtInfinity f) v x =
      sphereFromPlaneFunction v (extendAtInfinity f (planeSphere x)) := by
  simp only [planeInverseTransport, Function.comp_apply, sphereRealMap,
    planeSphere, extendAtInfinity_coe, finiteCoord_coe, sphereFromPlaneFunction_coe]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ModelCompactTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact target scalars have finite source L2 norm even when their
values do not descend across the source dust. This permits transport
of the actual vertical error, which need not be constant on holes. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem source_bounded_over_compact_target (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {K : Set EuclideanPlane} (hK : IsCompact K) :
    ∃ R ≥ 0, ∀ z : ℂ, (z : Sphere) ∈ G →
      complexPlaneCoordinates.symm (M.function z) ∈ K → ‖z‖ ≤ R := by
  let C := M.projection '' (planeSphere '' K)
  have hC : IsCompact C := (hK.image continuous_planeSphere).image M.projection_continuous
  have hno : OnePoint.infty ∉ C := by
    rintro ⟨p, ⟨x, hx, rfl⟩, hp⟩
    have hh : planeSphere x = OnePoint.infty :=
      (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hinf).mp
        (by simpa only [extendAtInfinity_infty] using hp)
    exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) hh
  obtain ⟨R, hR⟩ := (hC.image_of_continuousOn
    (continuousOn_finiteCoord_of_avoids_infty hno)).isBounded.exists_norm_le
  refine ⟨max R 0, le_max_right _ _, fun z hz hk => ?_⟩
  apply (hR z ?_).trans (le_max_left _ _)
  refine ⟨(z : Sphere), ?_, by simp only [finiteCoord_coe]⟩
  refine ⟨(M.function z : Sphere), ?_, ?_⟩
  · exact ⟨_, hk, by simp only [planeSphere, complexPlaneCoordinates.apply_symm_apply]⟩
  · simpa only [extendAtInfinity_coe] using M.projection_inverse _ hz

 theorem compact_target_pullback_memLp (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {v : EuclideanPlane → ℝ} (hv : Continuous v) (hs : HasCompactSupport v) :
    MemLp (planeInverseTransport (extendAtInfinity M.function) v) 2
      (volume.restrict (physicalPlaneDomain G)) := by
  let w := planeInverseTransport (extendAtInfinity M.function) v
  have hw (x : EuclideanPlane) : w x = v (complexPlaneCoordinates.symm
      (M.function (complexPlaneCoordinates x))) := by
    change planeInverseTransport (extendAtInfinity M.function) v x = _
    rw [planeInverseTransport_extendAtInfinity]
    simp only [planeSphere, extendAtInfinity_coe, sphereFromPlaneFunction_coe]
  have hD : IsOpen {z : ℂ | (z : Sphere) ∈ G} := hG.preimage OnePoint.continuous_coe
  have hf : ContinuousOn M.function {z : ℂ | (z : Sphere) ∈ G} :=
    (show DifferentiableOn ℂ M.function _ from fun z hz =>
      (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt).continuousOn
  have hc : ContinuousOn w (physicalPlaneDomain G) := by
    have hh := (hv.comp complexPlaneCoordinates.symm.continuous).continuousOn.comp
      (hf.comp complexPlaneCoordinates.continuous.continuousOn (fun _ hx => hx)) (mapsTo_univ _ _)
    exact hh.congr (fun x _ => hw x)
  obtain ⟨R, _, hR⟩ := M.source_bounded_over_compact_target hinf hs.isCompact
  obtain ⟨B, hB⟩ := hv.bounded_above_of_compact_support hs
  have hI : MemLp ((closedBall (0 : EuclideanPlane) R).indicator (fun _ => B)) 2 volume :=
    memLp_indicator_const 2 measurableSet_closedBall B
      (Or.inr (measure_closedBall_lt_top.ne))
  apply (hI.restrict _).of_le (hc.aestronglyMeasurable (isOpen_physicalPlaneDomain hG).measurableSet)
  filter_upwards [ae_restrict_mem (isOpen_physicalPlaneDomain hG).measurableSet] with x hx
  by_cases hxs : complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x)) ∈ tsupport v
  · have hxR : x ∈ closedBall (0 : EuclideanPlane) R := by
      rw [mem_closedBall_zero_iff]
      simpa only [complexPlaneCoordinates_norm] using hR _ hx hxs
    rw [indicator_of_mem hxR, hw]
    exact (hB _).trans (le_abs_self B)
  · rw [hw, image_eq_zero_of_notMem_tsupport hxs, norm_zero]
    exact norm_nonneg _

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ModelUniformBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform omitted-set and working-disk bounds for the actual compact
scalar models. The constants depend on the source exterior radius alone. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem uniform_omitted_and_image_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G)
    {R : ℝ} (hR : 0 < R)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G) :
    (∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ 3*R) ∧
      ∀ z : ℂ, (z : Sphere) ∈ G → ‖z‖ ≤ 4*R → ‖M.function z‖ ≤ 5*R := by
  obtain ⟨hfc,hmap,fi,hfic,hfimap,hl,hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence (extendAtInfinity M.function) fi G
      (extendAtInfinity M.function '' G) :=
    ⟨fun p hp => hfc.isSmoothSphereAt hG hp, hmap,
      fun p hp => hfic.isSmoothSphereAt M.image_open hp, hfimap, hl, hr⟩
  have hc : IsConformalOn (extendAtInfinity M.function)
      ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ) := by
    intro p hp
    exact hfc p (hsource ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)) hp))
  obtain ⟨hF,hbound⟩ := normalized_model_uniform_bound harea heq M.image_open hR hsource hc M.normalized
  constructor
  · intro z hz
    obtain ⟨w,hw,he⟩ := hF (z : Sphere) hz
    have hzw : w = z := OnePoint.coe_injective he
    simpa only [hzw, mem_closedBall, dist_zero_right] using hw
  · intro z hz hzr
    obtain ⟨w,hw,he⟩ := hbound z hz hzr
    have hzw : w = M.function z := OnePoint.coe_injective (by simpa only [extendAtInfinity_coe] using he)
    simpa only [hzw, mem_closedBall, dist_zero_right] using hw

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SelectedTraceBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected compact pair has a uniform trace bound, obtained from
the actual omitted set and controlled-height closeness. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem planePair_norm_le (a b : ℝ) : ‖planePair a b‖ ≤ |a|+|b| := by
  have he : ‖planePair a b‖^2 = a^2+b^2 := by simp only [plane_norm_sq, planePair_zero, planePair_one]
  nlinarith [norm_nonneg (planePair a b), abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoordinateLines
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

 theorem physicalCoordinateLine_energy_integrable {f : EuclideanPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2)
    (hi : Integrable (fun z => (fderiv ℝ f z (EuclideanSpace.single i 1))^2) volume) :
    Integrable (fun p : ℝ × ℝ => deriv (fun t => f (physicalCoordinateLine i p.1 t)) p.2^2)
      (volume.prod volume) := by
  simp only [physicalCoordinateLine_deriv hf]
  have hm := euclideanPlaneCoordinates_symm_measurePreserving.integrable_comp_of_integrable hi
  rw [Measure.volume_eq_prod] at hm
  fin_cases i
  · simpa [physicalCoordinateLine,Function.comp_def,Prod.swap] using hm.swap
  · simpa [physicalCoordinateLine,
      Function.comp_def] using hm

 theorem physicalCoordinateLine_energy_eq {f : EuclideanPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    (∫ p : ℝ × ℝ, deriv (fun t => f (physicalCoordinateLine i p.1 t)) p.2^2
      ∂(volume.prod volume)) =
    ∫ z, (fderiv ℝ f z (EuclideanSpace.single i 1))^2 := by
  simp only [physicalCoordinateLine_deriv hf]
  have hm := euclideanPlaneCoordinates_symm_measurePreserving.integral_comp
    euclideanPlaneCoordinates.symm.toHomeomorph.measurableEmbedding
    (fun z => (fderiv ℝ f z (EuclideanSpace.single i 1))^2)
  rw [Measure.volume_eq_prod] at hm
  fin_cases i
  · change (∫ p : ℝ × ℝ, (fderiv ℝ f (euclideanPlaneCoordinates.symm p.swap)
      (EuclideanSpace.single 0 1))^2 ∂(volume.prod volume)) = _
    exact (integral_prod_swap _).trans hm
  · exact hm

 theorem physicalCoordinateLine_coordinate (i : Fin 2) (y x : ℝ) :
    physicalCoordinateLine i y x i = x := by
  fin_cases i
  · change (euclideanPlaneCoordinates.symm (x,y)) 0 = x
    exact congrArg Prod.fst (euclideanPlaneCoordinates.apply_symm_apply (x,y))
  · change (euclideanPlaneCoordinates.symm (y,x)) 1 = x
    exact congrArg Prod.snd (euclideanPlaneCoordinates.apply_symm_apply (y,x))

 theorem physicalCoordinateLine_norm_le (i : Fin 2) (y x : ℝ) :
    ‖physicalCoordinateLine i y x‖ ≤ |x|+|y| := by
  have he (a b : ℝ) : euclideanPlaneCoordinates.symm (a,b) = planePair a b := by
    apply euclideanPlaneCoordinates.injective
    simp only [euclideanPlaneCoordinates_apply,planePair_zero,planePair_one,
      ContinuousLinearEquiv.apply_symm_apply]
  fin_cases i
  · simpa [physicalCoordinateLine,he] using planePair_norm_le x y
  · simpa [physicalCoordinateLine,he,
      add_comm] using planePair_norm_le y x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothLineOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth line estimate for a non-unit oscillation. This allows
uniform mollifications of a continuous Sobolev barrier to retain a
positive crossing cost without assuming an ACL theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_line_oscillation {f : ℝ → ℝ} {a b c : ℝ}
    (hf : ContDiff ℝ 1 f) (hc : c ∈ Icc a b) :
    (f c-f a)^2 ≤ (b-a)*(∫ x in a..b, deriv f x^2) := by
  have hi : IntervalIntegrable (deriv f) volume a b := hf.continuous_deriv_one.intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun x => deriv f x^2) volume a b := (hf.continuous_deriv_one.pow 2).intervalIntegrable a b
  have hsub : uIcc a c ⊆ uIcc a b :=
    uIcc_subset_uIcc_left (by simpa [uIcc_of_le (hc.1.trans hc.2)] using hc)
  have hiac := hi.mono_set hsub
  have hi2ac := hi2.mono_set hsub
  have hFTC : (∫ x in a..c, deriv f x) = f c-f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc.1
      (hf.continuous.continuousOn.mono (Icc_subset_Icc le_rfl hc.2))
      (fun x _ => (hf.differentiable_one x).hasDerivAt) hiac
  have hmono : (∫ x in a..c, deriv f x^2) ≤ ∫ x in a..b, deriv f x^2 :=
    intervalIntegral.integral_mono_interval le_rfl hc.1 hc.2
      (Eventually.of_forall (fun x => sq_nonneg (deriv f x))) hi2
  have henergy : 0 ≤ ∫ x in a..b, deriv f x^2 :=
    intervalIntegral.integral_nonneg_of_forall (hc.1.trans hc.2) (fun x => sq_nonneg _)
  calc
    _ = (∫ x in a..c, deriv f x)^2 := by rw [hFTC]
    _ ≤ (c-a)*(∫ x in a..c, deriv f x^2) := integral_sq_le_length_mul_integral_sq hc.1 hiac hi2ac
    _ ≤ (c-a)*(∫ x in a..b, deriv f x^2) := mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hc.1)
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hc.2 a) henergy

 theorem smooth_line_half_payment {f : ℝ → ℝ} {L c : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hc : c ∈ Icc (-L) L)
    (hosc : (1:ℝ)/2 ≤ f c-f (-L)) :
    1/(8*L) ≤ ∫ x in (-L)..L, deriv f x^2 := by
  have h := smooth_line_oscillation hf hc
  have hs : (1:ℝ)/4 ≤ (f c-f (-L))^2 := by
    nlinarith only [hosc,sq_nonneg (f c-f (-L)-1/2)]
  apply (div_le_iff₀ (by positivity : 0 < 8*L)).mpr
  nlinarith only [h,hs]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPlaneLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrate the positive oscillation cost over an arbitrary finite
measurable set of horizontal lines. No choice of crossing points needs
to be measurable. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_plane_half_payment
    {v : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hv : ∀ y, ContDiff ℝ 1 (v y))
    (hE : Integrable (fun p : ℝ × ℝ => deriv (v p.1) p.2^2) (volume.prod volume))
    {J : Set ℝ} (_hJ : MeasurableSet J) (hJf : volume J ≠ ∞)
    (hcross : ∀ᵐ y ∂volume.restrict J, ∃ c ∈ Icc (-L) L,
      (1:ℝ)/2 ≤ v y c-v y (-L)) :
    (volume J).toReal/(8*L) ≤ ∫ p : ℝ × ℝ, deriv (v p.1) p.2^2 ∂(volume.prod volume) := by
  let E := fun p : ℝ × ℝ => deriv (v p.1) p.2^2
  let μ := (volume.restrict J).prod (volume.restrict (Ioc (-L) L))
  have hEr : Integrable E μ := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact hE.restrict
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJf
  have hLL : -L ≤ L := by linarith
  have hbound : ∀ᵐ y ∂volume.restrict J,
      1/(8*L) ≤ ∫ x in Ioc (-L) L, deriv (v y) x^2 := by
    filter_upwards [hcross] with y hy
    obtain ⟨c,hc,hcjump⟩ := hy
    simpa only [intervalIntegral.integral_of_le hLL] using smooth_line_half_payment hL (hv y) hc hcjump
  calc
    _ = ∫ _y in J, (1/(8*L) : ℝ) := by
      rw [integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,div_eq_mul_inv,one_mul]
    _ ≤ ∫ y in J, ∫ x in Ioc (-L) L, deriv (v y) x^2 :=
      integral_mono_ae (integrable_const _) hEr.integral_prod_left hbound
    _ = ∫ p, E p ∂μ := (integral_prod _ hEr).symm
    _ = ∫ p in J ×ˢ Ioc (-L) L, E p ∂(volume.prod volume) := by
      dsimp only [μ]
      rw [Measure.prod_restrict]
    _ ≤ _ := setIntegral_le_integral hE (Eventually.of_forall (fun p => sq_nonneg _))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous compact Sobolev barriers pay for every transverse line
on which they attain one. Uniform mollification supplies the line FTC;
strong convergence of weak partials passes the energy bound to the limit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem sobolev_coordinate_line_payment
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    (W : DeGiorgi.MemW1pWitness 2 v univ)
    {L : ℝ} (hL : 0 < L) (hs : tsupport v ⊆ ball 0 L)
    (i : Fin 2) {J : Set ℝ} (hJ : MeasurableSet J) (hJL : J ⊆ Icc (-L) L)
    (hcross : ∀ y ∈ J, ∃ c ∈ Icc (-L) L, v (physicalCoordinateLine i y c) = 1) :
    (volume J).toReal/(8*L) ≤ ∫ x, ‖W.weakGrad x‖^2 := by
  have hcompact : HasCompactSupport v :=
    (isCompact_closedBall (0 : EuclideanPlane) L).of_isClosed_subset (isClosed_tsupport v)
      (hs.trans ball_subset_closedBall)
  have hvLp : MemLp v 2 volume := by simpa only [Measure.restrict_univ] using W.memLp
  have happrox := planarMollification_uniform_on_compact hvLp.aestronglyMeasurable
    (isCompact_closedBall (0 : EuclideanPlane) (2*L)) isOpen_univ (subset_univ _)
    hv.continuousOn (show (0 : ℝ) < 1/8 by norm_num)
  have hnorm (y x : ℝ) (hy : y ∈ Icc (-L) L) (hx : x ∈ Icc (-L) L) :
      physicalCoordinateLine i y x ∈ closedBall 0 (2*L) := by
    rw [mem_closedBall_zero_iff]
    exact (physicalCoordinateLine_norm_le i y x).trans (by
      have hx' : |x| ≤ L := abs_le.mpr hx
      have hy' : |y| ≤ L := abs_le.mpr hy
      linarith)
  have hzero (y : ℝ) : v (physicalCoordinateLine i y (-L)) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hb := mem_ball_zero_iff.mp (hs hx)
    have ha := PiLp.norm_apply_le (physicalCoordinateLine i y (-L)) i
    rw [physicalCoordinateLine_coordinate,Real.norm_eq_abs,abs_neg,abs_of_pos hL] at ha
    exact (not_lt_of_ge ha) hb
  have hpay : ∀ᶠ n in atTop, (volume J).toReal/(8*L) ≤
      ∫ x, (fderiv ℝ (planarMollification v n) x (EuclideanSpace.single i 1))^2 := by
    filter_upwards [happrox] with n hn
    have hf := planarMollification_smooth (hvLp.locallyIntegrable (by norm_num)) n
    rw [← physicalCoordinateLine_energy_eq (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) i]
    apply smooth_plane_half_payment hL
      (fun y => (hf.comp (physicalCoordinateLine_contDiff i y)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (physicalCoordinateLine_energy_integrable (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) i
        (planarMollification_partial_memLp W hcompact n i).integrable_sq) hJ
      (ne_of_lt ((measure_mono hJL).trans_lt measure_Icc_lt_top))
    filter_upwards [ae_restrict_mem hJ] with y hy
    obtain ⟨c,hc,hvc⟩ := hcross y hy
    refine ⟨c,hc,?_⟩
    have hec := hn _ (hnorm y c (hJL hy) hc)
    have hea := hn _ (hnorm y (-L) (hJL hy) ⟨le_rfl,by linarith⟩)
    rw [hvc] at hec
    rw [hzero y] at hea
    change (1:ℝ)/2 ≤ planarMollification v n (physicalCoordinateLine i y c) -
      planarMollification v n (physicalCoordinateLine i y (-L))
    have hc' := (abs_lt.mp hec).1
    have ha' := (abs_lt.mp hea).2
    linarith
  have hgrad : MemLp (fun x => W.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
  have hlim := integral_sq_tendsto_of_L2
    (fun n => planarMollification_partial_memLp W hcompact n i) hgrad
    (planarMollification_tendsto_gradient_L2 W i)
  refine (ge_of_tendsto hlim hpay).trans ?_
  have hn : Integrable (fun x => ‖W.weakGrad x‖^2) volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_norm_memLp.integrable_sq
  apply integral_mono_ae hgrad.integrable_sq hn
  exact Eventually.of_forall fun x => by
    have hi := PiLp.norm_apply_le (W.weakGrad x) i
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hi 2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevBarrierCollapse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing global Sobolev energy excludes a positive measure family of
coordinate crossings. The crossing locations may vary with every barrier. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem measure_zero_of_vanishing_sobolev_barriers
    {v : ℕ → EuclideanPlane → ℝ}
    (W : ∀ n, DeGiorgi.MemW1pWitness 2 (v n) univ)
    (hv : ∀ n, Continuous (v n)) {L : ℝ} (hL : 0 < L)
    (hs : ∀ n, tsupport (v n) ⊆ ball 0 L)
    (hE : Tendsto (fun n => ∫ x, ‖(W n).weakGrad x‖^2) atTop (𝓝 0))
    (i : Fin 2) {J : Set ℝ} (hJ : MeasurableSet J) (hJL : J ⊆ Icc (-L) L)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J,
      ∃ c ∈ Icc (-L) L, v n (physicalCoordinateLine i y c) = 1) :
    volume J = 0 := by
  have hp : ∀ᶠ n in atTop, (volume J).toReal/(8*L) ≤
      ∫ x, ‖(W n).weakGrad x‖^2 := by
    filter_upwards [hcross] with n hn
    exact sobolev_coordinate_line_payment (hv n) (W n) hL (hs n) i hJ hJL hn
  have hz := ge_of_tendsto hE hp
  have hreal : (volume J).toReal = 0 := by
    have hmul := (div_le_iff₀ (by positivity : 0 < 8*L)).mp hz
    exact le_antisymm (by simpa only [zero_mul] using hmul) ENNReal.toReal_nonneg
  have hf : volume J ≠ ∞ := ne_of_lt ((measure_mono hJL).trans_lt measure_Icc_lt_top)
  exact (ENNReal.toReal_eq_zero_iff _).mp hreal |>.resolve_right hf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalFrontierCrossings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact bounded region has a first boundary point on each
coordinate line meeting its closure. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem continuous_planeTransverse (i : Fin 2) : Continuous (planeTransverse i) := by
  unfold planeTransverse
  split <;> fun_prop

 theorem physicalCoordinateLine_transverse (i : Fin 2) (y x : ℝ) :
    planeTransverse i (physicalCoordinateLine i y x) = y := by
  fin_cases i
  · change (euclideanPlaneCoordinates.symm (x,y)) 1 = y
    exact congrArg Prod.snd (euclideanPlaneCoordinates.apply_symm_apply (x,y))
  · change (euclideanPlaneCoordinates.symm (y,x)) 0 = y
    exact congrArg Prod.fst (euclideanPlaneCoordinates.apply_symm_apply (y,x))

 theorem physicalCoordinateLine_of_transverse (i : Fin 2) {z : EuclideanPlane} {y : ℝ}
    (hy : planeTransverse i z = y) : physicalCoordinateLine i y (z i) = z := by
  apply euclideanPlaneCoordinates.injective
  fin_cases i <;> simpa [physicalCoordinateLine,planeTransverse] using hy.symm

 theorem exists_coordinate_frontier {U : Set EuclideanPlane}
    (hU : IsOpen U) (hcompact : IsCompact (closure U)) (i : Fin 2) {y : ℝ}
    (hne : ∃ z ∈ closure U, planeTransverse i z = y) :
    ∃ x : ℝ, physicalCoordinateLine i y x ∈ frontier U := by
  let K := closure U ∩ {z : EuclideanPlane | planeTransverse i z = y}
  have hK : IsCompact K := hcompact.inter_right
    (isClosed_eq (continuous_planeTransverse i) continuous_const)
  have hKne : K.Nonempty := by
    obtain ⟨z,hz,hy⟩ := hne
    exact ⟨z,hz,hy⟩
  have hi : Continuous (fun z : EuclideanPlane => z i) := by fun_prop
  obtain ⟨x,hx⟩ := (hK.image hi).exists_isLeast (hKne.image (fun z => z i))
  obtain ⟨z,hz,hzx⟩ := hx.1
  have he : physicalCoordinateLine i y x = z := by
    rw [← hzx]
    exact physicalCoordinateLine_of_transverse i hz.2
  have hxcl : physicalCoordinateLine i y x ∈ closure U := he.symm ▸ hz.1
  have hmin : ∀ w ∈ closure U, planeTransverse i w = y → x ≤ w i := by
    intro w hw hwy
    exact hx.2 (mem_image_of_mem _ ⟨hw,hwy⟩)
  have hnot : physicalCoordinateLine i y x ∉ U := by
    intro hin
    have hn : (physicalCoordinateLine i y) ⁻¹' U ∈ 𝓝 x :=
      (hU.preimage (physicalCoordinateLine_contDiff i y).continuous).mem_nhds hin
    obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp hn
    have hback : x-ε/2 ∈ ball x ε := by
      rw [mem_ball,Real.dist_eq]
      rw [show x-ε/2-x = -(ε/2) by ring,abs_neg,abs_of_pos (half_pos hε)]
      linarith
    have hm := hmin _ (subset_closure (hεU hback))
      (physicalCoordinateLine_transverse i y (x-ε/2))
    rw [physicalCoordinateLine_coordinate] at hm
    linarith
  exact ⟨x,by rw [frontier,hU.interior_eq]; exact ⟨hxcl,hnot⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompactBarrierProjection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact set trapped inside bounded regions whose boundary barriers
have vanishing energy has zero projection measure in both directions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem abs_planeTransverse_le_norm (i : Fin 2) (z : EuclideanPlane) :
    |planeTransverse i z| ≤ ‖z‖ := by
  unfold planeTransverse
  split <;> simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z _

 theorem projection_measure_zero_of_compact_barriers
    {K : Set EuclideanPlane} (hK : IsCompact K)
    {U : ℕ → Set EuclideanPlane} (hU : ∀ n, IsOpen (U n))
    (hUc : ∀ n, IsCompact (closure (U n)))
    {v : ℕ → EuclideanPlane → ℝ} (W : ∀ n, DeGiorgi.MemW1pWitness 2 (v n) univ)
    (hv : ∀ n, Continuous (v n)) {L : ℝ} (hL : 0 < L)
    (hs : ∀ n, tsupport (v n) ⊆ ball 0 L)
    (hE : Tendsto (fun n => ∫ x, ‖(W n).weakGrad x‖^2) atTop (𝓝 0))
    (htrap : ∀ᶠ n in atTop, K ⊆ closure (U n) ∧ ∀ x ∈ frontier (U n), v n x = 1)
    (i : Fin 2) : volume (planeTransverse i '' K) = 0 := by
  have hcross : ∀ᶠ n in atTop, ∀ y ∈ planeTransverse i '' K,
      ∃ c ∈ Icc (-L) L, v n (physicalCoordinateLine i y c) = 1 := by
    filter_upwards [htrap] with n hn
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨c,hc⟩ := exists_coordinate_frontier (hU n) (hUc n) i ⟨z,hn.1 hz,rfl⟩
    have hone := hn.2 _ hc
    have hsup : physicalCoordinateLine i (planeTransverse i z) c ∈ tsupport (v n) := by
      apply subset_tsupport
      change v n _ ≠ 0
      rw [hone]
      norm_num
    have hnorm := mem_ball_zero_iff.mp (hs n hsup)
    have hcoord := PiLp.norm_apply_le (physicalCoordinateLine i (planeTransverse i z) c) i
    rw [physicalCoordinateLine_coordinate,Real.norm_eq_abs] at hcoord
    exact ⟨c,abs_le.mp (hcoord.trans hnorm.le),hone⟩
  have hJL : planeTransverse i '' K ⊆ Icc (-L) L := by
    obtain ⟨n,hn⟩ := hcross.exists
    intro y hy
    obtain ⟨c,hc,hvone⟩ := hn y hy
    have hsup : physicalCoordinateLine i y c ∈ tsupport (v n) := by
      apply subset_tsupport
      change v n _ ≠ 0
      rw [hvone]
      norm_num
    have hnorm := mem_ball_zero_iff.mp (hs n hsup)
    have hcoord := abs_planeTransverse_le_norm i (physicalCoordinateLine i y c)
    rw [physicalCoordinateLine_transverse] at hcoord
    exact abs_le.mp (hcoord.trans hnorm.le)
  exact measure_zero_of_vanishing_sobolev_barriers W hv hL hs hE i
    (hK.image (continuous_planeTransverse i)).measurableSet hJL hcross

 theorem physical_subsingleton_of_zero_projection_measure
    {K : Set EuclideanPlane} (hK : IsCompact K) (hconn : IsConnected K)
    (hz : ∀ i : Fin 2, volume (planeTransverse i '' K) = 0) : K.Subsingleton := by
  have hone (i : Fin 2) : (planeTransverse i '' K).Subsingleton := by
    have hc := hconn.image _ (continuous_planeTransverse i).continuousOn
    have he := eq_Icc_of_connected_compact hc (hK.image (continuous_planeTransverse i))
    have hle := nonempty_Icc.mp (he ▸ hc.nonempty)
    have hm := hz i
    rw [he,Real.volume_Icc,ENNReal.ofReal_eq_zero] at hm
    intro a ha b hb
    rw [he] at ha hb
    linarith [ha.1,ha.2,hb.1,hb.2]
  intro x hx y hy
  ext i
  fin_cases i
  · simpa [planeTransverse] using hone 1 (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
  · simpa [planeTransverse] using hone 0 (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedJordanSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CannonMobius.affine_coe _root_.OAI.CannonMobius.affine_infty _root_.OAI.CannonMobius.inv_inv_apply _root_.OAI.CannonMobius.roundChart_coe _root_.OAI.CannonMobius.tripleMap_mul _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A retained Jordan curve separates the two sides of an open connected
sphere domain. This applies to the actual finite models without extending
the model map across any terminal disk. -/

open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem isPreconnected_finite_part {G : Set Sphere}
    (hG : IsOpen G) (hconn : IsPreconnected G) :
    IsPreconnected (((↑) : ℂ → Sphere) ⁻¹' G) := by
  by_cases hi : OnePoint.infty ∈ G
  · exact (finite_part_connected_unbounded hconn
      (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hi))).1
  · have he : finiteCoord '' G = ((↑) : ℂ → Sphere) ⁻¹' G := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact (CannonMobius.coe_coordinate (fun h => hi (h ▸ hp))).symm ▸ hp
      · intro hz
        exact ⟨(z : Sphere), hz, finiteCoord_coe z⟩
    rw [← he]
    exact hconn.image _ (continuousOn_finiteCoord_of_avoids_infty hi)

 theorem isPreconnected_sphere_inter_jordan
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  have hi := isPreconnected_inter_jordanInterior
    (hG.preimage OnePoint.continuous_coe) (isPreconnected_finite_part hG hconn) H
    (fun z hz => hboundary (mem_image_of_mem _ hz))
  rw [← image_preimage_inter ((↑) : ℂ → Sphere) (jordanInterior H) G]
  exact hi.image _ OnePoint.continuous_coe.continuousOn

 theorem isPreconnected_sphere_inter_jordan_exterior
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (closedTerminalCap H)ᶜ) := by
  let e : Sphere ≃ₜ Sphere := H.onePointCongr.symm.trans CannonMobius.inversion
  have hpre : e ⁻¹' (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1) =
      (closedTerminalCap H)ᶜ := by
    change H.onePointCongr.symm ⁻¹' (CannonMobius.inversion ⁻¹'
      (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1)) = _
    rw [inversion_preimage_unitDisk, preimage_compl, ← H.onePointCongr.image_eq_preimage_symm]
    congr 1
    simp only [closedTerminalCap, closure_jordanInterior, image_image,
      Homeomorph.onePointCongr_apply, OnePoint.map_some]
  have hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Homeomorph.refl ℂ)) ⊆ e '' G := by
    rintro p ⟨z, hz, rfl⟩
    have hzn : ‖z‖ = 1 := by simpa [frontier_jordanInterior] using hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hzn
    refine ⟨(H z⁻¹ : ℂ), hboundary ?_, ?_⟩
    · refine ⟨H z⁻¹, ?_, rfl⟩
      rw [frontier_jordanInterior]
      exact ⟨z⁻¹, by simp [norm_inv, hzn], rfl⟩
    · change CannonMobius.inv (H.onePointCongr.symm ((H z⁻¹ : ℂ) : Sphere)) = (z : Sphere)
      have hx : H.onePointCongr.symm ((H z⁻¹ : ℂ) : Sphere) = ((z⁻¹ : ℂ) : Sphere) := by
        change H.onePointCongr.symm (H.onePointCongr ((z⁻¹ : ℂ) : Sphere)) = _
        exact H.onePointCongr.symm_apply_apply _
      rw [hx]
      simp [CannonMobius.inv, hz0]
  have hc := isPreconnected_sphere_inter_jordan (e.isOpenMap G hG)
    (hconn.image e e.continuous.continuousOn) (Homeomorph.refl ℂ) hbd
  have he : e.symm '' (e '' G ∩ (((↑) : ℂ → Sphere) ''
      jordanInterior (Homeomorph.refl ℂ))) = G ∩ (closedTerminalCap H)ᶜ := by
    rw [e.symm.image_eq_preimage_symm, Homeomorph.symm_symm, preimage_inter,
      e.injective.preimage_image]
    simpa only [jordanInterior, Homeomorph.refl_apply, image_id] using
      congrArg (G ∩ ·) hpre
  rw [← he]
  exact hc.image e.symm e.symm.continuous.continuousOn

 theorem open_image_retained_jordan_side_eq
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) (H J : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty)
    (hboundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J)) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) := by
  let A : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior H
  let B : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  have hAo : IsOpen A := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hBo : IsOpen B := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hAf : frontier A = ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) :=
    frontier_sphere_image_jordanInterior H
  have hBf : frontier B = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) :=
    frontier_sphere_image_jordanInterior J
  have hAcl : closure A = closedTerminalCap H := closure_sphere_image_jordanInterior H
  have havoid (x : Sphere) (hx : x ∈ G) (hxA : x ∉ frontier A) : f x ∉ frontier B := by
    intro hy
    rw [hBf, ← hboundary] at hy
    obtain ⟨y, hy, he⟩ := hy
    have hyx := hi (hbd hy) hx he
    exact hxA (hAf.symm ▸ (hyx ▸ hy))
  have hsplit (S : Set Sphere) (hS : S ⊆ G) (ha : Disjoint S (frontier A)) :
      f '' S ⊆ B ∪ (closure B)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hb : f x ∈ B
    · exact Or.inl hb
    · exact Or.inr (fun hc => havoid x (hS hx)
        (fun h => Set.disjoint_left.mp ha hx h) ⟨hc, hBo.interior_eq.symm ▸ hb⟩)
  have hdisj : Disjoint B (closure B)ᶜ :=
    Set.disjoint_left.mpr (fun _ h h' => h' (subset_closure h))
  have houtside : f '' (G ∩ (closure A)ᶜ) ⊆ (closure B)ᶜ := by
    have hc : IsPreconnected (f '' (G ∩ (closure A)ᶜ)) :=
      ((hAcl.symm ▸ isPreconnected_sphere_inter_jordan_exterior hG hconn H hbd).image
        f (hf.mono inter_subset_left))
    apply hc.subset_right_of_subset_union hBo isClosed_closure.isOpen_compl hdisj
      (hsplit _ inter_subset_left (Set.disjoint_left.mpr (fun (x : Sphere) (h : x ∈ G ∩ (closure A)ᶜ)
        (h' : x ∈ frontier A) => h.2 (frontier_subset_closure h'))))
    refine ⟨OnePoint.infty, ?_, ?_⟩
    · refine ⟨OnePoint.infty, ⟨hinf, ?_⟩, hfix⟩
      rw [hAcl]
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
    · rw [closure_sphere_image_jordanInterior J]
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
  have hinverse : f '' G ∩ B ⊆ f '' (G ∩ A) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hb⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    by_contra hxA
    by_cases hxc : x ∈ closure A
    · have hxf : x ∈ frontier A := ⟨hxc, hAo.interior_eq.symm ▸ hxA⟩
      have hyf : f x ∈ frontier B := by
        rw [hBf, ← hboundary]
        exact mem_image_of_mem f (hAf ▸ hxf)
      exact hyf.2 (hBo.interior_eq.symm ▸ hb)
    · exact houtside (mem_image_of_mem f ⟨hx, hxc⟩) (subset_closure hb)
  have hmeet : (f '' (G ∩ A) ∩ B).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior H).nonempty
    have hzA : (z : Sphere) ∈ frontier A := hAf.symm ▸ mem_image_of_mem _ hz
    have hzG : (z : Sphere) ∈ G := hbd (mem_image_of_mem _ hz)
    have hzf : f (z : Sphere) ∈ frontier B := by
      rw [hBf, ← hboundary]
      exact mem_image_of_mem f (mem_image_of_mem _ hz)
    obtain ⟨y, hy, hyB⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hzf)
      (f '' G) ((ho G hG Subset.rfl).mem_nhds (mem_image_of_mem f hzG))
    exact ⟨y, hinverse ⟨hy, hyB⟩, hyB⟩
  have hins : f '' (G ∩ A) ⊆ B := by
    apply ((isPreconnected_sphere_inter_jordan hG hconn H hbd).image
      f (hf.mono inter_subset_left)).subset_left_of_subset_union
      hBo isClosed_closure.isOpen_compl hdisj
      (hsplit _ inter_subset_left (Set.disjoint_left.mpr (fun _ h h' =>
        h'.2 (hAo.interior_eq.symm ▸ h.2)))) hmeet
  exact Subset.antisymm (fun _ h => ⟨image_mono inter_subset_left h, hins h⟩) hinverse

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedCurveImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schoenflies and open-map side correspondence for one retained
source curve. The curve may surround missing source points. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_retained_curve_image (hsch : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) {f : Sphere → Sphere}
    (hf : ContinuousOn f G) (ho : ∀ U, IsOpen U → U ⊆ G → IsOpen (f '' U))
    (hi : InjOn f G) (hfix : f OnePoint.infty = OnePoint.infty)
    (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (hγ : Continuous γ) (hγi : Injective γ)
    (hfront : range γ = frontier (jordanInterior H))
    (hγG : ∀ t, (γ t : Sphere) ∈ G) :
    ∃ J : ℂ ≃ₜ ℂ,
      Continuous (fun t => finiteCoord (f (γ t : Sphere))) ∧
      range (fun t => finiteCoord (f (γ t : Sphere))) = frontier (jordanInterior J) ∧
      f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ∧
      f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) := by
  have hfinite (t : Circle) : f (γ t : Sphere) ≠ OnePoint.infty :=
    finite_image_of_fixes_infty hi hinf hfix (hγG t)
  let δ := fun t => finiteCoord (f (γ t : Sphere))
  have hδc (t : Circle) : (δ t : Sphere) = f (γ t : Sphere) :=
    CannonMobius.coe_coordinate (hfinite t)
  have hδ : Continuous δ := by
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have he : ((↑) : ℂ → Sphere) ∘ δ = f ∘ ((↑) : ℂ → Sphere) ∘ γ := funext hδc
    rw [he]
    exact hf.comp_continuous (OnePoint.continuous_coe.comp hγ) hγG
  have hδi : Injective δ := by
    intro s t hst
    apply hγi
    apply OnePoint.coe_injective
    exact hi (hγG s) (hγG t)
      ((hδc s).symm.trans ((congrArg ((↑) : ℂ → Sphere) hst).trans (hδc t)))
  obtain ⟨J,hJ⟩ := hsch δ hδ hδi
  have hJfront : range δ = frontier (jordanInterior J) :=
    (frontier_jordanInterior_eq_circle_range J δ hJ).symm
  have hb : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) := by
    rw [← hfront,← hJfront,image_image,← range_comp,← range_comp]
    congr 1
    funext t
    exact (hδc t).symm
  refine ⟨J,hδ,hJfront,hb,?_⟩
  apply open_image_retained_jordan_side_eq hG hconn hinf H J ?_ hf ho hi hfix hb
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨t,rfl⟩ := hfront.symm ▸ hz
  exact hγG t

 theorem matched_end_subset_retained_side
    {G : Set Sphere} {f : Sphere → Sphere} (hi : InjOn f G)
    (H J : ℂ ≃ₜ ℂ) (Hn Jn : ℕ → ℂ ≃ₜ ℂ)
    (hnest : Antitone (fun n => closedTerminalCap (Hn n)))
    (hfrontG : ∀ n, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Hn n)) ⊆ G)
    (hboundary : ∀ n, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (Hn n))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Jn n)))
    (hside : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J))
    {q : Sphere} (hend : (⋂ n, closedTerminalCap (Hn n)) = {q})
    (hq : q ∈ ((↑) : ℂ → Sphere) '' jordanInterior H) :
    (⋂ n, closedTerminalCap (Jn n)) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J := by
  obtain ⟨n,hn⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap (Hn n)).isClosed) hnest
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
    (by rw [hend]; exact singleton_subset_iff.mpr hq)
  exact (iInter_subset _ n).trans
    ((matched_jordan_disk_subset_iff hi H (Hn n) J (Jn n) (hfrontG n) (hboundary n) hside).mp hn)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedJordanConvergence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Anchors for the Jordan curves of actual finite models

A point of the physical domain on the inside of a retained contour gives
an interior anchor in every sufficiently late model. The proved side
correspondence identifies that side, and local uniform convergence gives
the anchor and boundary convergence needed for the crossing argument.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_domain_point_inside_jordan
    {G : Set Sphere} (hG : IsOpen G) (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    ∃ q : ℂ, (q : Sphere) ∈ G ∧ q ∈ jordanInterior H := by
  obtain ⟨p, hp⟩ := (isConnected_frontier_jordanInterior H).nonempty
  have hpG : p ∈ ((↑) : ℂ → Sphere) ⁻¹' G := hboundary ⟨p, hp, rfl⟩
  exact mem_closure_iff_nhds.mp (frontier_subset_closure hp)
    (((↑) : ℂ → Sphere) ⁻¹' G) ((hG.preimage OnePoint.continuous_coe).mem_nhds hpG)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AnchoredCurveImages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every fixed source contour has compatible image interiors along a
locally uniformly convergent sequence of normalized conformal maps. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_anchored_curve_images (hsch : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G)
    (f : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hf : ∀ n, IsConformalEquivalence (extendAtInfinity (f n)) G (extendAtInfinity (f n) '' G))
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn f F atTop {z : ℂ | (z : Sphere) ∈ G})
    (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (hγ : Continuous γ) (hγi : Injective γ)
    (hfront : range γ = frontier (jordanInterior H))
    (hγG : ∀ t, (γ t : Sphere) ∈ G) :
    ∃ (J : ℂ ≃ₜ ℂ) (Jn : ℕ → ℂ ≃ₜ ℂ) (q : ℂ),
      (q : Sphere) ∈ G ∧ F q ∈ jordanInterior J ∧
      Continuous (F ∘ γ) ∧ range (F ∘ γ) = frontier (jordanInterior J) ∧
      (∀ n, range (f n ∘ γ) = frontier (jordanInterior (Jn n))) ∧
      TendstoUniformly (fun n => f n ∘ γ) (F ∘ γ) atTop ∧
      Tendsto (fun n => f n q) atTop (𝓝 (F q)) ∧
      (∀ n, f n q ∈ jordanInterior (Jn n)) ∧
      extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
        extendAtInfinity F '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) := by
  have hinj (g : ℂ → ℂ)
      (hg : IsConformalEquivalence (extendAtInfinity g) G (extendAtInfinity g '' G)) :
      InjOn (extendAtInfinity g) G := by
    obtain ⟨_,_,gi,_,_,hl,_⟩ := hg
    intro x hx y hy he
    simpa only [hl x hx,hl y hy] using congrArg gi he
  have himg (g : ℂ → ℂ)
      (hg : IsConformalEquivalence (extendAtInfinity g) G (extendAtInfinity g '' G)) :=
    exists_retained_curve_image hsch hG hconn hinf
      (fun p hp => (hg.1 p hp).1.continuousWithinAt)
      (fun U hU hUG => hg.1.isOpen_image hG hU hUG) (hinj g hg) (by rfl)
      H γ hγ hγi hfront hγG
  obtain ⟨J,hJc,hJfront,hJbd,hJside⟩ := himg F hF
  choose Jn hJnc hJnfront hJnbd hJnside using fun n => himg (f n) (hf n)
  have hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨t,rfl⟩ := hfront.symm ▸ hz
    exact hγG t
  obtain ⟨q,hqG,hqH⟩ := exists_domain_point_inside_jordan hG H hbd
  have hinside (g : ℂ → ℂ) (K : ℂ ≃ₜ ℂ)
      (hside : extendAtInfinity g '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
        extendAtInfinity g '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior K)) :
      g q ∈ jordanInterior K := by
    have h := mem_image_of_mem (extendAtInfinity g) (show (q : Sphere) ∈
      G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) from ⟨hqG,q,hqH,rfl⟩)
    rw [hside] at h
    simpa only [extendAtInfinity_coe,OnePoint.coe_injective.mem_set_image] using h.2
  refine ⟨J,Jn,q,hqG,hinside F J hJside,?_,?_,?_,?_,hlim.tendsto_at hqG,
    fun n => hinside (f n) (Jn n) (hJnside n),hJside⟩
  · simpa only [extendAtInfinity_coe,finiteCoord_coe,Function.comp_def] using hJc
  · simpa only [extendAtInfinity_coe,finiteCoord_coe,Function.comp_def] using hJfront
  · intro n
    simpa only [extendAtInfinity_coe,finiteCoord_coe,Function.comp_def] using hJnfront n
  · apply tendstoUniformlyOn_univ.mp
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_univ).mp
    exact hlim.comp γ (fun t _ => hγG t) hγ.continuousOn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompactBarrierData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete compact global barriers surrounding a fixed compact set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_barrier_data_subsingleton
    {K : Set EuclideanPlane} (hK : IsCompact K) (hc : IsConnected K)
    {L : ℝ} (hL : 0 < L)
    (D : ∀ s : ℕ, CompactBarrierData K L (1/((s:ℝ)+1))) : K.Subsingleton := by
  have hE : Tendsto (fun s => ∫ x, ‖(D s).witness.weakGrad x‖^2) atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    simp only [zero_pow (by decide : 2 ≠ 0)] at ht
    exact squeeze_zero (fun s => integral_nonneg (fun x => sq_nonneg _))
      (fun s => (D s).energy.le) ht
  apply physical_subsingleton_of_zero_projection_measure hK hc
  intro i
  exact projection_measure_zero_of_compact_barriers hK
    (fun s => (D s).open_region) (fun s => (D s).compact_closure)
    (fun s => (D s).witness) (fun s => (D s).continuous) hL
    (fun s => (D s).support) hE
    (Eventually.of_forall (fun s => ⟨(D s).contains,(D s).one⟩)) i

 theorem exists_compact_barrier_of_curve_images
    {K : Set ℂ} (hK : IsCompact K) (J : ℂ ≃ₜ ℂ) (Jn : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior J))
    (hfrontn : ∀ n, range (γn n) = frontier (jordanInterior (Jn n)))
    (hlim : TendstoUniformly γn γ atTop)
    {q : ℂ} {qn : ℕ → ℂ} (hq : q ∈ jordanInterior J)
    (hqlim : Tendsto qn atTop (𝓝 q)) (hqn : ∀ n, qn n ∈ jordanInterior (Jn n))
    (hKJ : K ⊆ jordanInterior J) {L η : ℝ}
    (hbarrier : ∀ᶠ n in atTop,
      ∃ (v : EuclideanPlane → ℝ) (W : DeGiorgi.MemW1pWitness 2 v univ),
        Continuous v ∧ tsupport v ⊆ ball 0 L ∧
        (∀ t, v (complexPlaneCoordinates.symm (γn n t)) = 1) ∧
        (∫ x, ‖W.weakGrad x‖^2) < η^2) :
    Nonempty (CompactBarrierData (complexPlaneCoordinates.symm '' K) L η) := by
  have hret := eventually_compact_subset_jordanInterior_of_anchor J Jn γ γn hγ hfront
    (Eventually.of_forall hfrontn) hlim hq hqlim (Eventually.of_forall hqn) hK hKJ
  obtain ⟨n,hn,hb⟩ := (hret.and hbarrier).exists
  obtain ⟨v,W,hv,hs,hone,hE⟩ := hb
  let U := complexPlaneCoordinates ⁻¹' jordanInterior (Jn n)
  have hUc : IsCompact (closure U) := by
    have he : closure U = complexPlaneCoordinates.symm '' closure (jordanInterior (Jn n)) := by
      calc
        closure U = complexPlaneCoordinates ⁻¹' closure (jordanInterior (Jn n)) :=
          (complexPlaneCoordinates.toHomeomorph.preimage_closure _).symm
        _ = _ := by
          ext x
          constructor
          · intro hx
            exact ⟨complexPlaneCoordinates x,hx,complexPlaneCoordinates.symm_apply_apply x⟩
          · rintro ⟨z,hz,rfl⟩
            simpa only [mem_preimage,complexPlaneCoordinates.apply_symm_apply] using hz
    rw [he]
    exact (isCompact_closure_jordanInterior (Jn n)).image complexPlaneCoordinates.symm.continuous
  refine ⟨⟨U,(jordanInterior_isOpen _).preimage complexPlaneCoordinates.continuous,hUc,
    ?_,v,W,hv,hs,?_,hE⟩⟩
  · rintro x ⟨z,hz,rfl⟩
    apply subset_closure
    change complexPlaneCoordinates (complexPlaneCoordinates.symm z) ∈ jordanInterior (Jn n)
    rw [complexPlaneCoordinates.apply_symm_apply]
    exact hn hz
  · intro x hx
    have hx' : complexPlaneCoordinates x ∈ frontier (jordanInterior (Jn n)) := by
      change x ∈ complexPlaneCoordinates ⁻¹' frontier (jordanInterior (Jn n))
      have he : complexPlaneCoordinates ⁻¹' frontier (jordanInterior (Jn n)) = frontier U :=
        complexPlaneCoordinates.toHomeomorph.preimage_frontier _
      rwa [he]
    obtain ⟨t,ht⟩ := (hfrontn n).symm ▸ hx'
    have h := hone t
    rwa [ht,complexPlaneCoordinates.symm_apply_apply] at h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ComponentBarriers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From analytic barriers to circle-domain component control

The complementary components are the components of the sphere's closed
complement. Components admitting vanishing absolutely continuous barriers
are points. If all remaining components are round disks, the domain is
a circle domain.
-/

open Set Topology
open scoped OnePoint

namespace CircleDomainRigidity

private theorem image_planarPart {K : Set Sphere} (hinfty : ∞ ∉ K) :
    (fun z : ℂ => (z : Sphere)) '' planarPart K = K := by
  apply image_preimage_eq_of_subset
  intro p hp
  exact OnePoint.ne_infty_iff_exists.mp (fun h => hinfty (h ▸ hp))

/-- A compact connected sphere set missing infinity is a compact connected
plane set in the standard chart. -/
theorem planarPart_isCompact_isConnected {K : Set Sphere}
    (hcompact : IsCompact K) (hconn : IsConnected K) (hinfty : ∞ ∉ K) :
    IsCompact (planarPart K) ∧ IsConnected (planarPart K) := by
  have heq := image_planarPart hinfty
  have hcomp : IsCompact (planarPart K) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.isCompact_iff.mpr (heq.symm ▸ hcompact)
  have hpre : IsPreconnected (planarPart K) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
      (heq.symm ▸ hconn.isPreconnected)
  have hne : (planarPart K).Nonempty := by
    obtain ⟨p, hp⟩ := hconn.nonempty
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hinfty (h ▸ hp))
    exact ⟨z, hp⟩
  exact ⟨hcomp, hne, hpre⟩

/-- A genuine complementary component is compact and connected. -/
theorem IsComplementaryComponent.isCompact_isConnected {G K : Set Sphere}
    (hK : IsComplementaryComponent G K) (hG : IsOpen G) :
    IsCompact K ∧ IsConnected K := by
  obtain ⟨p, hp, rfl⟩ := hK
  have hclosed : IsClosed (connectedComponentIn Gᶜ p) := by
    rw [connectedComponentIn_eq_image hp]
    exact hG.isClosed_compl.isClosedMap_subtype_val _ isClosed_connectedComponent
  exact ⟨hclosed.isCompact, isConnected_connectedComponentIn_iff.mpr hp⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactPairCutoff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact cutoff of the two continued model coordinates is globally
Sobolev. Its actual gradient is the product/chain-rule field on the
working disk and vanishes outside that disk. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_pair_cutoff_witness
    {U : Set EuclideanPlane} (hU : IsOpen U) (hUf : volume U ≠ ∞)
    {p q : EuclideanPlane → ℝ} (hp : Continuous p) (hq : Continuous q)
    (Wp : DeGiorgi.MemW1pWitness 2 p univ) (Wq : DeGiorgi.MemW1pWitness 2 q univ)
    {Φ θ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hsθ : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ U) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => θ x*Φ (planePair (p x) (q x))) univ,
      (∀ i : Fin 2, ∀ᵐ x ∂volume.restrict U,
        W.weakGrad x i = θ x*(
          fderiv ℝ Φ (planePair (p x) (q x)) (EuclideanSpace.single (0 : Fin 2) 1)*Wp.weakGrad x i+
          fderiv ℝ Φ (planePair (p x) (q x)) (EuclideanSpace.single (1 : Fin 2) 1)*Wq.weakGrad x i)+
          fderiv ℝ θ x (EuclideanSpace.single i 1)*Φ (planePair (p x) (q x))) ∧
      (∀ i : Fin 2, ∀ᵐ x ∂volume, x ∉ U → W.weakGrad x i = 0) := by
  let P := fun x => Φ (planePair (p x) (q x))
  let A := localPairChainWitness hU hUf hp hq (Wp.restrict hU (subset_univ U))
    (Wq.restrict hU (subset_univ U)) hΦ hB hC hΦb hΦd
  obtain ⟨C₀,hC₀⟩ := hθ.continuous.bounded_above_of_compact_support hsθ
  obtain ⟨C₁,hC₁⟩ := (hθ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hsθ.fderiv ℝ)
  let J := A.mul_smooth_bounded_p (by norm_num) hU hθ
    (le_max_right C₀ 0) (le_max_right C₁ 0)
    (fun x => by simpa only [Real.norm_eq_abs] using (hC₀ x).trans (le_max_left C₀ 0))
    (fun x => (hC₁ x).trans (le_max_left C₁ 0))
  obtain ⟨W⟩ := exists_global_compact_cutoff_witness hU A.memW1p hθ hsθ hθU
  have hW := (W.restrict hU (subset_univ U)).ae_eq hU J
  refine ⟨W,?_,?_⟩
  · intro i
    filter_upwards [hW] with x hx
    have hi := congrArg (fun v : EuclideanPlane => v i) hx
    simpa only [DeGiorgi.MemW1pWitness.restrict,J,DeGiorgi.MemW1pWitness.mul_smooth_bounded_p,
      A,localPairChainWitness,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] using hi
  · intro i
    filter_upwards [compact_weakGradient_zero_off W i] with x hx hxu
    apply hx
    exact fun ht => hxu (hθU (tsupport_mul_subset_left ht))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FixedDiskCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed source and target cutoffs are chosen before the near-extremal
model, so their derivative constants do not depend on that model. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem exists_complex_disk_cutoff {r R : ℝ} (hrR : r < R) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ball 0 R ∧ (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ closedBall 0 r, f z = 1) := by
  obtain ⟨f,hf,hs,hsub,hu,hf1⟩ := exists_smooth_planar_cutoff
    (isCompact_closedBall (0 : ℂ) r) isOpen_ball (closedBall_subset_ball hrR)
  exact ⟨f,hf,hs,hsub,hu,fun z hz => hf1.self_of_nhdsSet z hz⟩

 theorem exists_physical_disk_cutoff {r R : ℝ} (hrR : r < R) :
    ∃ (f : EuclideanPlane → ℝ) (C : ℝ), 0 ≤ C ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ ball 0 R ∧
      (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ closedBall 0 r, f x = 1) ∧
      (∀ x, ‖fderiv ℝ f x‖ ≤ C) := by
  obtain ⟨g,hg,hgs,hgsub,hgu,hg1⟩ := exists_complex_disk_cutoff hrR
  let f := g ∘ complexPlaneCoordinates
  have hf : ContDiff ℝ ∞ f := hg.comp complexPlaneCoordinates.contDiff
  have hs : HasCompactSupport f := hgs.comp_homeomorph complexPlaneCoordinates.toHomeomorph
  obtain ⟨C,hC⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  refine ⟨f,max C 0,le_max_right _ _,hf,hs,?_,fun x => hgu _,?_,
    fun x => (hC x).trans (le_max_left _ _)⟩
  · rw [show f = g ∘ complexPlaneCoordinates.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro x hx
    have hz := hgsub hx
    change complexPlaneCoordinates x ∈ ball (0 : ℂ) R at hz
    simpa only [mem_ball, dist_zero_right, complexPlaneCoordinates_norm] using hz
  · intro x hx
    apply hg1
    simpa only [mem_closedBall, dist_zero_right, complexPlaneCoordinates_norm] using hx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ModelOuterCutoff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed target cutoff changes a source barrier only where the saved
outer collar already vanishes. The sharper exterior remainder gives a
nonempty transition annulus, independent of the finite test list. -/
open Set Function Filter Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exterior_decay_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G) :
    ∀ z : ℂ, 2*a ≤ ‖z‖ → ‖M.function z-z‖ ≤ 2*a^2/‖z‖ := by
  have hsub {z : ℂ} (hz : a < ‖z‖) : (z : Sphere) ∈ G := by
    apply hsource
    rintro ⟨w,hw,he⟩
    have hwz : w = z := OnePoint.coe_injective he
    subst w
    have := mem_ball_zero_iff.mp hw
    linarith
  have hf : DifferentiableOn ℂ M.function {z | a < ‖z‖} := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ (hsub hz))).differentiableWithinAt
  have hi : InjOn M.function {z | a < ‖z‖} := by
    intro z hz w hw he
    apply OnePoint.coe_injective
    apply M.conformal.bijOn.injOn (hsub hz) (hsub hw)
    simpa only [extendAtInfinity_coe] using congrArg ((↑) : ℂ → Sphere) he
  have hn : (fun z : ℂ => M.function z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
    simpa only [extendAtInfinity_coe,finiteCoord_coe] using M.normalized.2
  exact harea.scaled_exterior_decay ha hf hi hn

 theorem exterior_half_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {z : ℂ} (hz : 4*a ≤ ‖z‖) : ‖M.function z-z‖ ≤ a/2 := by
  have hn : 0 < ‖z‖ := by linarith
  apply (M.exterior_decay_bound harea ha hsource z (by linarith)).trans
  apply (div_le_iff₀ hn).mpr
  nlinarith

 theorem cutoff_preserves_inner_barrier (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    (θ : EuclideanPlane → ℝ)
    (hθone : ∀ x ∈ closedBall 0 (64*a), θ x = 1)
    (hθsupp : tsupport θ ⊆ ball 0 ((129/2:ℝ)*a))
    (v : ℂ → ℝ)
    (hv : ∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a → v z = 0) :
    (∀ z : ℂ, (z : Sphere) ∈ G → ‖z‖ < 65*a →
      θ (complexPlaneCoordinates.symm (M.function z))*v z = v z) ∧
    (∀ z : ℂ, (z : Sphere) ∈ G → 65*a ≤ ‖z‖ →
      θ (complexPlaneCoordinates.symm (M.function z))*v z = 0) := by
  have hn (z : ℂ) : ‖complexPlaneCoordinates.symm z‖ = ‖z‖ := by
    simpa only [complexPlaneCoordinates.apply_symm_apply] using
      (complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z)).symm
  have hθzero (z : ℂ) (hz : (129/2:ℝ)*a ≤ ‖M.function z‖) :
      θ (complexPlaneCoordinates.symm (M.function z)) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have ht := mem_ball_zero_iff.mp (hθsupp hx)
    rw [hn] at ht
    linarith
  constructor
  · intro z hz hzn
    by_cases hsmall : ‖z‖ ≤ 63*a
    · have hbound : ‖M.function z‖ ≤ 64*a := by
        by_cases h4 : ‖z‖ ≤ 4*a
        · have h := (M.uniform_omitted_and_image_bound harea hG ha hsource).2 z hz h4
          linarith
        · have h := M.exterior_half_bound harea ha hsource (le_of_not_ge h4)
          have ht := norm_le_norm_sub_add (M.function z) z
          linarith
      rw [hθone _ (by simpa only [mem_closedBall,dist_zero_right,hn] using hbound),one_mul]
    · rw [hv z hz (le_of_not_ge hsmall) hzn.le,mul_zero]
  · intro z hz hzn
    have h := M.exterior_half_bound harea ha hsource (by linarith)
    have ht := norm_le_norm_sub_add z (M.function z)
    rw [norm_sub_rev] at ht
    rw [hθzero z (by linarith),zero_mul]

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ModelPairBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact target barrier is built from two continued model
coordinates. Its gradient vanishes almost everywhere on every model hole. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem pairBarrier_continuous (M : CompactScalarModel G u)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (i j : Fin m) {Φ θ : EuclideanPlane → ℝ} (hΦ : Continuous Φ) (hθ : Continuous θ) :
    Continuous (M.pairBarrier i j Φ θ) :=
  hθ.mul (hΦ.comp (continuous_planePair (M.scalar_continuous hu hs i) (M.scalar_continuous hu hs j)))

 theorem pairBarrier_pullback (M : CompactScalarModel G u) (i j : Fin m)
    (Φ θ : EuclideanPlane → ℝ) {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G) :
    planeInverseTransport (extendAtInfinity M.function) (M.pairBarrier i j Φ θ) x =
      θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x)))*
        Φ (planePair (u i x) (u j x)) := by
  rw [planeInverseTransport_extendAtInfinity]
  simp only [planeSphere,extendAtInfinity_coe,sphereFromPlaneFunction_coe]
  dsimp only [pairBarrier]
  have he : planeSphere (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) =
      extendAtInfinity M.function (planeSphere x) := by
    simp only [planeSphere,extendAtInfinity_coe,complexPlaneCoordinates.apply_symm_apply]
  rw [he,M.projection_inverse _ hx]
  simp only [planeSphere,sphereFromPlaneFunction_coe,complexPlaneCoordinates.symm_apply_apply]

 theorem pairBarrier_witness (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (i j : Fin m) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {Φ θ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsΦ : HasCompactSupport Φ)
    (hΦunit : ∀ x, Φ x ∈ Icc (0 : ℝ) 1)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hsθ : HasCompactSupport θ)
    (hθone : ∀ x ∈ closedBall 0 (64*a), θ x = 1)
    (hθsupp : tsupport θ ⊆ ball 0 ((129/2:ℝ)*a)) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (M.pairBarrier i j Φ θ) univ,
      ∀ k : Fin 2, ∀ᵐ x ∂volume,
        x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) → W.weakGrad x k = 0 := by
  let U : Set EuclideanPlane := ball 0 (66*a)
  have hU : IsOpen U := isOpen_ball
  have hθU : tsupport θ ⊆ U := hθsupp.trans (ball_subset_ball (by linarith))
  obtain ⟨C,hC⟩ := (hsΦ.fderiv ℝ).exists_bound_of_continuous (hΦ.continuous_fderiv (by simp))
  obtain ⟨W,hW,hWzero⟩ := compact_pair_cutoff_witness hU measure_ball_lt_top.ne
    (M.scalar_continuous hu hs i) (M.scalar_continuous hu hs j) (M.witness i) (M.witness j)
    (hΦ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (by norm_num : (0 : ℝ) ≤ 1) (le_max_right C 0)
    (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hΦunit x).1]; exact (hΦunit x).2)
    (fun x => (hC x).trans (le_max_left C 0)) hθ hsθ hθU
  have hθderiv (x : EuclideanPlane)
      (hx : x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G)) : fderiv ℝ θ x = 0 := by
    have hb := (M.uniform_omitted_and_image_bound harea hG ha hsource).1 (complexPlaneCoordinates x) hx
    have hxb : x ∈ ball 0 (64*a) := by
      rw [mem_ball_zero_iff]
      rw [complexPlaneCoordinates_norm] at hb
      linarith
    have heq : θ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
      exact hθone y (ball_subset_closedBall hy)
    rw [heq.fderiv_eq]
    simp
  refine ⟨W,?_⟩
  intro k
  have hWk := (ae_restrict_iff' hU.measurableSet).mp (hW k)
  filter_upwards [hWk,hWzero k,M.gradient_zero i k,M.gradient_zero j k] with x hx hz hpi hqi hxc
  by_cases hxU : x ∈ U
  · rw [hx hxU,hpi hxc,hqi hxc,hθderiv x hxc]
    simp
  · exact hz hxU

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RecursiveTestBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite positive tolerances give an explicit summable error budget.
Each later step respects every earlier saved tolerance. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem savedToleranceMinimum_le {ε t : ℝ} {ts : List ℝ} (ht : t ∈ ts) :
    savedToleranceMinimum ε ts ≤ t := by
  induction ts with
  | nil => simp at ht
  | cons s ts ih =>
    rcases List.mem_cons.mp ht with rfl | ht
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih ht)

 theorem savedToleranceMinimum_le_initial (ε : ℝ) (ts : List ℝ) :
    savedToleranceMinimum ε ts ≤ min 1 ε := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih => exact (min_le_right _ _).trans ih

 theorem recursiveTestBudget_le_saved {ε t : ℝ} (n : ℕ) {ts : List ℝ} (ht : t ∈ ts) :
    recursiveTestBudget ε n ts ≤ (1/2 : ℝ)^(n+3)*t :=
  mul_le_mul_of_nonneg_left (savedToleranceMinimum_le ht) (by positivity)

 theorem recursiveTestBudget_le_initial (ε : ℝ) (n : ℕ) (ts : List ℝ) :
    recursiveTestBudget ε n ts ≤ (1/2 : ℝ)^(n+3)*ε := by
  exact mul_le_mul_of_nonneg_left
    ((savedToleranceMinimum_le_initial ε ts).trans (min_le_right _ _)) (by positivity)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SummableRecursiveBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The recursive choices have a summable majorant with an explicit total
and explicit tails, for uniform and gradient convergence. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem summable_geometric_test_budget (ε : ℝ) :
    Summable (fun n : ℕ => (1/2 : ℝ)^(n+3)*ε) := by
  simpa only [pow_add,mul_assoc] using
    summable_geometric_two.mul_right ((1/2 : ℝ)^3*ε)

 theorem tsum_geometric_test_budget (ε : ℝ) :
    (∑' n : ℕ, (1/2 : ℝ)^(n+3)*ε) = ε/4 := by
  simp_rw [pow_add,mul_assoc]
  rw [tsum_mul_right,tsum_geometric_two]
  ring

 theorem summable_recursive_test_budget {ε : ℝ} (hε : 0 < ε)
    (ts : ℕ → List ℝ) (hts : ∀ n t, t ∈ ts n → 0 < t) :
    Summable (fun n => recursiveTestBudget ε n (ts n)) :=
  Summable.of_nonneg_of_le (fun n => (recursiveTestBudget_pos hε n (hts n)).le)
    (fun n => recursiveTestBudget_le_initial ε n (ts n)) (summable_geometric_test_budget ε)

 theorem tsum_recursive_test_budget_le {ε : ℝ} (hε : 0 < ε)
    (ts : ℕ → List ℝ) (hts : ∀ n t, t ∈ ts n → 0 < t) :
    (∑' n, recursiveTestBudget ε n (ts n)) ≤ ε/4 := by
  rw [← tsum_geometric_test_budget]
  exact (summable_recursive_test_budget hε ts hts).tsum_le_tsum
    (fun n => recursiveTestBudget_le_initial ε n (ts n)) (summable_geometric_test_budget ε)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TrackedTestSequence
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Follow each old scalar through every actual appending stage. The
coordinate indices shift by two, and both errors retain the chosen budget. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)

local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

local notation "idx" => index hsupply hsard hsch hG hinf hTD ha hBa hε T

local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => witness hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem step_uniform (i : Fin T.count) (n : ℕ) (x : EuclideanPlane) :
    |f i (n+1) x-f i n x| < recursiveTestBudget ε n (states n).tolerances := by
  exact ((states n).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n).data.old_close (idx i n) x

 theorem step_gradient (i : Fin T.count) (n : ℕ) :
    (eLpNorm (fun x => (W i (n+1)).weakGrad x-(W i n).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G))).toReal < recursiveTestBudget ε n (states n).tolerances := by
  exact ((states n).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n).data.old_error (idx i n)

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveTestHistory
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every saved tolerance stays in the actual finite history. Thus each
later test change is bounded by its geometric share of that tolerance. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

local notation "τ" => savedTolerance hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem savedTolerance_pos (n : ℕ) : 0 < τ n :=
  ((states n).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n).saved.tolerance_pos

 theorem history_mono {n k : ℕ} (hnk : n ≤ k) {t : ℝ}
    (ht : t ∈ (states n).tolerances) : t ∈ (states k).tolerances := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hnk
  induction r with
  | zero => exact ht
  | succ r ih =>
    change t ∈ _ :: (states (n+r)).tolerances
    exact List.mem_cons_of_mem _ (ih (Nat.le_add_right _ _))

 theorem savedTolerance_mem (n : ℕ) : τ n ∈ (states (n+1)).tolerances :=
  List.mem_cons_self

 theorem later_budget_le_saved {n k : ℕ} (hnk : n+1 ≤ k) :
    recursiveTestBudget ε k (states k).tolerances ≤ (1/2 : ℝ)^(k+3)*τ n := by
  exact recursiveTestBudget_le_saved k
    (history_mono hsupply hsard hsch hG hinf hTD ha hBa hε T hnk
      (savedTolerance_mem hsupply hsard hsch hG hinf hTD ha hBa hε T n))

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RecursiveTailBudget
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite tail spends less than one quarter of a previously saved
tolerance. This controls both coordinates of each saved barrier. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "τ" => savedTolerance hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem tail_budget_le_saved {s k : ℕ} (hsk : s+1 ≤ k) (n : ℕ) :
    (∑ j ∈ Finset.range n, recursiveTestBudget ε (k+j) (states (k+j)).tolerances) ≤ τ s/4 := by
  have hτ := savedTolerance_pos hsupply hsard hsch hG hinf hTD ha hBa hε T s
  have hsum : (∑ j ∈ Finset.Ico k (k+n), recursiveTestBudget ε j (states j).tolerances) ≤ τ s/4 := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico k (k+n), (1/2 : ℝ)^(j+3)*τ s := by
        apply Finset.sum_le_sum
        intro j hj
        exact later_budget_le_saved hsupply hsard hsch hG hinf hTD ha hBa hε T
          (hsk.trans (Finset.mem_Ico.mp hj).1)
      _ ≤ ∑' j : ℕ, (1/2 : ℝ)^(j+3)*τ s :=
        (summable_geometric_test_budget (τ s)).sum_le_tsum _ (fun _ _ => by positivity)
      _ = τ s/4 := tsum_geometric_test_budget _
  simpa only [Finset.sum_Ico_eq_sum_range,Nat.add_sub_cancel_left] using hsum

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TrackedTailSequence
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Track a scalar from any saved stage, with cumulative uniform and
Sobolev-gradient errors controlled by the actual later budgets. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

local notation "idx" => tailIndex hsupply hsard hsch hG hinf hTD ha hBa hε T

local notation "f" => tailScalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => tailWitness hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem tail_step_uniform (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) (x : EuclideanPlane) :
    |f k i (n+1) x-f k i n x| < recursiveTestBudget ε (k+n) (states (k+n)).tolerances := by
  exact ((states (k+n)).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε (k+n)).data.old_close (idx k i n) x

 theorem tail_step_gradient (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) :
    (eLpNorm (fun x => (W k i (n+1)).weakGrad x-(W k i n).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G))).toReal <
      recursiveTestBudget ε (k+n) (states (k+n)).tolerances := by
  exact ((states (k+n)).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε (k+n)).data.old_error (idx k i n)

 theorem tail_uniform_error (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) (x : EuclideanPlane) :
    |f k i n x-f k i 0 x| ≤ ∑ j ∈ Finset.range n,
      recursiveTestBudget ε (k+j) (states (k+j)).tolerances := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := abs_sub_le (f k i (n+1) x) (f k i n x) (f k i 0 x)
    have hs := (tail_step_uniform hsupply hsard hsch hG hinf hTD ha hBa hε T k i n x).le
    rw [Finset.sum_range_succ]
    linarith

 theorem tail_gradient_error (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) :
    dist ((W k i n).weakGrad_memLp.toLp ((W k i n).weakGrad))
      ((W k i 0).weakGrad_memLp.toLp ((W k i 0).weakGrad)) ≤
      ∑ j ∈ Finset.range n, recursiveTestBudget ε (k+j) (states (k+j)).tolerances := by
  let F := fun n => (W k i n).weakGrad_memLp.toLp ((W k i n).weakGrad)
  have hs (j : ℕ) : dist (F j) (F (j+1)) ≤
      recursiveTestBudget ε (k+j) (states (k+j)).tolerances := by
    rw [dist_comm,Lp.dist_edist,Lp.edist_toLp_toLp]
    change (eLpNorm (fun x => (W k i (j+1)).weakGrad x-(W k i j).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G))).toReal ≤ _
    exact (tail_step_gradient hsupply hsard hsch hG hinf hTD ha hBa hε T k i j).le
  rw [dist_comm]
  exact dist_le_range_sum_of_dist_le n (fun {j} _ => hs j)

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TrackedTailGradient
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the tracked gradient's L2 metric estimate to its actual
weak-gradient difference, including restriction to a working disk. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => tailWitness hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem tail_gradient_norm_error (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) (L : ℝ) :
    (eLpNorm (fun x => (W k i n).weakGrad x-(W k i 0).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤
      ∑ j ∈ Finset.range n, recursiveTestBudget ε (k+j) (states (k+j)).tolerances := by
  have h := tail_gradient_error hsupply hsard hsch hG hinf hTD ha hBa hε T k i n
  rw [Lp.dist_edist,Lp.edist_toLp_toLp] at h
  change (eLpNorm (fun x => (W k i n).weakGrad x-(W k i 0).weakGrad x) 2
    (volume.restrict (physicalPlaneDomain G))).toReal ≤ _ at h
  have hm : MemLp (fun x => (W k i n).weakGrad x-(W k i 0).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G)) :=
    (W k i n).weakGrad_memLp.sub (W k i 0).weakGrad_memLp
  exact (ENNReal.toReal_mono hm.eLpNorm_ne_top (eLpNorm_mono_measure _
    (Measure.restrict_mono (inter_subset_left : physicalPlaneDomain G ∩ ball 0 L ⊆ physicalPlaneDomain G) le_rfl))).trans h

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PersistentSavedBarriers
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual recursive construction preserves every saved separating
barrier at every later finite stage. No infinite pair-nullity is needed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "f" => tailScalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => tailWitness hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem saved_barriers_persist (s n : ℕ) :
    let step := (states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s
    let ip : Fin (states (s+1)).family.count := (0 : Fin ((states s).family.count+1)).succ
    let iq : Fin (states (s+1)).family.count :=
      ⟨0,by change 0 < (states s).family.count+2; omega⟩
    step.saved.Holds (f (s+1) ip n) (f (s+1) iq n) := by
  let step := (states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s
  let ip : Fin (states (s+1)).family.count := (0 : Fin ((states s).family.count+1)).succ
  let iq : Fin (states (s+1)).family.count :=
      ⟨0,by change 0 < (states s).family.count+2; omega⟩
  let p := f (s+1) ip n
  let q := f (s+1) iq n
  let τ := step.saved.tolerance
  have hτ : 0 < τ := step.saved.tolerance_pos
  have hb := tail_budget_le_saved hsupply hsard hsch hG hinf hTD ha hBa hε T
    (s := s) (k := s+1) le_rfl n
  have hpE (x : EuclideanPlane) : |p x-step.data.p x| ≤ τ/4 :=
    (tail_uniform_error hsupply hsard hsch hG hinf hTD ha hBa hε T (s+1) ip n x).trans hb
  have hqE (x : EuclideanPlane) : |q x-step.data.q x| ≤ τ/4 :=
    (tail_uniform_error hsupply hsard hsch hG hinf hTD ha hBa hε T (s+1) iq n x).trans hb
  have hopen := (isOpen_physicalPlaneDomain hG).inter (isOpen_ball (x := (0 : EuclideanPlane)) (ε := 65*a))
  let Wp := (W (s+1) ip n).restrict hopen inter_subset_left
  let Wq := (W (s+1) iq n).restrict hopen inter_subset_left
  apply step.saved.stable p q
    ((states (s+1+n)).family.continuous _)
    ((states (s+1+n)).family.continuous _) Wp Wq
  · intro x
    have he : planePair (p x) (q x)-planePair (step.data.p x) (step.data.q x) =
        planePair (p x-step.data.p x) (q x-step.data.q x) := by
      ext i
      fin_cases i <;> simp
    rw [he]
    exact (planePair_norm_le _ _).trans (by linarith [hpE x,hqE x])
  · have hg := (tail_gradient_norm_error hsupply hsard hsch hG hinf hTD ha hBa hε T
      (s+1) ip n (65*a)).trans hb
    exact hg.trans (show τ/4 ≤ τ by linarith)
  · have hg := (tail_gradient_norm_error hsupply hsard hsch hG hinf hTD ha hBa hε T
      (s+1) iq n (65*a)).trans hb
    exact hg.trans (show τ/4 ≤ τ by linarith)

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_StrongWeakPartialLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded pointwise convergence and strong L2 convergence of actual
weak partial derivatives identify the derivative of the limit. Only the
compact support of the testing function is used for the value limit. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_of_bounded_pointwise_strong_limit
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (hu : ∀ n, ContinuousOn (u n) U)
    {C : ℝ} (hb : ∀ n x, x ∈ U → ‖u n x‖ ≤ C)
    (hp : ∀ x ∈ U, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {i : Fin 2} {g : ℕ → EuclideanPlane → ℝ}
    (hg : ∀ n, MemLp (g n) 2 (volume.restrict U))
    (hweak : ∀ n, DeGiorgi.HasWeakPartialDeriv i (g n) (u n) U)
    (G : Lp ℝ 2 (volume.restrict U))
    (hG : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 G)) :
    DeGiorgi.HasWeakPartialDeriv i G v U := by
  intro φ hφ hs hsub
  let ψ := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsψ : HasCompactSupport ψ := hs.fderiv_apply (𝕜 := ℝ) _
  have hleft : Tendsto (fun n => ∫ x in U, u n x*ψ x) atTop
      (𝓝 (∫ x in U, v x*ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun x => C*‖ψ x‖)
    · intro n
      exact ((hu n).aestronglyMeasurable hU.measurableSet).mul hψ.aestronglyMeasurable
    · exact ((hψ.integrable_of_hasCompactSupport hsψ).restrict (s := U)).norm.const_mul C
    · intro n
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb n x hx) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      exact (hp x hx).mul_const _
  have hφL : MemLp φ 2 (volume.restrict U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hs).restrict U
  have hpair (n : ℕ) : inner ℝ ((hg n).toLp (g n)) (hφL.toLp φ) =
      ∫ x in U, g n x*φ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hg n).coeFn_toLp,hφL.coeFn_toLp] with x hx hy
    simp only [Real.inner_apply,hx,hy]
  have hpairG : inner ℝ G (hφL.toLp φ) = ∫ x in U, G x*φ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφL.coeFn_toLp] with x hx
    simp only [Real.inner_apply,hx]
  have hright := hG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hφL.toLp φ))
  simp only [hpair,hpairG] at hright
  have he : (fun n => ∫ x in U, u n x*ψ x) =
      (fun n => -(∫ x in U, g n x*φ x)) := funext fun n => hweak n φ hφ hs hsub
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright.neg

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_StrongGradientEnergyLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong Cauchy control retains the full Dirichlet energy when taking
bounded pointwise limits, rather than only a lower semicontinuity bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem energy_limit_of_strong_cauchy_partials
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (hv : MemLp v 2 (volume.restrict U))
    (hu : ∀ n, ContinuousOn (u n) U)
    {C : ℝ} (hb : ∀ n x, x ∈ U → ‖u n x‖ ≤ C)
    (hp : ∀ x ∈ U, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    (g : Fin 2 → ℕ → EuclideanPlane → ℝ)
    (hg : ∀ i n, MemLp (g i n) 2 (volume.restrict U))
    (hw : ∀ i n, DeGiorgi.HasWeakPartialDeriv i (g i n) (u n) U)
    (hc : ∀ i, CauchySeq (fun n => (hg i n).toLp (g i n)))
    {B : ℝ} (he : Tendsto (fun n => ∫ x in U, g 0 n x^2+g 1 n x^2) atTop (𝓝 B)) :
    ∃ W : DeGiorgi.MemW1pWitness 2 v U,
      (∫ x in U, W.weakGrad x 0^2+W.weakGrad x 1^2) = B := by
  choose G hG using fun i => cauchySeq_tendsto_of_complete (hc i)
  let W : DeGiorgi.MemW1pWitness 2 v U := {
    memLp := hv
    weakGrad := fun x => WithLp.toLp 2 (fun i => G i x)
    weakGrad_component_memLp := fun i => Lp.memLp (G i)
    isWeakGrad := fun i => weakPartial_of_bounded_pointwise_strong_limit hU hu hb hp
      (hg i) (hw i) (G i) (hG i) }
  have ht (i : Fin 2) : Tendsto (fun n => ∫ x in U, g i n x^2) atTop
      (𝓝 (∫ x in U, G i x^2)) := by
    apply integral_sq_tendsto_of_L2 (hg i) (Lp.memLp (G i))
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (g i) (hg i) (G i) (Lp.memLp (G i))).mp
    simpa only [Lp.toLp_coeFn] using hG i
  have ht' := (ht 0).add (ht 1)
  simp only [← integral_add (hg 0 _).integrable_sq (hg 1 _).integrable_sq,
    ← integral_add (Lp.memLp (G 0)).integrable_sq (Lp.memLp (G 1)).integrable_sq] at ht'
  exact ⟨W, tendsto_nhds_unique ht' he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PairedEnergyCauchy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality of two-component Dirichlet energies of differences transfers
strong Cauchy control. This is the Hilbert-space step in conformal energy
transport for nonsmooth functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integral_sq_sub_eq_Lp_dist_sq
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, (f x-g x)^2 ∂μ) = dist (hf.toLp f) (hg.toLp g)^2 := by
  rw [Lp.dist_edist,Lp.edist_toLp_toLp]
  exact integral_sq_eq_eLpNorm_toReal_sq (hf.sub hg)

 theorem cauchy_partials_of_paired_energy_isometry
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (f : Fin 2 → ℕ → X → ℝ) (g : Fin 2 → ℕ → Y → ℝ)
    (hf : ∀ i n, MemLp (f i n) 2 μ) (hg : ∀ i n, MemLp (g i n) 2 ν)
    (hc : ∀ i, CauchySeq (fun n => (hf i n).toLp (f i n)))
    (he : ∀ m n,
      (∫ y, (g 0 m y-g 0 n y)^2+(g 1 m y-g 1 n y)^2 ∂ν) =
      ∫ x, (f 0 m x-f 0 n x)^2+(f 1 m x-f 1 n x)^2 ∂μ) :
    ∀ i, CauchySeq (fun n => (hg i n).toLp (g i n)) := by
  intro i
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N₀,hN₀⟩ := Metric.cauchySeq_iff.mp (hc 0) (ε/2) (half_pos hε)
  obtain ⟨N₁,hN₁⟩ := Metric.cauchySeq_iff.mp (hc 1) (ε/2) (half_pos hε)
  refine ⟨max N₀ N₁,?_⟩
  intro m hm n hn
  have h₀ := hN₀ m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn)
  have h₁ := hN₁ m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn)
  have h := he m n
  have hig (j : Fin 2) : Integrable (fun y => (g j m y-g j n y)^2) ν :=
    ((hg j m).sub (hg j n)).integrable_sq
  have hif (j : Fin 2) : Integrable (fun x => (f j m x-f j n x)^2) μ :=
    ((hf j m).sub (hf j n)).integrable_sq
  rw [integral_add (hig 0) (hig 1), integral_add (hif 0) (hif 1),
    integral_sq_sub_eq_Lp_dist_sq (hg 0 m) (hg 0 n),
    integral_sq_sub_eq_Lp_dist_sq (hg 1 m) (hg 1 n),
    integral_sq_sub_eq_Lp_dist_sq (hf 0 m) (hf 0 n),
    integral_sq_sub_eq_Lp_dist_sq (hf 1 m) (hf 1 n)] at h
  have hb₀ := dist_nonneg (x := (hf 0 m).toLp (f 0 m)) (y := (hf 0 n).toLp (f 0 n))
  have hb₁ := dist_nonneg (x := (hf 1 m).toLp (f 1 m)) (y := (hf 1 n).toLp (f 1 n))
  have ht₀ := dist_nonneg (x := (hg 0 m).toLp (g 0 m)) (y := (hg 0 n).toLp (g 0 n))
  have ht₁ := dist_nonneg (x := (hg 1 m).toLp (g 1 m)) (y := (hg 1 n).toLp (g 1 n))
  have hf₀ := (sq_lt_sq₀ hb₀ (half_pos hε).le).mpr h₀
  have hf₁ := (sq_lt_sq₀ hb₁ (half_pos hε).le).mpr h₁
  have hsmall : dist ((hf 0 m).toLp (f 0 m)) ((hf 0 n).toLp (f 0 n))^2+
      dist ((hf 1 m).toLp (f 1 m)) ((hf 1 n).toLp (f 1 n))^2 < ε^2 := by
    nlinarith only [hf₀,hf₁,sq_pos_of_pos hε]
  have hs := h.trans_lt hsmall
  fin_cases i
  · change dist ((hg 0 m).toLp (g 0 m)) ((hg 0 n).toLp (g 0 n)) < ε
    exact (sq_lt_sq₀ ht₀ hε.le).mp ((le_add_of_nonneg_right (sq_nonneg _)).trans_lt hs)
  · change dist ((hg 1 m).toLp (g 1 m)) ((hg 1 n).toLp (g 1 n)) < ε
    exact (sq_lt_sq₀ ht₁ hε.le).mp ((le_add_of_nonneg_left (sq_nonneg _)).trans_lt hs)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothTransportDifferenceEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conformal energy identity applied to differences of the actual
smooth transports, for the Cauchy argument below. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem smooth_transport_difference_energy
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u v : EuclideanPlane → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (physicalPlaneDomain U))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (physicalPlaneDomain U))
    (hgu : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain U)))
    (hgv : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain U))) :
    (∫ x in physicalPlaneDomain V,
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)-
        fderiv ℝ (planeInverseTransport fi v) x (EuclideanSpace.single 0 1))^2+
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)-
        fderiv ℝ (planeInverseTransport fi v) x (EuclideanSpace.single 1 1))^2) =
    ∫ x in physicalPlaneDomain U,
      (fderiv ℝ u x (EuclideanSpace.single 0 1)-fderiv ℝ v x (EuclideanSpace.single 0 1))^2+
      (fderiv ℝ u x (EuclideanSpace.single 1 1)-fderiv ℝ v x (EuclideanSpace.single 1 1))^2 := by
  have hPU := isOpen_physicalPlaneDomain hU
  have hPV := isOpen_physicalPlaneDomain hV
  have hdu (x) (hx : x ∈ physicalPlaneDomain U) : DifferentiableAt ℝ u x :=
    (hu.contDiffAt (hPU.mem_nhds hx)).differentiableAt (by norm_num)
  have hdv (x) (hx : x ∈ physicalPlaneDomain U) : DifferentiableAt ℝ v x :=
    (hv.contDiffAt (hPU.mem_nhds hx)).differentiableAt (by norm_num)
  have hgs (i : Fin 2) : MemLp (fun x => fderiv ℝ (fun x => u x-v x) x
      (EuclideanSpace.single i 1)) 2 (volume.restrict (physicalPlaneDomain U)) := by
    apply MemLp.ae_eq (hf_Lp := (hgu i).sub (hgv i))
    filter_upwards [ae_restrict_mem hPU.measurableSet] with x hx
    simp only [Pi.sub_apply,fderiv_fun_sub (hdu x hx) (hdv x hx),sub_apply]
  have hs := smooth_plane_energy_transport heq hU hV hinf hfix hf (hu.sub hv) hgs
  have htu := (smooth_plane_energy_transport heq hU hV hinf hfix hf hu hgu).1
  have htv := (smooth_plane_energy_transport heq hU hV hinf hfix hf hv hgv).1
  have hsub : planeInverseTransport fi (fun x => u x-v x) =
      (fun x => planeInverseTransport fi u x-planeInverseTransport fi v x) := rfl
  rw [hsub] at hs
  calc
    _ = ∫ x in physicalPlaneDomain V,
        (fderiv ℝ (fun x => planeInverseTransport fi u x-planeInverseTransport fi v x) x
          (EuclideanSpace.single 0 1))^2+
        (fderiv ℝ (fun x => planeInverseTransport fi u x-planeInverseTransport fi v x) x
          (EuclideanSpace.single 1 1))^2 := by
      apply setIntegral_congr_fun hPV.measurableSet
      intro x hx
      have h₀ := (htu.contDiffAt (hPV.mem_nhds hx)).differentiableAt (by norm_num)
      have h₁ := (htv.contDiffAt (hPV.mem_nhds hx)).differentiableAt (by norm_num)
      simp only [fderiv_fun_sub h₀ h₁,sub_apply]
    _ = _ := hs.2.2
    _ = _ := by
      apply setIntegral_congr_fun hPU.measurableSet
      intro x hx
      simp only [fderiv_fun_sub (hdu x hx) (hdv x hx),sub_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ConformalSobolevEnergyIdentity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Dirichlet energy transport for a continuous compactly supported
Sobolev function. Strong Cauchy control of transported mollifications
retains equality, strengthening the earlier one-sided bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem sobolev_conformal_energy_identity
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (H : DeGiorgi.MemW1pWitness 2 u univ)
    (hv : EqOn v (planeInverseTransport fi u) (physicalPlaneDomain V))
    (hL : MemLp v 2 (volume.restrict (physicalPlaneDomain V))) :
    ∃ K : DeGiorgi.MemW1pWitness 2 v (physicalPlaneDomain V),
      (∫ x in physicalPlaneDomain V, K.weakGrad x 0^2+K.weakGrad x 1^2) =
        ∫ x in physicalPlaneDomain U, H.weakGrad x 0^2+H.weakGrad x 1^2 := by
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using H.memLp
  let a := planarMollification u
  let b := fun n => planeInverseTransport fi (a n)
  have ha (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (a n) :=
    planarMollification_smooth (huL.locallyIntegrable (by norm_num)) n
  let d := fun (i : Fin 2) n x => fderiv ℝ (a n) x (EuclideanSpace.single i 1)
  let e := fun (i : Fin 2) n x => fderiv ℝ (b n) x (EuclideanSpace.single i 1)
  have hd (i : Fin 2) (n : ℕ) : MemLp (d i n) 2
      (volume.restrict (physicalPlaneDomain U)) :=
    (planarMollification_partial_memLp H hs n i).restrict _
  have ht (n : ℕ) := smooth_plane_energy_transport heq hU hV hinf hfix hf
    (ha n).contDiffOn (fun i => hd i n)
  have he (i : Fin 2) (n : ℕ) : MemLp (e i n) 2
      (volume.restrict (physicalPlaneDomain V)) := (ht n).2.1 i
  have hdc (i : Fin 2) : CauchySeq (fun n => (hd i n).toLp (d i n)) := by
    have hg : MemLp (fun x => H.weakGrad x i) 2 (volume.restrict (physicalPlaneDomain U)) := by
      simpa only [Measure.restrict_univ] using (H.weakGrad_component_memLp i).restrict (physicalPlaneDomain U)
    have hl : Tendsto (fun n => eLpNorm (fun x => d i n x-H.weakGrad x i) 2
        (volume.restrict (physicalPlaneDomain U))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (planarMollification_tendsto_gradient_L2 H i)
        (fun _ => bot_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
    exact ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (d i) (hd i)
      (fun x => H.weakGrad x i) hg).mpr hl).cauchySeq
  have hec := cauchy_partials_of_paired_energy_isometry d e hd he hdc (fun m n =>
    smooth_transport_difference_energy heq hU hV hinf hfix hf (ha m).contDiffOn
      (ha n).contDiffOn (fun i => hd i m) (fun i => hd i n))
  obtain ⟨C,hC⟩ := hu.bounded_above_of_compact_support hs
  have hunit (x : EuclideanPlane) : u x ∈ Icc (-C) C :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using hC x)
  have hb (n : ℕ) (x : EuclideanPlane) (_hx : x ∈ physicalPlaneDomain V) : ‖b n x‖ ≤ C := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (planarMollification_mem_Icc hu.aestronglyMeasurable hunit n _)
  have hp (x : EuclideanPlane) (hx : x ∈ physicalPlaneDomain V) :
      Tendsto (fun n => b n x) atTop (𝓝 (v x)) := by
    rw [hv hx]
    exact planarMollification_tendsto_of_continuous hu _
  apply energy_limit_of_strong_cauchy_partials (isOpen_physicalPlaneDomain hV) hL
    (fun n => (ht n).1.continuousOn) hb hp e he
    (fun i n => weakPartial_of_smooth_on (isOpen_physicalPlaneDomain hV) (ht n).1 i) hec
  convert planarMollification_energy_tendsto H hs (physicalPlaneDomain U) using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact (ht n).2.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalWeakGradientEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locality identifies the actual Sobolev gradient and its energy. A
zero exterior contributes no energy; the intervening circle is null. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakGradient_eq_on_subset
    {Ω V : Set EuclideanPlane} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {u v : EuclideanPlane → ℝ}
    (Hu : DeGiorgi.MemW1pWitness 2 u Ω) (Hv : DeGiorgi.MemW1pWitness 2 v V)
    (heq : EqOn u v V) :
    Hu.weakGrad =ᵐ[volume.restrict V] Hv.weakGrad := by
  let H := Hu.restrict hV hVΩ
  have hi (i : Fin 2) : (fun x => Hu.weakGrad x i) =ᵐ[volume.restrict V]
      fun x => Hv.weakGrad x i := by
    apply (weakPartial_congrOn hV (H.isWeakGrad i) heq).ae_eq hV (Hv.isWeakGrad i)
    · exact (H.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
    · exact (Hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
  filter_upwards [ae_all_iff.mpr hi] with x hx
  ext i
  exact hx i

 theorem weakGradient_zero_on_subset
    {Ω V : Set EuclideanPlane} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {u : EuclideanPlane → ℝ} (H : DeGiorgi.MemW1pWitness 2 u Ω)
    (hz : ∀ x ∈ V, u x = 0) : ∀ᵐ x ∂volume.restrict V, H.weakGrad x = 0 := by
  let H₀ := (H.restrict hV hVΩ).smul 0
  have heq : EqOn u (fun x => (0 : ℝ)*u x) V := by
    intro x hx
    change u x = 0*u x
    rw [hz x hx,zero_mul]
  have hg := weakGradient_eq_on_subset hV hVΩ H H₀ heq
  filter_upwards [hg] with x hx
  simpa only [H₀,DeGiorgi.MemW1pWitness.smul,zero_smul] using hx

 theorem localized_weakGradient_energy
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω) {R : ℝ}
    {u v : EuclideanPlane → ℝ} (Hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (Hv : DeGiorgi.MemW1pWitness 2 v (Ω ∩ ball 0 R))
    (heq : EqOn u v (Ω ∩ ball 0 R))
    (hz : ∀ x ∈ Ω, R < ‖x‖ → u x = 0) :
    (∫ x in Ω, ‖Hu.weakGrad x‖^2) = ∫ x in Ω ∩ ball 0 R, ‖Hv.weakGrad x‖^2 := by
  have hV := hΩ.inter (isOpen_ball (x := (0 : EuclideanPlane)) (ε := R))
  have hZ := hΩ.inter (isClosed_closedBall (x := (0 : EuclideanPlane)) (ε := R)).isOpen_compl
  have hgz := weakGradient_zero_on_subset hZ inter_subset_left Hu (fun x hx => hz x hx.1 (by
    simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hx.2))
  have hgz' := (ae_restrict_iff' hZ.measurableSet).mp hgz
  have hcircle : ∀ᵐ x : EuclideanPlane ∂volume, x ∉ sphere 0 R :=
    compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume 0 R)
  have hezero : ∀ᵐ x ∂volume.restrict Ω, x ∉ ball 0 R → ‖Hu.weakGrad x‖^2 = 0 := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet,ae_restrict_of_ae hgz',
      ae_restrict_of_ae hcircle] with x hx hg hc hb
    have hnorm : R < ‖x‖ := by
      have hn : R ≤ ‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hb
      have hne : ‖x‖ ≠ R := by simpa only [mem_sphere,dist_zero_right] using hc
      exact lt_of_le_of_ne hn hne.symm
    rw [hg ⟨hx,by simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hnorm⟩]
    simp
  have hrestrict : (volume.restrict Ω).restrict (ball 0 R) = volume.restrict (Ω ∩ ball 0 R) := by
    rw [Measure.restrict_restrict measurableSet_ball,inter_comm]
  calc
    _ = ∫ x in ball 0 R, ‖Hu.weakGrad x‖^2 ∂volume.restrict Ω :=
      (setIntegral_eq_integral_of_ae_compl_eq_zero hezero).symm
    _ = ∫ x in Ω ∩ ball 0 R, ‖Hu.weakGrad x‖^2 := by rw [hrestrict]
    _ = _ := integral_congr_ae ((weakGradient_eq_on_subset hV inter_subset_left Hu Hv heq).mono
      (fun _ hx => congrArg (fun z : EuclideanPlane => ‖z‖^2) hx))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelPairBarrierEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact target barrier has exactly the saved local source
energy. Its gradient on the model holes and on the exterior both vanish. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem pairBarrier_energy (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (i j : Fin m) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {Φ θ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsΦ : HasCompactSupport Φ)
    (hΦunit : ∀ x, Φ x ∈ Icc (0 : ℝ) 1)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hsθ : HasCompactSupport θ)
    (hθone : ∀ x ∈ closedBall 0 (64*a), θ x = 1)
    (hθsupp : tsupport θ ⊆ ball 0 ((129/2:ℝ)*a))
    (H : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (u i x) (u j x)))
      (physicalPlaneDomain G ∩ ball 0 (65*a)))
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
      Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z))) = 0) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (M.pairBarrier i j Φ θ) univ,
      (∀ k : Fin 2, ∀ᵐ x ∂volume,
        x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) → W.weakGrad x k = 0) ∧
      (∫ x, ‖W.weakGrad x‖^2) =
        ∫ x in physicalPlaneDomain G ∩ ball 0 (65*a), ‖H.weakGrad x‖^2 := by
  obtain ⟨W,hWzero⟩ := M.pairBarrier_witness harea hG hu hs i j ha hsource
    hΦ hsΦ hΦunit hθ hsθ hθone hθsupp
  have hB := M.pairBarrier_continuous hu hs i j hΦ.continuous hθ.continuous
  have hsB : HasCompactSupport (M.pairBarrier i j Φ θ) := hsθ.mul_right
  obtain ⟨hfc,hmap,fi,hfic,hfimap,hl,hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.image_open hp,hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp,hmap,hr,hl⟩
  have hfix : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  let v := planeInverseTransport (extendAtInfinity M.function) (M.pairBarrier i j Φ θ)
  obtain ⟨K,hK⟩ := sobolev_conformal_energy_identity heq M.image_open hG
    ⟨_,hinf,rfl⟩ hfix hfic hB hsB W (v := v) (fun _ _ => rfl)
    (M.compact_target_pullback_memLp hG hinf hB hsB)
  have hnormK : (∫ x in physicalPlaneDomain G, ‖K.weakGrad x‖^2) =
      ∫ x in physicalPlaneDomain (extendAtInfinity M.function '' G), ‖W.weakGrad x‖^2 := by
    simpa only [plane_norm_sq] using hK
  have hv := M.cutoff_preserves_inner_barrier harea hG ha hsource θ hθone hθsupp
    (fun z => Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z)))) hzero
  have hlocal : (∫ x in physicalPlaneDomain G, ‖K.weakGrad x‖^2) =
      ∫ x in physicalPlaneDomain G ∩ ball 0 (65*a), ‖H.weakGrad x‖^2 := by
    apply localized_weakGradient_energy (isOpen_physicalPlaneDomain hG) K H
    · intro x hx
      change planeInverseTransport _ _ x = _
      rw [M.pairBarrier_pullback i j Φ θ hx.1]
      have hh := hv.1 (complexPlaneCoordinates x) hx.1
        (by simpa only [mem_ball,dist_zero_right,complexPlaneCoordinates_norm] using hx.2)
      simpa only [complexPlaneCoordinates.symm_apply_apply] using hh
    · intro x hx hxn
      change planeInverseTransport _ _ x = 0
      rw [M.pairBarrier_pullback i j Φ θ hx]
      have hh := hv.2 (complexPlaneCoordinates x) hx
        (by simpa only [complexPlaneCoordinates_norm] using hxn.le)
      simpa only [complexPlaneCoordinates.symm_apply_apply] using hh
  have hzE : ∀ᵐ x ∂volume,
      x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) → ‖W.weakGrad x‖^2 = 0 := by
    filter_upwards [hWzero 0,hWzero 1] with x h₀ h₁ hx
    rw [plane_norm_sq,h₀ hx,h₁ hx]
    norm_num
  refine ⟨W,hWzero,?_⟩
  exact (setIntegral_eq_integral_of_ae_compl_eq_zero hzE).symm.trans (hnormK.symm.trans hlocal)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SmallModelBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A saved source barrier produces an actual compact global target
barrier, with the same small energy and value one on its image contour. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_small_pair_barrier (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (i j : Fin m) {a η : ℝ} (ha : 0 < a) (hη : 0 < η)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsΦ : HasCompactSupport Φ)
    (hΦunit : ∀ x, Φ x ∈ Icc (0 : ℝ) 1)
    (H : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (u i x) (u j x)))
      (physicalPlaneDomain G ∩ ball 0 (65*a)))
    (hH : (eLpNorm H.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
      Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z))) = 0)
    {C : Set ℂ} (hCG : ∀ z ∈ C, (z : Sphere) ∈ G) (hCr : C ⊆ ball 0 (65*a))
    (hCone : ∀ z ∈ C,
      Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z))) = 1) :
    ∃ (v : EuclideanPlane → ℝ) (W : DeGiorgi.MemW1pWitness 2 v univ),
      Continuous v ∧ tsupport v ⊆ ball 0 (65*a) ∧
      (∀ x, v x ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ C, v (complexPlaneCoordinates.symm (M.function z)) = 1) ∧
      (∫ x, ‖W.weakGrad x‖^2) < η^2 := by
  obtain ⟨θ,D,_hD,hθ,hsθ,hθsupp,hθunit,hθone,_hθD⟩ := exists_physical_disk_cutoff
    (show 64*a < (129/2:ℝ)*a by linarith)
  obtain ⟨W,_hWzero,hWE⟩ := M.pairBarrier_energy harea hG hinf hu hs i j ha hsource
    hΦ hsΦ hΦunit hθ hsθ hθone hθsupp H hzero
  refine ⟨M.pairBarrier i j Φ θ,W,M.pairBarrier_continuous hu hs i j hΦ.continuous hθ.continuous,
    ?_,?_,?_,?_⟩
  · exact tsupport_mul_subset_left.trans (hθsupp.trans (ball_subset_ball (by linarith)))
  · intro x
    exact ⟨mul_nonneg (hθunit x).1 (hΦunit _).1,
      (mul_le_mul (hθunit x).2 (hΦunit _).2 (hΦunit _).1 zero_le_one).trans_eq (one_mul 1)⟩
  · intro z hz
    have hv := (M.cutoff_preserves_inner_barrier harea hG ha hsource θ hθone hθsupp
      (fun z => Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z)))) hzero).1
      z (hCG z hz) (mem_ball_zero_iff.mp (hCr hz))
    rw [hCone z hz] at hv
    change θ (complexPlaneCoordinates.symm (M.function z))*Φ
      (planePair (sphereFromPlaneFunction (u i) (M.projection
        (planeSphere (complexPlaneCoordinates.symm (M.function z)))))
        (sphereFromPlaneFunction (u j) (M.projection
        (planeSphere (complexPlaneCoordinates.symm (M.function z)))))) = 1
    have hproj : M.projection (M.function z : Sphere) = (z : Sphere) := by
      simpa only [extendAtInfinity_coe] using M.projection_inverse (z : Sphere) (hCG z hz)
    simpa only [planeSphere,complexPlaneCoordinates.apply_symm_apply,hproj,
      sphereFromPlaneFunction_coe,hCone z hz] using hv
  · rw [hWE]
    have he : (∫ x in physicalPlaneDomain G ∩ ball 0 (65*a), ‖H.weakGrad x‖^2) =
        (eLpNorm H.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal^2 := by
      rw [integral_sq_eq_eLpNorm_toReal_sq H.weakGrad_norm_memLp,
        eLpNorm_norm _]
    rw [he]
    exact (sq_lt_sq₀ ENNReal.toReal_nonneg hη.le).mpr hH

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactScalarModelFromCircle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed circle model belongs to the coefficient-extremal class. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
 theorem CompactScalarCircleModel.exists_coefficient
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (M : CompactScalarCircleModel G u) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) :
    ∃ b : ℂ, HasPrincipalCoefficient M.function b := by
  have hm : ∀ᶠ z : ℂ in cobounded ℂ, (z : Sphere) ∈ G := by
    have ht : Tendsto (fun z : ℂ => (z : Sphere)) (cobounded ℂ) (𝓝 OnePoint.infty) := by
      simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
        (OnePoint.tendsto_coe_infty : Tendsto (fun z : ℂ => (z : Sphere)) _ _)
    exact ht.eventually (hG.mem_nhds hinf)
  apply exists_principal_coefficient
  · exact hm.mono fun z hz => finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)
  · simpa only [extendAtInfinity_coe, finiteCoord_coe] using M.normalized.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SavedModelBarriers
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every saved source contour has an actual compact global barrier on
every later finite circle model, with energy tending to zero in the
saved stage. All witnesses come from the recursive construction. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem saved_model_barrier (harea : ExteriorCoefficientAreaTheorem) (s n : ℕ)
    (M : CompactScalarCircleModel G (states (s+1+n)).family.test) :
    let S := ((states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s).saved
    ∀ l : Fin S.count,
      ∃ (v : EuclideanPlane → ℝ) (W : DeGiorgi.MemW1pWitness 2 v univ),
        Continuous v ∧ tsupport v ⊆ ball 0 (65*a) ∧
        (∀ x, v x ∈ Icc (0 : ℝ) 1) ∧
        (∀ z ∈ range (S.curve l), v (complexPlaneCoordinates.symm (M.function z)) = 1) ∧
        (∫ x, ‖W.weakGrad x‖^2) < (1/((s:ℝ)+1))^2 := by
  dsimp only
  let step := (states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s
  let ip : Fin (states (s+1)).family.count := (0 : Fin ((states s).family.count+1)).succ
  let iq : Fin (states (s+1)).family.count :=
    ⟨0,by change 0 < (states s).family.count+2; omega⟩
  let i := tailIndex hsupply hsard hsch hG hinf hTD ha hBa hε T (s+1) ip n
  let j := tailIndex hsupply hsard hsch hG hinf hTD ha hBa hε T (s+1) iq n
  have hhold := saved_barriers_persist hsupply hsard hsch hG hinf hTD ha hBa hε T s n
  obtain ⟨b,hb⟩ := M.exists_coefficient hG hinf
  let A := M.toCompactScalarModel hinf (states (s+1+n)).family.compact b hb
  have hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G := by
    intro p hp
    by_contra hpG
    cases p using OnePoint.rec with
    | infty => exact hpG hinf
    | coe z => exact hp ⟨z,hBa hpG,rfl⟩
  intro l
  obtain ⟨H,hH⟩ := (hhold l).2.2
  have hcl (z : ℂ) (hz : z ∈ range (step.saved.curve l)) :
      z ∈ closure (jordanInterior (step.saved.jordan l)) := by
    apply frontier_subset_closure
    rwa [(step.saved.regular l).2.2.1]
  apply A.exists_small_pair_barrier harea hG hinf (states (s+1+n)).family.continuous
    (states (s+1+n)).family.compact i j ha (by positivity) hsource
    (step.saved.smooth l) (step.saved.compact l) (step.saved.unit l) H hH (hhold l).2.1
    (fun z hz => (step.saved.regular l).2.2.2 z hz)
  · intro z hz
    have h := step.saved.inside l (hcl z hz)
    rw [mem_ball_zero_iff] at h ⊢
    linarith
  · intro z hz
    exact (hhold l).1 z (step.saved.contains l (hcl z hz))

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RecursiveLimitBarriers
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal selection of actual finite-model barriers around a matched
limit end. The only small-energy data used are the saved recursive pairs. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem saved_model_barrier_of_le (harea : ExteriorCoefficientAreaTheorem) (s k : ℕ)
    (hk : s+1 ≤ k) (M : CompactScalarCircleModel G (states k).family.test) :
    let S := ((states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s).saved
    ∀ l : Fin S.count,
      ∃ (v : EuclideanPlane → ℝ) (W : DeGiorgi.MemW1pWitness 2 v univ),
        Continuous v ∧ tsupport v ⊆ ball 0 (65*a) ∧
        (∀ x, v x ∈ Icc (0 : ℝ) 1) ∧
        (∀ z ∈ range (S.curve l), v (complexPlaneCoordinates.symm (M.function z)) = 1) ∧
        (∫ x, ‖W.weakGrad x‖^2) < (1/((s:ℝ)+1))^2 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hk
  exact saved_model_barrier hsupply hsard hsch hG hinf hTD ha hBa hε T harea s r M

 theorem saved_barrier_around_matched_end
    (harea : ExteriorCoefficientAreaTheorem) (hconn : IsConnected G)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G})
    (Hn Jn : ℕ → ℂ ≃ₜ ℂ)
    (hnest : Antitone (fun n => closedTerminalCap (Hn n)))
    (hfrontG : ∀ n, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Hn n)) ⊆ G)
    (hboundary : ∀ n, extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (Hn n))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Jn n)))
    {q : Sphere} (hq : q ∈ Gᶜ) (hend : (⋂ n, closedTerminalCap (Hn n)) = {q})
    {K : Set ℂ} (hK : IsCompact K)
    (hKend : ((↑) : ℂ → Sphere) '' K ⊆ ⋂ n, closedTerminalCap (Jn n)) (s : ℕ) :
    Nonempty (CompactBarrierData (complexPlaneCoordinates.symm '' K) (65*a) (1/((s:ℝ)+1))) := by
  let S := ((states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s).saved
  obtain ⟨z,rfl⟩ := OnePoint.ne_infty_iff_exists.mp (show q ≠ OnePoint.infty from
    fun he => hq (he ▸ hinf))
  obtain ⟨l,hl⟩ := mem_iUnion.mp (S.cover hq)
  obtain ⟨J,Jm,w,hwG,hwJ,hγ,hfront,hfrontm,hγlim,hwlim,hwm,hside⟩ :=
    exists_anchored_curve_images hsch hG hconn.isPreconnected hinf
      (fun n => (M (σ n)).function) F (fun n => (M (σ n)).conformal) hF hlim
      (S.jordan l) (S.curve l) (S.regular l).2.1.continuous (S.regular l).2.1.injective
      (S.regular l).2.2.1.symm (fun t => (S.regular l).2.2.2 _ (mem_range_self t))
  have hKJ : K ⊆ jordanInterior J := by
    have ht := matched_end_subset_retained_side hF.bijOn.injOn (S.jordan l) J Hn Jn
      hnest hfrontG hboundary hside hend (mem_image_of_mem _ hl)
    intro x hx
    exact OnePoint.coe_injective.mem_set_image.mp (ht (hKend (mem_image_of_mem _ hx)))
  apply exists_compact_barrier_of_curve_images hK J Jm (F ∘ S.curve l)
    (fun n => (M (σ n)).function ∘ S.curve l) hγ hfront hfrontm hγlim hwJ hwlim hwm hKJ
  filter_upwards [hσ.tendsto_atTop.eventually_ge_atTop (s+1)] with n hn
  obtain ⟨v,W,hv,hs,_hu,hone,hE⟩ := saved_model_barrier_of_le
    hsupply hsard hsch hG hinf hTD ha hBa hε T harea s (σ n) hn (M (σ n)) l
  exact ⟨v,W,hv,hs,(fun t => hone _ (mem_range_self t)),hE⟩

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SummableTestLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable changes produce genuine continuous and L2 limits, with the
same explicit tail estimates used to preserve saved barriers. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem continuous_limit_of_summable_steps
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : ℕ → C(X,ℝ)) (d : ℕ → ℝ) (hd : Summable d) (hd0 : ∀ n, 0 ≤ d n)
    (hstep : ∀ n x, |f n x-f (n+1) x| ≤ d n) :
    ∃ g : C(X,ℝ), Tendsto f atTop (𝓝 g) ∧
      ∀ n x, |f n x-g x| ≤ ∑' j, d (n+j) := by
  have hdist : ∀ n, dist (f n) (f (n+1)) ≤ d n := fun n =>
    (ContinuousMap.dist_le (hd0 n)).mpr (fun x => by
      simpa only [Real.dist_eq] using hstep n x)
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable d hdist hd)
  refine ⟨g,hg,fun n x => ?_⟩
  have ht := dist_le_tsum_of_dist_le_of_tendsto d hdist hd hg n
  have hp := (ContinuousMap.dist_apply_le_dist x : dist (f n x) (g x) ≤ dist (f n) g)
  simpa only [Real.dist_eq] using hp.trans ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedConformalEnds
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem front_source (n : ℕ) (i : Fin (D.cores n).count) :
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((D.cores n).disk i)) ⊆ G :=
  (D.cores n).boundary_subset_domain i

 theorem projection_on_image (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    {x : Sphere} (hx : x ∈ G) : D.projection hG hf (f x) = x := by
  rw [projection,dite_eq_left (mem_image_of_mem f hx),hf.bijOn.injOn.leftInvOn_invFunOn hx]

 theorem projection_outside (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    {p : Sphere} (hp : p ∉ f '' G) : D.projection hG hf p ∈ Gᶜ := by
  rw [projection,dite_eq_right hp]
  exact (D.endAt hG hf p hp).outside

namespace EndAt
variable {D} {p : Sphere} (E : D.EndAt p)

 theorem target_nested (hf : IsConformalEquivalence f G (f '' G)) (n : ℕ) :
    closedTerminalCap (D.disks (n+1) (E.address (n+1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (D.disks n (E.address n)) :=
  (matched_jordan_disk_subset_iff hf.bijOn.injOn _ _ _ _
    (D.front_source _ _) (D.boundary _ _) (D.side _ _)).mp (E.source_nested n)

 theorem source_in_cap {p' : Sphere} (E' : D.EndAt p')
    (hp' : p' ∈ (f '' G)ᶜ) (n : ℕ)
    (hinside : p' ∈ ((↑) : ℂ → Sphere) '' jordanInterior (D.disks n (E.address n))) :
    E'.source ∈ closedTerminalCap ((D.cores n).disk (E.address n)) := by
  have hpCap := mem_iInter.mp (E'.target_eq ▸ mem_connectedComponentIn hp') n
  have he : E'.address n = E.address n := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (D.disks n) (D.disjoint n) hne)
      hpCap ((image_mono subset_closure) hinside)
  have hqCap := mem_iInter.mp (E'.source_eq ▸ mem_connectedComponentIn E'.outside) n
  rwa [he] at hqCap

 theorem projection_in_cap (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (n : ℕ) {y : Sphere}
    (hy : y ∈ ((↑) : ℂ → Sphere) '' jordanInterior (D.disks n (E.address n))) :
    D.projection hG hf y ∈ closedTerminalCap ((D.cores n).disk (E.address n)) := by
  by_cases hyG : y ∈ f '' G
  · have hh : y ∈ f '' (G ∩ (((↑) : ℂ → Sphere) ''
        jordanInterior ((D.cores n).disk (E.address n)))) := by
      rw [D.side]
      exact ⟨hyG,hy⟩
    obtain ⟨x,hx,rfl⟩ := hh
    rw [D.projection_on_image hG hf hx.1]
    exact (image_mono subset_closure) hx.2
  · rw [projection,dite_eq_right hyG]
    exact E.source_in_cap (D.endAt hG hf y hyG) hyG n hy

end EndAt

 theorem projection_continuous (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (hTD : IsTotallyDisconnected Gᶜ) :
    Continuous (D.projection hG hf) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ f '' G
  · obtain ⟨x,hx,rfl⟩ := hp
    have hi := continuousAt_conformal_invFunOn hf.1 hG hf.bijOn.injOn hx
    have hval : D.projection hG hf (f x) = invFunOn f G (f x) := by
      rw [projection,dite_eq_left (mem_image_of_mem f hx)]
    change Tendsto (D.projection hG hf) (𝓝 (f x)) (𝓝 (D.projection hG hf (f x)))
    rw [hval]
    apply hi.tendsto.congr'
    filter_upwards [(hf.1.isOpen_image hG hG Subset.rfl).mem_nhds (mem_image_of_mem f hx)] with y hy
    simp only [projection,dite_eq_left hy]
  · let E := D.endAt hG hf p hp
    have hval : D.projection hG hf p = E.source := by rw [projection,dite_eq_right hp]
    change Tendsto (D.projection hG hf) (𝓝 p) (𝓝 (D.projection hG hf p))
    rw [hval]
    apply tendsto_nhds.mpr
    intro V hV hpV
    have hsingle : connectedComponentIn Gᶜ E.source = {E.source} :=
      (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn E.outside)
    obtain ⟨n,hn⟩ := nested_sphere_sets_eventually_subset
      (fun n => (isCompact_closedTerminalCap ((D.cores n).disk (E.address n))).isClosed)
      (antitone_nat_of_succ_le (fun n => (E.source_nested n).trans (image_mono subset_closure)))
      hV (by rw [← E.source_eq,hsingle]; exact singleton_subset_iff.mpr hpV)
    have hpInside : p ∈ ((↑) : ℂ → Sphere) '' jordanInterior (D.disks n (E.address n)) :=
      E.target_nested hf n (mem_iInter.mp (E.target_eq ▸ mem_connectedComponentIn hp) (n+1))
    filter_upwards [(OnePoint.isOpen_image_coe.mpr
      (jordanInterior_isOpen (D.disks n (E.address n)))).mem_nhds hpInside] with y hy
    exact hn (E.projection_in_cap hG hf n hy)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedEndsHomeomorph
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton complementary components make the continuous inverse end
projection bijective, giving the actual sphere homeomorphism extension. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem projection_surjective (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (hTD : IsTotallyDisconnected Gᶜ) :
    Surjective (D.projection hG hf) := by
  have hP := D.projection_continuous hG hf hTD
  intro q
  by_cases hq : q ∈ G
  · exact ⟨f q,D.projection_on_image hG hf hq⟩
  · obtain ⟨b,p,hp,hsource,htarget,_⟩ := corresponding_target_end_of_source hG hf.1
      hf.bijOn.injOn D.cores D.disks D.strict D.cover D.disjoint D.complement D.boundary D.side hq
    have hcaps (n : ℕ) : D.projection hG hf p ∈ closedTerminalCap ((D.cores n).disk (b n)) := by
      apply inverse_projection_matched_cap hG hP
        (fun x hx => D.projection_on_image hG hf hx)
        (fun y hy => D.projection_outside hG hf hy)
        ((D.cores n).disk (b n)) (D.disks n (b n)) (D.front_source n (b n))
        (D.boundary n (b n)) (D.side n (b n))
      exact mem_image_of_mem _ (mem_iInter.mp (htarget ▸ mem_connectedComponentIn hp) n)
    have hmem : D.projection hG hf p ∈ connectedComponentIn Gᶜ q := by
      rw [hsource]
      exact mem_iInter.mpr hcaps
    have hsingle := (hTD _ (connectedComponentIn_subset Gᶜ q)
      isPreconnected_connectedComponentIn).eq_singleton_of_mem (mem_connectedComponentIn hq)
    exact ⟨p,by simpa only [hsingle,mem_singleton_iff] using hmem⟩

 theorem projection_injective (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hTD : IsTotallyDisconnected Gᶜ) (hT : IsTotallyDisconnected (f '' G)ᶜ) :
    Injective (D.projection hG hf) := by
  have hP := D.projection_continuous hG hf hTD
  intro x y hxy
  by_cases hx : x ∈ f '' G
  · obtain ⟨z,hz,rfl⟩ := hx
    have hyz : D.projection hG hf y = z := hxy.symm.trans (D.projection_on_image hG hf hz)
    exact ((inverse_projection_fiber_on_domain
      (fun z hz => D.projection_on_image hG hf hz)
      (fun p hp => D.projection_outside hG hf hp) hz).mp hyz).symm
  · have hfiber := inverse_projection_component_eq_fiber hG hTD hf.1 hf.bijOn.injOn hP
      (fun z hz => D.projection_on_image hG hf hz)
      (fun p hp => D.projection_outside hG hf hp)
      D.cores D.disks D.strict D.cover D.disjoint D.complement D.boundary D.side hx
    have hy : y ∈ connectedComponentIn (f '' G)ᶜ x := by
      rw [hfiber]
      exact hxy.symm
    exact hT _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hx) hy

 include D in
 theorem exists_homeomorph_extension (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hTD : IsTotallyDisconnected Gᶜ) (hT : IsTotallyDisconnected (f '' G)ᶜ) :
    ∃ H : Sphere ≃ₜ Sphere, ∀ x ∈ G, H x = f x := by
  let e : Sphere ≃ Sphere := Equiv.ofBijective (D.projection hG hf)
    ⟨D.projection_injective hG hf hTD hT,D.projection_surjective hG hf hTD⟩
  have hc : Continuous e := D.projection_continuous hG hf hTD
  let H := e.toHomeomorphOfContinuousClosed hc hc.isClosedMap
  refine ⟨H.symm,?_⟩
  intro x hx
  apply H.injective
  rw [H.apply_symm_apply]
  change x = D.projection hG hf (f x)
  exact (D.projection_on_image hG hf hx).symm

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
-- module Solutions.Q146_CD.CircleDomains_Uniformization_TrackedTestLimits
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual old coordinates have continuous sphere limits and strong
L2 gradient limits. Both stay within the total recursive error budget. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "d" => (fun n : ℕ => recursiveTestBudget ε n (AppendingConstructionState.tolerances (states n)))

 theorem exists_continuous_limit (i : Fin T.count) :
    ∃ g : C(Sphere,ℝ),
      Tendsto (sphereScalar hsupply hsard hsch hG hinf hTD ha hBa hε T i) atTop (𝓝 g) ∧
      ∀ z, |g z-sphereFromPlaneFunction (T.test i) z| ≤ ε/4 := by
  let F := sphereScalar hsupply hsard hsch hG hinf hTD ha hBa hε T i
  have hd := summable_recursive_test_budget hε (fun n => (states n).tolerances)
    (fun n => (states n).positive)
  have hd0 : ∀ n, 0 ≤ d n := fun n => (recursiveTestBudget_pos hε n (states n).positive).le
  have hstep : ∀ n z, |F n z-F (n+1) z| ≤ d n := by
    intro n z
    change |sphereFromPlaneFunction (f i n) z-sphereFromPlaneFunction (f i (n+1)) z| ≤ d n
    cases z using OnePoint.rec with
    | infty => simpa [sphereFromPlaneFunction] using hd0 n
    | coe z =>
      have hh := step_uniform hsupply hsard hsch hG hinf hTD ha hBa hε T i n
        (complexPlaneCoordinates.symm z)
      simpa only [sphereFromPlaneFunction_coe,abs_sub_comm] using hh.le
  obtain ⟨g,hg,hbound⟩ := continuous_limit_of_summable_steps F d hd hd0 hstep
  refine ⟨g,hg,?_⟩
  intro z
  have hb := (hbound 0 z).trans (by
    simpa only [zero_add] using tsum_recursive_test_budget_le hε
      (fun n => (states n).tolerances) (fun n => (states n).positive))
  change |sphereFromPlaneFunction (T.test i) z-g z| ≤ ε/4 at hb
  rwa [abs_sub_comm] at hb

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TrackedTestBounds
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scalar and Dirichlet bounds for the actual tracked old tests.
The bounds depend only on the original test and the total recursive budget. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => witness hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "d" => (fun n : ℕ => recursiveTestBudget ε n (AppendingConstructionState.tolerances (states n)))

 theorem finite_budget_le (n : ℕ) : ∑ j ∈ Finset.range n, d j ≤ ε/4 := by
  have hd := summable_recursive_test_budget hε (fun n => (states n).tolerances)
    (fun n => (states n).positive)
  exact (hd.sum_le_tsum (Finset.range n) (fun j _ =>
    (recursiveTestBudget_pos hε j (states j).positive).le)).trans
    (tsum_recursive_test_budget_le hε (fun n => (states n).tolerances)
      (fun n => (states n).positive))

 theorem scalar_initial_error (i : Fin T.count) (n : ℕ) (x : EuclideanPlane) :
    |f i n x-T.test i x| ≤ ε/4 := by
  have hstep (j : ℕ) : dist (f i j x) (f i (j+1) x) ≤ d j := by
    simpa only [Real.dist_eq,abs_sub_comm] using
      (step_uniform hsupply hsard hsch hG hinf hTD ha hBa hε T i j x).le
  have hh := dist_le_range_sum_of_dist_le n (fun {j} _ => hstep j)
  have hh' := hh.trans (finite_budget_le hsupply hsard hsch hG hinf hTD ha hBa hε T n)
  change |T.test i x-f i n x| ≤ ε/4 at hh'
  simpa only [abs_sub_comm] using hh'

 theorem gradient_norm_bound (i : Fin T.count) (n : ℕ) :
    ‖(W i n).weakGrad_memLp.toLp ((W i n).weakGrad)‖ ≤
      ‖(T.witness i).weakGrad_memLp.toLp ((T.witness i).weakGrad)‖+ε/4 := by
  let V := fun n => (W i n).weakGrad_memLp.toLp ((W i n).weakGrad)
  have hstep (j : ℕ) : dist (V j) (V (j+1)) ≤ d j := by
    rw [dist_comm,Lp.dist_edist,Lp.edist_toLp_toLp]
    exact (step_gradient hsupply hsard hsch hG hinf hTD ha hBa hε T i j).le
  have hh := (dist_le_range_sum_of_dist_le n (fun {j} _ => hstep j)).trans
    (finite_budget_le hsupply hsard hsch hG hinf hTD ha hBa hε T n)
  have hn := norm_le_norm_sub_add (V n) (V 0)
  rw [← dist_eq_norm,dist_comm] at hn
  change ‖V n‖ ≤ ‖V 0‖+ε/4
  linarith

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedEnergyWeakClosure
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost everywhere convergence of bounded continuous scalars and a
uniform global Dirichlet budget produce a global weak gradient. Compact
support is needed only for the test functions, not for a common support
of the approximating scalars. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_of_bounded_ae_pointwise_weak_limit
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (hu : ∀ n, Continuous (u n)) {C : ℝ}
    (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {i : Fin 2} {g : ℕ → EuclideanPlane → ℝ}
    (hw : ∀ n, DeGiorgi.HasWeakPartialDeriv i (g n) (u n) univ)
    (G : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (hG : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ x, g n x*w x) atTop (𝓝 (∫ x, G x*w x))) :
    DeGiorgi.HasWeakPartialDeriv i G v univ := by
  intro φ hφ hs _
  simp only [Measure.restrict_univ]
  let ψ := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsψ : HasCompactSupport ψ := hs.fderiv_apply (𝕜 := ℝ) _
  have hl : Tendsto (fun n => ∫ x, u n x*ψ x) atTop (𝓝 (∫ x, v x*ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun x => C*‖ψ x‖)
    · exact fun n => (hu n).aestronglyMeasurable.mul hψ.aestronglyMeasurable
    · exact (hψ.integrable_of_hasCompactSupport hsψ).norm.const_mul C
    · exact fun n => Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)
    · exact hp.mono (fun x hx => hx.mul_const _)
  have hr := tendsto_pairings_with_memLp_test hG (hφ.continuous.memLp_of_hasCompactSupport hs)
  have he : (fun n => ∫ x, u n x*ψ x) = (fun n => -(∫ x, g n x*φ x)) := by
    funext n
    simpa only [Measure.restrict_univ] using hw n φ hφ hs (subset_univ _)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr.neg

 theorem exists_bounded_energy_weak_gradient
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (W : ℕ → EuclideanPlane → EuclideanPlane)
    (hWL : ∀ n, MemLp (W n) 2 volume)
    (hW : ∀ n, DeGiorgi.HasWeakGrad (W n) (u n) univ)
    (hu : ∀ n, Continuous (u n)) {C : ℝ} (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {B : ℝ} (hB : ∀ n, (∫ x, ‖W n x‖^2) ≤ B) :
    ∃ g : EuclideanPlane → EuclideanPlane,
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g v univ ∧ (∫ x, ‖g x‖^2) ≤ B := by
  let u₀ := fun n x => W n x (0 : Fin 2)
  let u₁ := fun n x => W n x (1 : Fin 2)
  have hm₀ (n : ℕ) : MemLp (u₀ n) 2 volume := by
    exact memLp_piLp_iff.mp (hWL n) 0
  have hm₁ (n : ℕ) : MemLp (u₁ n) 2 volume := by
    exact memLp_piLp_iff.mp (hWL n) 1
  have he (n : ℕ) : (∫ x, u₀ n x^2+u₁ n x^2) ≤ B := by
    simpa only [plane_norm_sq] using hB n
  have hn (n : ℕ) : ‖(hm₀ n).toLp (u₀ n)‖ ≤ B+1 ∧ ‖(hm₁ n).toLp (u₁ n)‖ ≤ B+1 := by
    have h0 : ‖(hm₀ n).toLp (u₀ n)‖^2 = ∫ x, u₀ n x^2 := by
      rw [Lp.norm_toLp,integral_sq_eq_eLpNorm_toReal_sq (hm₀ n)]
    have h1 : ‖(hm₁ n).toLp (u₁ n)‖^2 = ∫ x, u₁ n x^2 := by
      rw [Lp.norm_toLp,integral_sq_eq_eLpNorm_toReal_sq (hm₁ n)]
    have hh := he n
    rw [integral_add (hm₀ n).integrable_sq (hm₁ n).integrable_sq,← h0,← h1] at hh
    constructor <;> nlinarith [sq_nonneg (‖(hm₀ n).toLp (u₀ n)‖-1),
      sq_nonneg (‖(hm₁ n).toLp (u₁ n)‖-1),sq_nonneg ‖(hm₀ n).toLp (u₀ n)‖,
      sq_nonneg ‖(hm₁ n).toLp (u₁ n)‖]
  obtain ⟨G₀,_,s,hs,h0⟩ := exists_L2_weak_subsequence volume u₀ hm₀ (B+1) (fun n => (hn n).1)
  obtain ⟨G₁,_,t,ht,h1⟩ := exists_L2_weak_subsequence volume (u₁ ∘ s)
    (fun n => hm₁ (s n)) (B+1) (fun n => (hn (s n)).2)
  let σ := s ∘ t
  have hσ : StrictMono σ := hs.comp ht
  have h0' (w : Lp ℝ 2 (volume : Measure EuclideanPlane)) := (h0 w).comp ht.tendsto_atTop
  let g : EuclideanPlane → EuclideanPlane := fun x => planePair (G₀ x) (G₁ x)
  refine ⟨g,?_,?_,?_⟩
  · apply memLp_piLp_iff.mpr
    intro i
    fin_cases i
    · change MemLp (fun x => planePair (G₀ x) (G₁ x) 0) 2 volume
      simpa only [planePair_zero] using Lp.memLp G₀
    · change MemLp (fun x => planePair (G₀ x) (G₁ x) 1) 2 volume
      simpa only [planePair_one] using Lp.memLp G₁
  · intro i
    fin_cases i
    · change DeGiorgi.HasWeakPartialDeriv 0 (fun x => planePair (G₀ x) (G₁ x) 0) v univ
      simpa only [planePair_zero] using weakPartial_of_bounded_ae_pointwise_weak_limit (fun n => hu (σ n))
        (fun n => hb (σ n)) (hp.mono (fun _ hx => hx.comp hσ.tendsto_atTop))
        (fun n => hW (σ n) 0) G₀ h0'
    · change DeGiorgi.HasWeakPartialDeriv 1 (fun x => planePair (G₀ x) (G₁ x) 1) v univ
      simpa only [planePair_one] using weakPartial_of_bounded_ae_pointwise_weak_limit (fun n => hu (σ n))
        (fun n => hb (σ n)) (hp.mono (fun _ hx => hx.comp hσ.tendsto_atTop))
        (fun n => hW (σ n) 1) G₁ h1
  · have hh := paired_L2_energy_le (fun n => hm₀ (σ n)) (fun n => hm₁ (σ n)) G₀ G₁
      (ε := fun _ => 0) tendsto_const_nhds
      (Eventually.of_forall (fun n => by simpa only [add_zero] using he (σ n)))
      (h0' G₀) (h1 G₁)
    simpa only [g,plane_norm_sq,planePair_zero,planePair_one] using hh

 theorem exists_bounded_energy_weak_closure
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (W : ∀ n, DeGiorgi.MemW1pWitness 2 (u n) univ)
    (hu : ∀ n, Continuous (u n)) {C : ℝ} (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {B : ℝ} (hB : ∀ n, (∫ x, ‖(W n).weakGrad x‖^2) ≤ B) :
    ∃ g : EuclideanPlane → EuclideanPlane,
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g v univ ∧ (∫ x, ‖g x‖^2) ≤ B := by
  exact exists_bounded_energy_weak_gradient (fun n => (W n).weakGrad)
    (fun n => by simpa only [Measure.restrict_univ] using (W n).weakGrad_memLp)
    (fun n => (W n).isWeakGrad) hu hb hp hB

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarModelExactEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The globally continued scalar has exactly its original source
Dirichlet energy. Apply conformal energy transport to the global target
scalar in the reverse direction and identify the source weak gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarCircleModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem scalar_energy_eq (M : CompactScalarCircleModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)) (i : Fin m) :
    (∫ x, ‖(M.witness i).weakGrad x‖^2) =
      ∫ x in physicalPlaneDomain G, ‖(W i).weakGrad x‖^2 := by
  let A := fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))
  have huc : Continuous (sphereFromPlaneFunction (u i)) := continuousOn_univ.mp
    (sphereFromPlaneFunction_continuousOn isOpen_univ (hu i).continuousOn
      (hs i).isCompact (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  have hA : Continuous A := (huc.comp M.projection_continuous).comp continuous_planeSphere
  have hsA : HasCompactSupport A := M.scalar_compact hinf hs i
  obtain ⟨hfc,hmap,fi,hfic,hfimap,hl,hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.circle.1 hp,hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp,hmap,hr,hl⟩
  have hfix : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  have hpull : EqOn (u i) (planeInverseTransport (extendAtInfinity M.function) A)
      (physicalPlaneDomain G) := by
    intro x hx
    rw [planeInverseTransport_extendAtInfinity]
    simp only [planeSphere,extendAtInfinity_coe,sphereFromPlaneFunction_coe]
    change u i x = sphereFromPlaneFunction (u i)
      (M.projection (planeSphere (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x)))))
    have he : planeSphere (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) =
        extendAtInfinity M.function (planeSphere x) := by
      simp only [planeSphere,complexPlaneCoordinates.apply_symm_apply,extendAtInfinity_coe]
    rw [he,M.projection_inverse _ hx]
    simp only [planeSphere,sphereFromPlaneFunction_coe,complexPlaneCoordinates.symm_apply_apply]
  obtain ⟨K,hK⟩ := sobolev_conformal_energy_identity heq M.circle.1 hG
    ⟨_,hinf,rfl⟩ hfix hfic hA hsA (M.witness i) hpull (W i).memLp
  have hsource : (∫ x in physicalPlaneDomain G, ‖K.weakGrad x‖^2) =
      ∫ x in physicalPlaneDomain G, ‖(W i).weakGrad x‖^2 := by
    apply integral_congr_ae
    exact (K.ae_eq (isOpen_physicalPlaneDomain hG) (W i)).mono
      (fun _ he => congrArg (fun v : EuclideanPlane => ‖v‖^2) he)
  have hzero : ∀ᵐ x ∂volume, x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) →
      ‖(M.witness i).weakGrad x‖^2 = 0 := by
    filter_upwards [M.gradient_zero i 0,M.gradient_zero i 1] with x h0 h1 hx
    rw [plane_norm_sq,h0 hx,h1 hx]
    norm_num
  calc
    _ = ∫ x in physicalPlaneDomain (extendAtInfinity M.function '' G),
        ‖(M.witness i).weakGrad x‖^2 := (setIntegral_eq_integral_of_ae_compl_eq_zero hzero).symm
    _ = ∫ x in physicalPlaneDomain G, ‖K.weakGrad x‖^2 := by
      simpa only [plane_norm_sq] using hK.symm
    _ = _ := hsource

end CompactScalarCircleModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_RecursiveLimitDust
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every complementary component of the actual recursive conformal limit
is a point. Matched ends and the saved finite-stage barriers supply all
geometric and energy data. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem recursive_limit_component_singleton
    (harea : ExteriorCoefficientAreaTheorem) (hconn : IsConnected G)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G})
    {p : Sphere} (hp : p ∈ (extendAtInfinity F '' G)ᶜ) :
    connectedComponentIn (extendAtInfinity F '' G)ᶜ p = {p} := by
  let f := extendAtInfinity F
  let E := connectedComponentIn (f '' G)ᶜ p
  have hV : IsOpen (f '' G) := hF.1.isOpen_image hG hG Subset.rfl
  have hEinfty : OnePoint.infty ∉ E := by
    intro h
    exact connectedComponentIn_subset _ _ h ⟨OnePoint.infty,hinf,rfl⟩
  have hEc : IsCompact E :=
    (IsComplementaryComponent.isCompact_isConnected ⟨p,hp,rfl⟩ hV).1
  have hEconn : IsConnected E := isConnected_connectedComponentIn_iff.mpr hp
  obtain ⟨hK,hKconn⟩ := planarPart_isCompact_isConnected hEc hEconn hEinfty
  let K := planarPart E
  have hphysc : IsCompact (complexPlaneCoordinates.symm '' K) :=
    hK.image complexPlaneCoordinates.symm.continuous
  have hphysconn : IsConnected (complexPlaneCoordinates.symm '' K) :=
    hKconn.image _ complexPlaneCoordinates.symm.continuous.continuousOn
  obtain ⟨C,J,hstrict,hcover,hd,he,hboundary,hside⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hconn hinf hF.1 hF.bijOn.injOn rfl
  obtain ⟨b,q,hq,hsource,htarget,hnest⟩ := corresponding_source_end_of_target hG
    hF.1 hF.bijOn.injOn C J hstrict hcover hd he hboundary hside hp
  have hsourcenest : Antitone (fun n => closedTerminalCap ((C n).disk (b n))) := by
    apply antitone_nat_of_succ_le
    intro n
    exact (hnest n).trans (image_mono subset_closure)
  have hfrontG (n : ℕ) : ((↑) : ℂ → Sphere) ''
      frontier (jordanInterior ((C n).disk (b n))) ⊆ G :=
    (C n).boundary_subset_domain (b n)
  have hqsingle : connectedComponentIn Gᶜ q = {q} :=
    (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
      (mem_connectedComponentIn hq)
  have hsource' : (⋂ n, closedTerminalCap ((C n).disk (b n))) = {q} :=
    hsource.symm.trans hqsingle
  have hKend : ((↑) : ℂ → Sphere) '' K ⊆ ⋂ n, closedTerminalCap (J n (b n)) := by
    rintro _ ⟨z,hz,rfl⟩
    exact htarget ▸ hz
  have hdata (s : ℕ) : Nonempty (CompactBarrierData (complexPlaneCoordinates.symm '' K)
      (65*a) (1/((s:ℝ)+1))) := saved_barrier_around_matched_end
    hsupply hsard hsch hG hinf hTD ha hBa hε T harea hconn M hσ hF hlim
    (fun n => (C n).disk (b n)) (fun n => J n (b n)) hsourcenest hfrontG
    (fun n => hboundary n (b n)) hq hsource' hK hKend s
  have hsub := compact_barrier_data_subsingleton hphysc hphysconn
    (show (0:ℝ) < 65*a by positivity) (fun s => Classical.choice (hdata s))
  have hKsub : K.Subsingleton := by
    intro z hz w hw
    apply complexPlaneCoordinates.symm.injective
    exact hsub (mem_image_of_mem _ hz) (mem_image_of_mem _ hw)
  have hEsub : E.Subsingleton := by
    intro z hz w hw
    obtain ⟨z',rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun he => hEinfty (he ▸ hz))
    obtain ⟨w',rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun he => hEinfty (he ▸ hw))
    exact congrArg ((↑) : ℂ → Sphere) (hKsub hz hw)
  exact hEsub.eq_singleton_of_mem (mem_connectedComponentIn hp)

 theorem recursive_limit_complement_totallyDisconnected
    (harea : ExteriorCoefficientAreaTheorem) (hconn : IsConnected G)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G}) :
    IsTotallyDisconnected (extendAtInfinity F '' G)ᶜ := by
  intro S hS hSc x hx y hy
  have hp := recursive_limit_component_singleton hsupply hsard hsch hG hinf hTD
    ha hBa hε T harea hconn M hσ hF hlim (hS hx)
  have hm := hSc.subset_connectedComponentIn hx hS hy
  exact (show y = x by simpa only [hp,mem_singleton_iff] using hm).symm

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_RecursiveLimitIdentity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized recursive limit is the identity when the source
complement is removable. Its sphere extension and orientation are proved
from matched ends; neither is a separate assumption. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem recursive_limit_eq_id
    (harea : ExteriorCoefficientAreaTheorem) (hconn : IsConnected G)
    (hrem : IsConformallyRemovable Gᶜ)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hnorm : IsPrincipalNormalized (extendAtInfinity F))
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G}) :
    ∀ z : ℂ, (z : Sphere) ∈ G → F z = z := by
  have htarget := recursive_limit_complement_totallyDisconnected
    hsupply hsard hsch hG hinf hTD ha hBa hε T harea hconn M hσ hF hlim
  obtain ⟨D⟩ := exists_matched_conformal_ends hsard hsch hG hconn hinf hF rfl
  obtain ⟨H,he⟩ := D.exists_homeomorph_extension hG hF hTD htarget
  have hid := removable_normalized_extension_eq_id hG hinf hrem hF.1 hnorm H he
  intro z hz
  have hh : extendAtInfinity F (z : Sphere) = (z : Sphere) := (he _ hz).symm.trans (hid _)
  exact OnePoint.coe_injective hh

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ScalarModelInverseConvergence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual continuous projections of finite scalar models converge
to the inverse on the limiting conformal image. This also transports
uniformly convergent source tests to their actual model continuations. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem CompactScalarCircleModel.projection_finite
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (M : CompactScalarCircleModel G u) (hinf : OnePoint.infty ∈ G) (z : ℂ) :
    M.projection (z : Sphere) ≠ OnePoint.infty := by
  intro h
  have he := (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hinf).mp h
  exact OnePoint.coe_ne_infty z (he.trans (extendAtInfinity_infty M.function))

 theorem scalar_model_projection_tendsto
    (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G)
    {m : ℕ → ℕ} {u : (n : ℕ) → Fin (m n) → EuclideanPlane → ℝ}
    (M : (n : ℕ) → CompactScalarCircleModel G (u n))
    {F : ℂ → ℂ} (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M n).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G})
    {z : ℂ} (hz : (z : Sphere) ∈ G) :
    Tendsto (fun n => (M n).projection (F z : Sphere)) atTop (𝓝 (z : Sphere)) := by
  have hV := hF.1.isOpen_image hG hG (Subset.refl G)
  obtain ⟨fi,hfi⟩ := hF.exists_smooth_inverse hG hV
  have hfp := hfi.finite_open_embedding hinf rfl hV
  choose gi hgi using fun n => (M n).conformal.exists_smooth_inverse hG (M n).circle.1
  have hmp (n : ℕ) := (hgi n).finite_open_embedding hinf (M n).normalized.1 (M n).circle.1
  have hi : Tendsto (fun n => finiteCoord ((M n).projection (F z : Sphere))) atTop (𝓝 z) := by
    apply inverse_tendsto_of_locally_uniform_open_embeddings hsch
      (hG.preimage OnePoint.continuous_coe)
      (by simpa only [extendAtInfinity_coe,finiteCoord_coe] using hfp.1)
      (by simpa only [extendAtInfinity_coe,finiteCoord_coe] using hfp.2.1)
      (by simpa only [extendAtInfinity_coe,finiteCoord_coe] using hfp.2.2)
      (fun _ => {z : ℂ | (z : Sphere) ∈ G})
      (fun _ => hG.preimage OnePoint.continuous_coe)
      (fun n => (M n).function) (fun n z => finiteCoord ((M n).projection (z : Sphere)))
      (fun n z hz => by
        convert (hmp n).1 z hz using 1
        · funext w; simp only [extendAtInfinity_coe,finiteCoord_coe]
        · rfl)
      (fun n S hS hSG => by
        simpa only [extendAtInfinity_coe,finiteCoord_coe] using (hmp n).2.1 S hS hSG)
      (fun n x hx y hy he => (hmp n).2.2 hx hy (by
        simpa only [extendAtInfinity_coe,finiteCoord_coe] using he))
      ?_ hlim (fun _ _ hKG => Eventually.of_forall (fun _ => hKG)) hz
    intro n x hx
    simpa only [extendAtInfinity_coe,finiteCoord_coe] using
      congrArg finiteCoord ((M n).projection_inverse (x : Sphere) hx)
  have ht := OnePoint.continuous_coe.continuousAt.tendsto.comp hi
  apply ht.congr'
  exact Eventually.of_forall (fun n => CannonMobius.coe_coordinate ((M n).projection_finite hinf (F z)))

 theorem scalar_model_continuations_tendsto
    (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G)
    {m : ℕ → ℕ} {u : (n : ℕ) → Fin (m n) → EuclideanPlane → ℝ}
    (M : (n : ℕ) → CompactScalarCircleModel G (u n))
    {F : ℂ → ℂ} (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M n).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G})
    {a : ℕ → C(Sphere,ℝ)} {b : C(Sphere,ℝ)} (hab : Tendsto a atTop (𝓝 b))
    {z : ℂ} (hz : (z : Sphere) ∈ G) :
    Tendsto (fun n => a n ((M n).projection (F z : Sphere))) atTop (𝓝 (b (z : Sphere))) := by
  have hp := scalar_model_projection_tendsto hsch hG hinf M hF hlim hz
  exact (continuous_eval.tendsto (b,(z : Sphere))).comp (hab.prodMk_nhds hp)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TrackedGlobalWeakLimit
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual continued tracked test converges off the removable dust,
and hence almost everywhere, to its continuous source limit. Its exact
model energy and the recursive budget give a global weak gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => witness hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "idx" => index hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "sf" => sphereScalar hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem exists_tracked_global_weak_limit_oai
    (hprincipal : PrincipalRealBeltrami) (harea : ExteriorCoefficientAreaTheorem)
    (hconn : IsConnected G) (hrem : IsConformallyRemovable Gᶜ)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hnorm : IsPrincipalNormalized (extendAtInfinity F))
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G}) (i : Fin T.count) :
    ∃ (v : C(Sphere,ℝ)) (g : EuclideanPlane → EuclideanPlane),
      (∀ p, |v p-sphereFromPlaneFunction (T.test i) p| ≤ ε/4) ∧
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g (fun x => v (planeSphere x)) univ ∧
      (∫ x, ‖g x‖^2) ≤
        (‖(T.witness i).weakGrad_memLp.toLp ((T.witness i).weakGrad)‖+ε/4)^2 := by
  obtain ⟨v,hv,hclose⟩ := exists_continuous_limit hsupply hsard hsch hG hinf hTD ha hBa hε T i
  have hid := recursive_limit_eq_id hsupply hsard hsch hG hinf hTD ha hBa hε T
    harea hconn hrem M hσ hnorm hF hlim
  let A := fun n x => sf i (σ n) ((M (σ n)).projection (planeSphere x))
  let V : ∀ n, DeGiorgi.MemW1pWitness 2 (A n) univ :=
    fun n => (M (σ n)).witness (idx i (σ n))
  have hAc (n : ℕ) : Continuous (A n) :=
    ((sf i (σ n)).continuous.comp (M (σ n)).projection_continuous).comp continuous_planeSphere
  obtain ⟨C,hC⟩ := (T.continuous i).bounded_above_of_compact_support (T.compact i)
  have hC0 : 0 ≤ C := (norm_nonneg (T.test i 0)).trans (hC 0)
  have hbound (n : ℕ) (p : Sphere) : ‖sf i n p‖ ≤ C+ε/4 := by
    cases p using OnePoint.rec with
    | infty =>
      simp only [sphereScalar,ContinuousMap.coe_mk,sphereFromPlaneFunction,ite_true, if_true,norm_zero]
      positivity
    | coe z =>
      simp only [sphereScalar,ContinuousMap.coe_mk,sphereFromPlaneFunction_coe,Real.norm_eq_abs]
      have he := scalar_initial_error hsupply hsard hsch hG hinf hTD ha hBa hε T i n
        (complexPlaneCoordinates.symm z)
      have ht := norm_le_norm_sub_add (f i n (complexPlaneCoordinates.symm z))
        (T.test i (complexPlaneCoordinates.symm z))
      simp only [Real.norm_eq_abs] at ht
      have hc := hC (complexPlaneCoordinates.symm z)
      rw [Real.norm_eq_abs] at hc
      linarith
  have hnull := removable_complement_volume_zero hprincipal hG hinf hrem
  have hp : ∀ᵐ x ∂volume, Tendsto (fun n => A n x) atTop (𝓝 (v (planeSphere x))) := by
    have hmem : physicalPlaneDomain G ∈ ae volume := by
      simpa only [compl_compl] using (compl_mem_ae_iff.mpr hnull)
    filter_upwards [hmem] with x hx
    have ht := scalar_model_continuations_tendsto hsch hG hinf (fun n => M (σ n)) hF hlim
      (hv.comp hσ.tendsto_atTop) (z := complexPlaneCoordinates x) hx
    rw [hid _ hx] at ht
    exact ht
  let B := ‖(T.witness i).weakGrad_memLp.toLp ((T.witness i).weakGrad)‖+ε/4
  have he (n : ℕ) : (∫ x, ‖(V n).weakGrad x‖^2) ≤ B^2 := by
    rw [(M (σ n)).scalar_energy_eq hG hinf (states (σ n)).family.continuous
      (states (σ n)).family.compact (states (σ n)).family.witness (idx i (σ n))]
    change (∫ x in physicalPlaneDomain G, ‖(W i (σ n)).weakGrad x‖^2) ≤ B^2
    have heq : (∫ x in physicalPlaneDomain G, ‖(W i (σ n)).weakGrad x‖^2) =
        ‖(W i (σ n)).weakGrad_memLp.toLp ((W i (σ n)).weakGrad)‖^2 := by
      rw [Lp.norm_toLp]
      simpa only [eLpNorm_norm _] using
        integral_sq_eq_eLpNorm_toReal_sq (W i (σ n)).weakGrad_memLp.norm
    rw [heq]
    have hb := gradient_norm_bound hsupply hsard hsch hG hinf hTD ha hBa hε T i (σ n)
    have hn := norm_nonneg ((W i (σ n)).weakGrad_memLp.toLp ((W i (σ n)).weakGrad))
    change _ ≤ B at hb
    nlinarith
  obtain ⟨g,hg,hweak,henergy⟩ := exists_bounded_energy_weak_closure V hAc
    (fun n x => hbound (σ n) ((M (σ n)).projection (planeSphere x))) hp he
  exact ⟨v,g,hclose,hg,hweak,henergy⟩

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.AppendingSequence.exists_tracked_global_weak_limit_oai := @OAI.CircleDomainRigidity.AppendingSequence.exists_tracked_global_weak_limit_oai
